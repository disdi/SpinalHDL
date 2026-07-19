package spinal.lib.cpu.riscv.debug

import spinal.core._
import spinal.lib._

/**
 * SWD transport for the RISC-V debug module (see fpga/SWD.md).
 *
 * This file will grow through the SWD.md phases:
 *   - Phase 2A (this step): SwdPhy — the ARM ADI SW-DP line layer (wire protocol
 *     state machine), terminating in the decoded-transaction seam below.
 *   - Phase 2B: DP register file (DPIDR, CTRL/STAT, SELECT, RDBUFF, ABORT) behind the seam.
 *   - Phase 2C: AP -> DebugBus bridge + clock crossing, then DebugModuleFiber.withSwdTransport().
 *
 * Seam note (2A <-> 2B): on the wire, the ACK of a *write* is sent BEFORE the 33-bit
 * WDATA phase, so write data cannot ride in the request. The seam is therefore three flows:
 *   - cmd  (2A -> 2B): decoded header, fired once the request passes parity/stop/park
 *   - rsp  (2B -> 2A): ACK (+ read data), must be presented within the turnaround cycle
 *   - wr   (2A -> 2B): write commit, fired after the WDATA phase with its parity verdict
 *
 * Scope/limits of this layer (per ADIv6.0, SWD protocol v1 point-to-point):
 *   - turnaround period fixed at 1 cycle (the power-on default; DLCR.TURNROUND is not supported)
 *   - no ORUNDETECT sticky-overrun mode: on WAIT/FAULT the data phase is always skipped
 *   - multi-drop (SWD v2) not supported
 *
 * Clocking: the component's implicit clock is SWCLK (probe-driven). The target samples
 * SWDIO on the rising edge and updates its own output on the rising edge, matching the
 * OpenOCD bitbang model (host sets data while SWCLK is low, samples target data while low).
 * SWDIO is exposed as i/o/oe — the tristate/IOBUF belongs at SoC/platform level (SWD.md 6.3).
 */

case class SwdDpCmd() extends Bundle {
  val apNdp = Bool()          // request APnDP bit
  val rnw   = Bool()          // request RnW bit
  val addr  = Bits(2 bits)    // A[3:2] (addr(0) = A[2])
}

case class SwdDpRsp() extends Bundle {
  val ack   = Bits(3 bits)    // OK=001, WAIT=010, FAULT=100 — sent LSB first
  val rdata = Bits(32 bits)   // used when cmd.rnw and ack == OK
}

case class SwdDpWrite() extends Bundle {
  val data     = Bits(32 bits)
  val parityOk = Bool()       // false => WDATAERR material for the DP (Phase 2B)
}

object SwdAck {
  def OK    = B"3'b001"
  def WAIT  = B"3'b010"
  def FAULT = B"3'b100"
}

case class SwdPhy() extends Component {
  val io = new Bundle {
    val swdio = new Bundle {
      val i  = in  Bool()
      val o  = out Bool()
      val oe = out Bool()
    }
    val dp = new Bundle {
      val cmd = master Flow(SwdDpCmd())
      val rsp = slave  Flow(SwdDpRsp())
      val wr  = master Flow(SwdDpWrite())
    }
  }

  val dio = io.swdio.i

  val oData  = Reg(Bool()) init(False)
  val oDrive = Reg(Bool()) init(False)
  io.swdio.o  := oData
  io.swdio.oe := oDrive

  // Response capture: rsp may be presented combinationally off cmd (same cycle the
  // turnaround starts) or held valid for one cycle; latch it for the rest of the frame.
  val rspHold = Reg(SwdDpRsp())
  when(io.dp.rsp.valid){ rspHold := io.dp.rsp.payload }
  val ackNow   = Mux(io.dp.rsp.valid, io.dp.rsp.payload.ack,   rspHold.ack)

  val cmdValid   = Reg(Bool()) init(False)
  val cmdPayload = Reg(SwdDpCmd())
  cmdValid := False
  io.dp.cmd.valid   := cmdValid
  io.dp.cmd.payload := cmdPayload

  val wrValid   = Reg(Bool()) init(False)
  val wrPayload = Reg(SwdDpWrite())
  wrValid := False
  io.dp.wr.valid   := wrValid
  io.dp.wr.payload := wrPayload

  // Line reset: 50+ SWCLK cycles with SWDIO high while the host owns the line
  // (ADIv6.0 B4.3.3). Recovers from any state, including protocol error.
  val lineReset = new Area {
    val counter = Reg(UInt(6 bits)) init(0)
    val hit = counter === 50
    when(oDrive || !dio) {
      counter := 0
    } elsewhen(!hit) {
      counter := counter + 1
    }
  }

  object EState extends SpinalEnum {
    val IDLE, HEADER, ACK, READ_DATA, WR_TRN, WRITE_DATA, RELEASE, ERROR, RESET_WAIT = newElement()
  }
  val state = Reg(EState()) init(EState.RESET_WAIT)
  val cnt   = Reg(UInt(6 bits)) init(0)
  val hdr   = Reg(Bits(6 bits))          // apNdp, rnw, a2, a3, parity, stop (LSB first)
  val wShift = Reg(Bits(32 bits))

  switch(state) {
    is(EState.IDLE) {
      oDrive := False
      when(dio) {                        // start bit
        state := EState.HEADER
        cnt := 0
      }
    }
    is(EState.HEADER) {
      hdr := dio ## hdr(5 downto 1)      // LSB-first shift-in
      cnt := cnt + 1
      when(cnt === 6) {                  // dio is the park bit; hdr holds apNdp..stop
        val apNdp = hdr(0)
        val rnw   = hdr(1)
        val a2    = hdr(2)
        val a3    = hdr(3)
        val parityOk = (apNdp ^ rnw ^ a2 ^ a3) === hdr(4)
        val stopOk   = !hdr(5)
        when(parityOk && stopOk && dio) {
          cmdValid := True
          cmdPayload.apNdp := apNdp
          cmdPayload.rnw   := rnw
          cmdPayload.addr  := a3 ## a2
          state := EState.ACK            // next cycle is the turnaround
          cnt := 0
        } otherwise {
          state := EState.ERROR          // silent until line reset (B4.2.5)
        }
      }
    }
    is(EState.ACK) {                     // drives ACK[0..2], first bit lands after the turnaround
      oDrive := True
      oData  := ackNow(cnt(1 downto 0))
      cnt := cnt + 1
      when(cnt === 2) {
        cnt := 0
        when(ackNow === SwdAck.OK) {
          when(cmdPayload.rnw) {
            state := EState.READ_DATA    // target keeps the line: RDATA follows ACK directly
          } otherwise {
            state := EState.WR_TRN       // turnaround back to host before WDATA
          }
        } otherwise {
          state := EState.RELEASE        // WAIT/FAULT: no data phase (no ORUNDETECT)
        }
      }
    }
    is(EState.READ_DATA) {               // 32 data bits LSB first + even parity
      oDrive := True
      oData  := Mux(cnt === 32, rspHold.rdata.xorR, rspHold.rdata(cnt(4 downto 0)))
      cnt := cnt + 1
      when(cnt === 32) {
        state := EState.RELEASE
      }
    }
    is(EState.WR_TRN) {                  // release the line, then one turnaround bit period
      oDrive := False                    // (a write has a 2nd turnaround after ACK; the host
      cnt := cnt + 1                     //  drives its first WDATA bit only after it)
      when(cnt === 1) {
        state := EState.WRITE_DATA
        cnt := 0
      }
    }
    is(EState.WRITE_DATA) {              // sample 32 data bits LSB first, then parity
      wShift := dio ## wShift(31 downto 1)
      cnt := cnt + 1
      when(cnt === 32) {                 // dio is the parity bit; wShift holds the data
        wrValid := True
        wrPayload.data     := wShift
        wrPayload.parityOk := wShift.xorR === dio
        state := EState.IDLE
      }
    }
    is(EState.RELEASE) {                 // turnaround back to host after a target-driven phase
      oDrive := False
      state := EState.IDLE
    }
    is(EState.ERROR) {                   // protocol error: line released, headers ignored
      oDrive := False
    }
    is(EState.RESET_WAIT) {              // line reset seen; leave once the host drives low
      oDrive := False
      when(!dio) {
        state := EState.IDLE
      }
    }
  }

  when(lineReset.hit) {                  // overrides everything, including ERROR
    state := EState.RESET_WAIT
  }
}

/**
 * Phase 2B seam toward the AP layer (Phase 2C consumes this; until then the testbench
 * stubs it). AP reads are posted per ADI: the DP answers an AP read from `rdBuffer` and
 * launches the new access; the result lands in `rdBuffer` on completion.
 */
case class SwdApCmd() extends Bundle {
  val rnw   = Bool()          // true = AP read, false = AP write
  val addr  = Bits(2 bits)    // AP register A[3:2]
  val apSel = Bits(8 bits)    // SELECT[31:24]; the Phase 2D gateway decodes ADDR == 0
  val wdata = Bits(32 bits)   // valid for writes only
}

case class SwdApRsp() extends Bundle {
  val error = Bool()          // completion error -> STICKYERR
  val data  = Bits(32 bits)   // read result (ignored for write completions)
}

/**
 * Phase 2B: ADI SW-DP register file behind the SwdPhy seam (SWD.md Phase 2B).
 *
 * DP register map (SWD, A[3:2]):
 *   read : 00 DPIDR | 01 CTRL/STAT (DPBANKSEL==0; other banks RAZ) | 10 RESEND | 11 RDBUFF
 *   write: 00 ABORT | 01 CTRL/STAT (DPBANKSEL==0; other banks WI)  | 10 SELECT | 11 TARGETSEL (v2) ignored
 *
 * ACK policy (combinational off the cmd pulse, so it lands within the turnaround):
 *   - FAULT: any sticky flag set, for AP accesses and RDBUFF reads (ADIv5.2 B4.2.4);
 *            other DP accesses keep responding OK so the host can read CTRL/STAT and ABORT.
 *   - WAIT : AP access or RDBUFF read while an AP transaction is outstanding.
 *   - OK   : everything else. The access itself only happens on OK.
 *
 * Scope limits: ORUNDETECT is stored but overrun detection is not implemented (STICKYORUN
 * and STICKYCMP are never set by hardware, only clearable); power-up ACKs mirror the REQs
 * (FPGA integration per SWD.md Phase 2D); DPIDR default is a placeholder with a non-ARM
 * DESIGNER field - set the real value per Phase 2D before host-tool integration.
 */
case class SwdDp(dpidr : BigInt = BigInt("0BA11AAB", 16)) extends Component {
  val io = new Bundle {
    val dp = new Bundle {
      val cmd = slave  Flow(SwdDpCmd())
      val rsp = master Flow(SwdDpRsp())
      val wr  = slave  Flow(SwdDpWrite())
    }
    val ap = new Bundle {
      val cmd = master Flow(SwdApCmd())
      val rsp = slave  Flow(SwdApRsp())
    }
  }

  // CTRL/STAT state
  val orunDetect   = Reg(Bool()) init(False)   // stored; overrun detection NOT implemented
  val stickyOrun   = Reg(Bool()) init(False)   // never set by hardware, ABORT-clearable
  val stickyCmp    = Reg(Bool()) init(False)   // never set by hardware, ABORT-clearable
  val stickyErr    = Reg(Bool()) init(False)   // set on AP completion error
  val wdataErr     = Reg(Bool()) init(False)   // set on SWD write-data parity error
  val cdbgPwrUpReq = Reg(Bool()) init(False)
  val csysPwrUpReq = Reg(Bool()) init(False)

  val select    = Reg(Bits(32 bits)) init(0)   // APSEL[31:24] APBANKSEL[7:4] DPBANKSEL[3:0]
  val dpBankSel = select(3 downto 0)

  val rdBuffer  = Reg(Bits(32 bits)) init(0)   // posted AP read result (RDBUFF / RESEND)
  val apBusy    = Reg(Bool()) init(False)
  val apWasRead = Reg(Bool()) init(False)      // outstanding transaction is a read
  val apDiscard = Reg(Bool()) init(False)      // DAPABORT: drop the in-flight completion

  val anySticky = stickyOrun || stickyCmp || stickyErr || wdataErr

  val ctrlStat = Bits(32 bits)
  ctrlStat := 0
  ctrlStat(0)  := orunDetect
  ctrlStat(1)  := stickyOrun
  ctrlStat(4)  := stickyCmp
  ctrlStat(5)  := stickyErr
  ctrlStat(7)  := wdataErr
  ctrlStat(28) := cdbgPwrUpReq
  ctrlStat(29) := cdbgPwrUpReq                 // CDBGPWRUPACK mirrors REQ
  ctrlStat(30) := csysPwrUpReq
  ctrlStat(31) := csysPwrUpReq                 // CSYSPWRUPACK mirrors REQ

  val cmd  = io.dp.cmd
  val isAp = cmd.payload.apNdp
  val addr = cmd.payload.addr
  val isRdbuffRead = !isAp && cmd.payload.rnw && addr === B"11"
  val gated = isAp || isRdbuffRead             // accesses subject to sticky/busy gating

  val ack = Bits(3 bits)
  when(anySticky && gated) {
    ack := SwdAck.FAULT
  } elsewhen(apBusy && gated) {
    ack := SwdAck.WAIT
  } otherwise {
    ack := SwdAck.OK
  }

  val dpReadData = Bits(32 bits)
  switch(addr) {
    is(B"00") { dpReadData := B(dpidr, 32 bits) }                            // DPIDR
    is(B"01") { dpReadData := (dpBankSel === 0) ? ctrlStat | B(0, 32 bits) } // banked
    is(B"10") { dpReadData := rdBuffer }                                     // RESEND
    is(B"11") { dpReadData := rdBuffer }                                     // RDBUFF
  }

  // Combinational response off the (registered) cmd pulse -> within the turnaround.
  io.dp.rsp.valid := cmd.valid
  io.dp.rsp.payload.ack   := ack
  io.dp.rsp.payload.rdata := isAp ? rdBuffer | dpReadData

  // A write's data arrives via wr after its ACK - remember the acked target.
  val last = new Area {
    val pendingWrite = Reg(Bool()) init(False)
    val isApReg      = Reg(Bool())
    val addrReg      = Reg(Bits(2 bits))
  }
  when(cmd.valid) {
    last.pendingWrite := !cmd.payload.rnw && ack === SwdAck.OK
    last.isApReg      := isAp
    last.addrReg      := addr
  }

  // AP completion
  when(io.ap.rsp.valid) {
    apBusy := False
    when(apDiscard) {
      apDiscard := False
    } otherwise {
      when(io.ap.rsp.payload.error) {
        stickyErr := True
      } elsewhen(apWasRead) {
        rdBuffer := io.ap.rsp.payload.data
      }
    }
  }

  // Write commit (fires after the WDATA phase; absent on WAIT/FAULT frames)
  val wr = io.dp.wr
  val apWrFire = False
  when(wr.valid) {
    last.pendingWrite := False
    when(!wr.payload.parityOk) {
      wdataErr := True                         // WDATAERR; the write is dropped
    } elsewhen(last.pendingWrite) {
      when(last.isApReg) {
        apWrFire := True
      } otherwise {
        switch(last.addrReg) {
          is(B"00") {                          // ABORT
            when(wr.payload.data(1)) { stickyCmp  := False }
            when(wr.payload.data(2)) { stickyErr  := False }
            when(wr.payload.data(3)) { wdataErr   := False }
            when(wr.payload.data(4)) { stickyOrun := False }
            when(wr.payload.data(0)) {         // DAPABORT
              when(apBusy) { apDiscard := True }
              apBusy := False
            }
          }
          is(B"01") {                          // CTRL/STAT (bank 0 only; others WI)
            when(dpBankSel === 0) {
              orunDetect   := wr.payload.data(0)
              cdbgPwrUpReq := wr.payload.data(28)
              csysPwrUpReq := wr.payload.data(30)
            }
          }
          is(B"10") { select := wr.payload.data }
          is(B"11") { }                        // TARGETSEL (SWD v2) - ignored in v1
        }
      }
    }
  }

  // AP launch: reads fire at the request (posted), writes fire at the data commit.
  val apRdFire = cmd.valid && isAp && cmd.payload.rnw && ack === SwdAck.OK
  io.ap.cmd.valid := apRdFire || apWrFire
  io.ap.cmd.payload.rnw   := apRdFire
  io.ap.cmd.payload.addr  := apRdFire ? addr | last.addrReg
  io.ap.cmd.payload.apSel := select(31 downto 24)
  io.ap.cmd.payload.wdata := wr.payload.data
  when(io.ap.cmd.valid) {                      // last assignment wins over the rsp clear
    apBusy    := True
    apWasRead := apRdFire
  }
}

/** Phase 2A + 2B assembly: line layer + SW-DP register file, exposing the AP seam (2C). */
case class SwdPhyDp(dpidr : BigInt = BigInt("0BA11AAB", 16)) extends Component {
  val io = new Bundle {
    val swdio = new Bundle {
      val i  = in  Bool()
      val o  = out Bool()
      val oe = out Bool()
    }
    val ap = new Bundle {
      val cmd = master Flow(SwdApCmd())
      val rsp = slave  Flow(SwdApRsp())
    }
  }
  val phy = SwdPhy()
  val dp  = SwdDp(dpidr)
  phy.io.swdio.i := io.swdio.i
  io.swdio.o  := phy.io.swdio.o
  io.swdio.oe := phy.io.swdio.oe
  dp.io.dp.cmd  << phy.io.dp.cmd
  phy.io.dp.rsp << dp.io.dp.rsp
  dp.io.dp.wr   << phy.io.dp.wr
  io.ap.cmd     << dp.io.ap.cmd
  dp.io.ap.rsp  << io.ap.rsp
}

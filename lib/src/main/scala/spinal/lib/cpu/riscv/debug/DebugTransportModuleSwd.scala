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

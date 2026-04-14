package rvspeccore.core

import chisel3._
import chisel3.util._
import spec._
import spec.instset._
import spec.instset.csr._
import rvspeccore.checker.ArbitraryRegFile

abstract class BaseCore()(implicit val config: RVConfig) extends Module {
  implicit val XLEN: Int = config.XLEN

  // State
  val now  = Wire(State())
  val next = Wire(State())
  // IO ports
  val iFetchpc = Wire(UInt(XLEN.W))
  val mem      = Wire(MemIO())
  val tlb      = if (config.functions.tlb) Some(Wire(TLBIO())) else None
  val commit   = Wire(CommitIO())
  // internal signals
  val inst  = Wire(UInt(32.W))
  val setpc = Wire(Bool())
}
class CommitIO(implicit XLEN: Int) extends Bundle {
  val exception = Bool()

  val readRs1 = Bool()
  val rs1Addr = UInt(5.W)
  val readRs2 = Bool()
  val rs2Addr = UInt(5.W)

  val rdAddr = UInt(5.W)
  val rdData = UInt(XLEN.W)

  val csrWr    = Bool()
  val csrAddr  = UInt(12.W)
  val csrNdata = UInt(XLEN.W)
}
object CommitIO {
  def apply()(implicit XLEN: Int): CommitIO = new CommitIO
}

class ReadMemIO()(implicit XLEN: Int) extends Bundle {
  val valid    = Output(Bool())
  val addr     = Output(UInt(XLEN.W))
  val memWidth = Output(UInt(log2Ceil(XLEN + 1).W))
  val data     = Input(UInt(XLEN.W))
}

class WriteMemIO()(implicit XLEN: Int) extends Bundle {
  val valid    = Output(Bool())
  val addr     = Output(UInt(XLEN.W))
  val memWidth = Output(UInt(log2Ceil(XLEN + 1).W))
  val data     = Output(UInt(XLEN.W))
}

class MemIO()(implicit XLEN: Int) extends Bundle {
  val read  = new ReadMemIO
  val write = new WriteMemIO
}
object MemIO {
  def apply()(implicit XLEN: Int): MemIO = new MemIO
}

class TLBIO()(implicit XLEN: Int) extends Bundle {
  val Anotherread  = Vec(3 + 3, new ReadMemIO())
  val Anotherwrite = Vec(3, new WriteMemIO())
}
object TLBIO {
  def apply()(implicit XLEN: Int): TLBIO = new TLBIO
}

// This contained registers about privileged extensions
class PrivilegedState()(implicit config: RVConfig) extends Bundle {
  val mode = UInt(2.W)
  val csr  = CSR()
}

object PrivilegedState {
  def apply()(implicit config: RVConfig): PrivilegedState = new PrivilegedState
  def wireInit()(implicit config: RVConfig): PrivilegedState = {
    val privilegedState = Wire(new PrivilegedState)

    privilegedState.mode := PrivilegeLevel.initLevel.asUInt
    privilegedState.csr  := CSR.wireInit()

    privilegedState
  }
}

// This extends BaseState with rf and pc
class State()(implicit config: RVConfig) extends Bundle {
  val XLEN: Int = config.XLEN

  val pc        = UInt(XLEN.W)
  val reg       = Vec(32, UInt(XLEN.W))
  val privilege = PrivilegedState()
}
object State {
  def apply()(implicit config: RVConfig): State = new State
  def wireInit()(implicit config: RVConfig): State = {
    implicit val XLEN = config.XLEN

    val state = Wire(new State)

    state.pc := config.initValue.getOrElse("pc", "h8000_0000").U(XLEN.W)
    state.reg := {
      if (config.formal.arbitraryRegFile) ArbitraryRegFile.gen
      else Seq.fill(32)(0.U(XLEN.W))
    }
    state.privilege := PrivilegedState.wireInit()

    state
  }
}

class RiscvTrans(singleInstMode: Option[Inst] = None)(implicit config: RVConfig) extends BaseCore with RVInstSet {
  val io = IO(new Bundle {
    // Processor IO
    val inst     = Input(UInt(32.W))
    val valid    = Input(Bool())
    val iFetchpc = Output(UInt(XLEN.W))
    val mem      = MemIO()
    val tlb      = if (config.functions.tlb) Some(TLBIO()) else None
    // Processor status
    val now  = Input(State())
    val next = Output(State())
    // Commit info
    val commit = Output(CommitIO())
  })

  // Initial the value
  now := io.now
  // these signals should keep the value in the next clock if there no changes below
  next     := now
  inst     := 0.U
  setpc    := false.B
  iFetchpc := now.pc
  commit   := 0.U.asTypeOf(CommitIO())

  // dont read or write mem
  // if there no LOAD/STORE below
  mem := 0.U.asTypeOf(new MemIO)
  tlb.map(_ := 0.U.asTypeOf(new TLBIO))

  // ID & EXE
  when(io.valid) {
    // CSR
    // TODO: merge into a function?
    // next.privilege.csr.mcycle := now.privilege.csr.mcycle + 1.U
    exceptionSupportInit()

    if (!config.functions.tlb) {
      inst     := io.inst
      iFetchpc := now.pc
    } else {
      val (resultStatus, resultPC) = iFetchTrans(now.pc)
      inst     := Mux(resultStatus, io.inst, "h0000_0013".U) // With a NOP instruction
      iFetchpc := resultPC
    }

    // Decode and Excute
    singleInstMode match {
      case Some(singleInst) => {
        doIBase(singleInst)
        if (config.extensions.C) doCExtension(singleInst)
        if (config.extensions.M) doMExtension(singleInst)
        if (config.functions.privileged) doPrivileged(singleInst)
        if (config.extensions.Zicsr) doZicsrExtension(singleInst)
        if (config.extensions.Zifencei) doZifenceiExecute(singleInst)
        if (config.extensions.B) doBExtension(singleInst)
      }
      case None => {
        doRVI
        if (config.extensions.C) doRVC
        if (config.extensions.M) doRVM
        if (config.functions.privileged) doRVPrivileged
        if (config.extensions.Zicsr) doRVZicsr
        if (config.extensions.Zifencei) doRVZifencei
        if (config.extensions.B) doRVB
      }
    }

    when(!setpc) {
      if (config.extensions.C) {
        // + 4.U for 32 bits width inst
        // + 2.U for 16 bits width inst in C extension
        next.pc := now.pc + Mux(inst(1, 0) === "b11".U, 4.U, 2.U)
      } else {
        next.pc := now.pc + 4.U
      }
    }
    tryRaiseException()
  }

  // mem port
  io.mem <> mem
  io.tlb.map(_ <> tlb.get)

  io.next     := next
  io.iFetchpc := iFetchpc
  io.commit <> commit
}

class RiscvCore(singleInstMode: Option[Inst] = None)(implicit config: RVConfig) extends Module {
  implicit val XLEN: Int = config.XLEN

  val io = IO(new Bundle {
    // Processor IO
    val inst     = Input(UInt(32.W))
    val valid    = Input(Bool())
    val iFetchpc = Output(UInt(XLEN.W))
    val mem      = MemIO()
    val tlb      = if (config.functions.tlb) Some(TLBIO()) else None
    // Processor status
    val now  = Output(State())
    val next = Output(State())
    // Sync from checker
    val sync = Flipped(Valid(State()))
  })

  val state = RegInit(State.wireInit())
  val trans = Module(new RiscvTrans(singleInstMode))

  trans.io.inst  := io.inst
  trans.io.valid := io.valid
  trans.io.mem <> io.mem
  trans.io.tlb.map(_ <> io.tlb.get)

  trans.io.now := state
  state        := Mux(io.sync.valid, io.sync.bits, trans.io.next)

  io.now      := state
  io.next     := trans.io.next
  io.iFetchpc := trans.io.iFetchpc
}

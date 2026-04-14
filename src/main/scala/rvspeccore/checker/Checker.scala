package rvspeccore.checker

import chisel3._
import chisel3.util._

import rvspeccore.core._
import rvspeccore.core.spec._
import rvspeccore.core.spec.instset.csr._
import rvspeccore.core.tool._
import dataclass.since

class InstCommit()(implicit XLEN: Int) extends Bundle {
  val valid = Bool()
  val excp  = Bool()
  val inst  = UInt(32.W)
  val pc    = UInt(XLEN.W)
  val npc   = UInt(XLEN.W)
}
object InstCommit {
  def apply()(implicit XLEN: Int) = new InstCommit
}

class StoreOrLoadInfo(implicit XLEN: Int) extends Bundle {
  val addr     = UInt(XLEN.W)
  val data     = UInt(XLEN.W)
  val memWidth = UInt(log2Ceil(XLEN + 1).W)
}
object StoreOrLoadInfo {
  def apply()(implicit XLEN: Int) = new StoreOrLoadInfo
}

class StoreOrLoadInfoTLB(implicit XLEN: Int) extends Bundle {
  val addr  = UInt(XLEN.W)
  val data  = UInt(XLEN.W)
  val level = UInt(log2Ceil(XLEN + 1).W)
}
object StoreOrLoadInfoTLB {
  def apply()(implicit XLEN: Int) = new StoreOrLoadInfoTLB
}

abstract class Checker(enableReg: Boolean = false)(implicit config: RVConfig) extends Module {
  implicit val XLEN: Int = config.XLEN

  /** Delay input data by a register if `delay` is true.
    *
    * This function helps to get signal values from the counterexample that only
    * contains values of registers from model checking.
    */
  def regDelay[T <: Data](data: T): T = {
    if (enableReg) RegNext(data, 0.U.asTypeOf(data.cloneType)) else data
  }

}

/** Checker with result port.
  *
  * Check pc of commited instruction and next value of all register. Although
  * `pc` in the result port, but it won't be checked.
  */
class CheckerWithState(
    enableReg: Boolean = false,
    singleInstMode: Option[Inst] = None
)(implicit
    config: RVConfig
) extends Checker {
  val io = IO(new Bundle {
    val instCommit = Input(InstCommit())
    val state      = Input(State())
    val mem        = if (config.formal.checkMem) Some(Input(MemIO())) else None
    val dtlbmem    = if (config.formal.checkMem && config.functions.tlb) Some(Input(TLBSig())) else None
    val itlbmem    = if (config.formal.checkMem && config.functions.tlb) Some(Input(TLBSig())) else None
  })
  // TODO: io.result has .internal states now, consider use it or not

  val checkInst = io.instCommit.valid && (singleInstMode match {
    case Some(inst) => inst(io.instCommit.inst)
    case None       => true.B
  })

  // link to spec core
  val specCore = Module(new RiscvCore(singleInstMode))
  specCore.io.valid        := checkInst
  specCore.io.inst         := io.instCommit.inst
  specCore.io.sync.valid   := io.instCommit.valid && !checkInst
  specCore.io.sync.bits    := io.state
  specCore.io.sync.bits.pc := io.instCommit.npc

  // initial another io.mem.get.Anotherread
  if (config.functions.tlb) {
    for (i <- 0 until 6) {
      specCore.io.tlb.get.Anotherread(i).data := DontCare
    }
  }

  // assertions
  specCore.io.mem.read.data := DontCare
  if (config.formal.checkMem) {
    val ignoreMem = io.instCommit.valid && (io.instCommit.excp || !checkInst)
    val loadQueue = Module(new Queue(new StoreOrLoadInfo, 1, true, true))
    loadQueue.io.enq.valid         := io.mem.get.read.valid
    loadQueue.io.enq.bits.addr     := io.mem.get.read.addr
    loadQueue.io.enq.bits.data     := io.mem.get.read.data
    loadQueue.io.enq.bits.memWidth := io.mem.get.read.memWidth

    loadQueue.io.deq.ready    := specCore.io.mem.read.valid || ignoreMem
    specCore.io.mem.read.data := loadQueue.io.deq.bits.data
    when(regDelay(specCore.io.mem.read.valid)) {
      // printf("[SpecCore] Load Queue Valid: %x %x %x %x\n", loadQueue.io.deq.valid, loadQueue.io.deq.bits.addr, loadQueue.io.deq.bits.data, loadQueue.io.deq.bits.memWidth)
      assert(!regDelay(io.instCommit.excp))
      assert(regDelay(loadQueue.io.deq.bits.addr) === regDelay(specCore.io.mem.read.addr))
      assert(regDelay(loadQueue.io.deq.bits.memWidth) === regDelay(specCore.io.mem.read.memWidth))
    }

    val storeQueue = Module(new Queue(new StoreOrLoadInfo, 1, true, true))
    storeQueue.io.enq.valid         := io.mem.get.write.valid
    storeQueue.io.enq.bits.addr     := io.mem.get.write.addr
    storeQueue.io.enq.bits.data     := io.mem.get.write.data
    storeQueue.io.enq.bits.memWidth := io.mem.get.write.memWidth

    storeQueue.io.deq.ready := specCore.io.mem.write.valid || ignoreMem
    when(regDelay(specCore.io.mem.write.valid)) {
      // printf("[SpecCore] store Queue Valid: %x %x %x %x\n", storeQueue.io.deq.valid, storeQueue.io.deq.bits.addr, storeQueue.io.deq.bits.data, storeQueue.io.deq.bits.memWidth)
      assert(!regDelay(io.instCommit.excp))
      assert(regDelay(storeQueue.io.deq.bits.addr) === regDelay(specCore.io.mem.write.addr))
      assert(regDelay(storeQueue.io.deq.bits.memWidth) === regDelay(specCore.io.mem.write.memWidth))
      val storeDataMask = specCore.trans.width2Mask(specCore.io.mem.write.memWidth)
      assert(((regDelay(storeQueue.io.deq.bits.data) ^ regDelay(specCore.io.mem.write.data)) & storeDataMask) === 0.U)
    }

    if (config.functions.tlb) {
      /* tlbLoadQueuess(0) -> level 2
       * tlbLoadQueuess(1) -> level 1
       * tlbLoadQueuess(2) -> level 0
       */
      val tlbLoadQueues = Seq.fill(3)(Module(new Queue(new StoreOrLoadInfoTLB, 1, true, true)))
      // initial the queue
      for (i <- 0 until 3) {
        tlbLoadQueues(i).io.enq.valid      := io.dtlbmem.get.read.valid && (io.dtlbmem.get.read.level === (2 - i).U)
        tlbLoadQueues(i).io.enq.bits.addr  := io.dtlbmem.get.read.addr
        tlbLoadQueues(i).io.enq.bits.data  := io.dtlbmem.get.read.data
        tlbLoadQueues(i).io.enq.bits.level := io.dtlbmem.get.read.level

        tlbLoadQueues(i).io.deq.ready           := specCore.io.tlb.get.Anotherread(i).valid || ignoreMem
        specCore.io.tlb.get.Anotherread(i).data := tlbLoadQueues(i).io.deq.bits.data

        when(regDelay(specCore.io.tlb.get.Anotherread(i).valid)) {
          assert(regDelay(tlbLoadQueues(i).io.deq.bits.addr) === regDelay(specCore.io.tlb.get.Anotherread(i).addr))
        }
      }
    }

  }

  when(regDelay(checkInst)) {
    // now pc:
    assert(regDelay(io.instCommit.pc) === regDelay(specCore.io.now.pc))
    // next pc: hard to get next pc in a pipeline, it's ok to check it at next instruction
    if (config.formal.checkNPC) assert(regDelay(io.instCommit.npc) === regDelay(specCore.io.next.pc))

    // next reg
    for (i <- 0 until 32) {
      assert(regDelay(io.state.reg(i.U)) === regDelay(specCore.io.next.reg(i.U)))
    }

    // next csr:
    if (config.formal.checkCSRs) {
      io.state.privilege.csr.table.zip(specCore.io.next.privilege.csr.table).map {
        case (dut, spec) => {
          assert(regDelay(dut.signal) === regDelay(spec.signal))
        }
      }
    }
  }

}

class WriteBack()(implicit XLEN: Int) extends Bundle {
  val rs1Addr = UInt(5.W)
  val rs2Addr = UInt(5.W)
  val rs1Data = UInt(XLEN.W)
  val rs2Data = UInt(XLEN.W)

  val rdAddr = UInt(5.W)
  val rdData = UInt(XLEN.W)

  val csrWr    = Bool()
  val csrAddr  = UInt(12.W)
  val csrNdata = UInt(XLEN.W)
}
object WriteBack {
  def apply()(implicit XLEN: Int) = new WriteBack
}

/** Checker with write back port.
  *
  * Check pc of commited instruction, the register been write back and the
  * register with privilege information. privilege contains some register value
  * before DUT execute the instruction. wb contains some writeback signal.
  */
class CheckerWithAction(
    enableReg: Boolean = false,
    singleInstMode: Option[Inst] = None
)(implicit
    config: RVConfig
) extends Checker {
  val io = IO(new Bundle {
    val instCommit = Input(InstCommit())
    val writeback  = Input(WriteBack())
    val privilege  = Input(PrivilegedState())
    val mem        = if (config.formal.checkMem) Some(Input(new MemIO)) else None
    val dtlbmem    = if (config.formal.checkMem && config.functions.tlb) Some(Input(new TLBSig)) else None
    val itlbmem    = if (config.formal.checkMem && config.functions.tlb) Some(Input(new TLBSig)) else None
  })

  val checkInst = io.instCommit.valid && (singleInstMode match {
    case Some(inst) => inst(io.instCommit.inst)
    case None       => true.B
  })
  // link to spec core
  val specCore = Module(new RiscvTrans(singleInstMode))
  specCore.io.now                           := 0.U.asTypeOf(new State)
  specCore.io.now.privilege                 := io.privilege
  specCore.io.now.pc                        := io.instCommit.pc
  specCore.io.now.reg(io.writeback.rs1Addr) := io.writeback.rs1Data
  // if r1addr == r2addr and rs2 is not use, the value of rs1 should not be cover by the value of rs2
  when(io.writeback.rs1Addr =/= io.writeback.rs2Addr) {
    specCore.io.now.reg(io.writeback.rs2Addr) := io.writeback.rs2Data
  }
  specCore.io.valid := checkInst
  specCore.io.inst  := io.instCommit.inst

  // initial another io.mem.get.Anotherread
  if (config.functions.tlb) {
    for (i <- 0 until 6) {
      specCore.io.tlb.get.Anotherread(i).data := DontCare
    }
  }

  val specCommit = specCore.io.commit
  val specMem    = specCore.io.mem
  val specTlb    = specCore.io.tlb
  val specNPC    = specCore.io.next.pc

  // check memory behavior
  specCore.io.mem.read.data := DontCare
  if (config.formal.checkMem) {
    val ignoreMem = io.instCommit.valid && (io.instCommit.excp || !checkInst)
    val loadQueue = Module(new Queue(new StoreOrLoadInfo, 1, true, true))
    loadQueue.io.enq.valid         := io.mem.get.read.valid
    loadQueue.io.enq.bits.addr     := io.mem.get.read.addr
    loadQueue.io.enq.bits.data     := io.mem.get.read.data
    loadQueue.io.enq.bits.memWidth := io.mem.get.read.memWidth

    loadQueue.io.deq.ready := specMem.read.valid || ignoreMem
    specMem.read.data      := loadQueue.io.deq.bits.data
    when(regDelay(specMem.read.valid)) {
      assert(!regDelay(io.instCommit.excp))
      assert(regDelay(loadQueue.io.deq.bits.addr) === regDelay(specMem.read.addr))
      assert(regDelay(loadQueue.io.deq.bits.memWidth) === regDelay(specMem.read.memWidth))
    }

    val storeQueue = Module(new Queue(new StoreOrLoadInfo, 1, true, true))
    storeQueue.io.enq.valid         := io.mem.get.write.valid
    storeQueue.io.enq.bits.addr     := io.mem.get.write.addr
    storeQueue.io.enq.bits.data     := io.mem.get.write.data
    storeQueue.io.enq.bits.memWidth := io.mem.get.write.memWidth

    storeQueue.io.deq.ready := specMem.write.valid || ignoreMem
    when(regDelay(specMem.write.valid)) {
      assert(!regDelay(io.instCommit.excp))
      assert(regDelay(storeQueue.io.deq.bits.addr) === regDelay(specMem.write.addr))
      assert(regDelay(storeQueue.io.deq.bits.memWidth) === regDelay(specMem.write.memWidth))
      val storeDataMask = specCore.width2Mask(specMem.write.memWidth)
      assert(((regDelay(storeQueue.io.deq.bits.data) ^ regDelay(specMem.write.data)) & storeDataMask) === 0.U)
    }

    if (config.functions.tlb) {
      /* tlbLoadQueuess(0) -> level 2
       * tlbLoadQueuess(1) -> level 1
       * tlbLoadQueuess(2) -> level 0
       */
      val tlbLoadQueues = Seq.fill(3)(Module(new Queue(new StoreOrLoadInfoTLB, 1, true, true)))
      // initial the queue
      for (i <- 0 until 3) {
        tlbLoadQueues(i).io.enq.valid      := io.dtlbmem.get.read.valid && (io.dtlbmem.get.read.level === (2 - i).U)
        tlbLoadQueues(i).io.enq.bits.addr  := io.dtlbmem.get.read.addr
        tlbLoadQueues(i).io.enq.bits.data  := io.dtlbmem.get.read.data
        tlbLoadQueues(i).io.enq.bits.level := io.dtlbmem.get.read.level

        tlbLoadQueues(i).io.deq.ready   := specTlb.get.Anotherread(i).valid || ignoreMem
        specTlb.get.Anotherread(i).data := tlbLoadQueues(i).io.deq.bits.data

        when(regDelay(specTlb.get.Anotherread(i).valid)) {
          assert(regDelay(tlbLoadQueues(i).io.deq.bits.addr) === regDelay(specTlb.get.Anotherread(i).addr))
        }
      }
    }
  }

  when(regDelay(checkInst)) {
    if (config.formal.checkNPC) assert(regDelay(io.instCommit.npc) === regDelay(specNPC))

    assert(regDelay(io.instCommit.excp) === regDelay(specCommit.exception))

    when(!regDelay(specCommit.exception)) {
      assert(regDelay(io.writeback.rdAddr) === regDelay(specCommit.rdAddr))
      when(io.writeback.rdAddr =/= 0.U) {
        assert(regDelay(io.writeback.rdData) === regDelay(specCommit.rdData))
        assert(regDelay(io.writeback.rdData) === regDelay(specCore.io.next.reg(io.writeback.rdAddr)))
      }

      // try to verify two operands of instruction
      when(regDelay(specCommit.readRs1)) {
        when(regDelay(io.writeback.rs1Addr) === 0.U) {
          assert(regDelay(io.writeback.rs1Data) === 0.U)
        }
        assert(regDelay(io.writeback.rs1Addr) === regDelay(specCommit.rs1Addr))
      }
      when(regDelay(specCommit.readRs2)) {
        when(regDelay(io.writeback.rs2Addr) === 0.U) {
          assert(regDelay(io.writeback.rs2Data) === 0.U)
        }
        assert(regDelay(io.writeback.rs2Addr) === regDelay(specCommit.rs2Addr))
      }

      // try to verify csr write and read
      if (config.formal.checkCSRs) {
        when(regDelay(specCommit.csrWr) || regDelay(io.writeback.csrWr)) {
          assert(regDelay(specCommit.csrWr) === regDelay(io.writeback.csrWr))
          assert(regDelay(specCommit.csrAddr) === regDelay(io.writeback.csrAddr))
          assert(regDelay(specCommit.csrNdata) === regDelay(io.writeback.csrNdata))
        }
      }
    }
  }

}

@deprecated(
  message = "CheckerWithResult is deprecated. " +
    "Use CheckerWithState with RVConfig.formal (e.g., enable \"CheckMem\") instead.",
  since = "riscvspeccore 1.3"
)
class CheckerWithResult(
    val checkMem: Boolean = true,
    enableReg: Boolean = false,
    singleInstMode: Option[Inst] = None
)(implicit
    config: RVConfig
) extends Checker {
  val io = IO(new Bundle {
    val instCommit = Input(new Bundle {
      val valid = Bool()
      val inst  = UInt(32.W)
      val pc    = UInt(XLEN.W)
      val npc   = UInt(XLEN.W)
    })
    val result = Input(new Bundle {
      val pc  = UInt(XLEN.W)
      val reg = Vec(32, UInt(XLEN.W))
      val privilege = new Bundle {
        val csr = CSR()
        val internal = new Bundle {
          val privilegeMode = UInt(2.W)
        }
      }
    })
    val event = Input(new Bundle {
      val valid         = Bool()
      val intrNO        = UInt(XLEN.W)
      val cause         = UInt(XLEN.W)
      val exceptionPC   = UInt(XLEN.W)
      val exceptionInst = UInt(XLEN.W)
    })
    val mem     = if (checkMem) Some(Input(new MemIO)) else None
    val dtlbmem = if (checkMem && config.functions.tlb) Some(Input(new TLBSig)) else None
    val itlbmem = if (checkMem && config.functions.tlb) Some(Input(new TLBSig)) else None
  })

  private val newFormal = {
    val raw = config.formal.raw
    val updated =
      if (checkMem) raw.toSet + "CheckMem"
      else raw.toSet - "CheckMem"
    updated.toSeq
  }

  private val newConfig = RVConfig(
    config.XLEN,
    config.extensions.raw,
    config.fakeExtensions.raw,
    config.initValue,
    config.functions.raw,
    newFormal
  )

  val checker = Module(new CheckerWithState(enableReg, singleInstMode)(newConfig))

  checker.io.instCommit.valid := io.instCommit.valid
  checker.io.instCommit.excp  := io.event.valid
  checker.io.instCommit.inst  := io.instCommit.inst
  checker.io.instCommit.pc    := io.instCommit.pc
  checker.io.instCommit.npc   := io.instCommit.npc

  checker.io.state.pc             := io.result.pc
  checker.io.state.reg            := io.result.reg
  checker.io.state.privilege.csr  := io.result.privilege.csr
  checker.io.state.privilege.mode := io.result.privilege.internal.privilegeMode

  checker.io.mem.foreach(_ := io.mem.get)
  checker.io.dtlbmem.foreach(_ := io.dtlbmem.get)
  checker.io.itlbmem.foreach(_ := io.itlbmem.get)
}

@deprecated(
  message = "CheckerWithWB is deprecated. " +
    "Use CheckerWithAction with RVConfig.formal (e.g., enable \"CheckMem\" \"checkNPC\") instead.",
  since = "riscvspeccore 1.3"
)
class CheckerWithWB(
    val checkMem: Boolean = true,
    enableReg: Boolean = false,
    singleInstMode: Option[Inst] = None,
    checkNPC: Boolean = false
)(implicit
    config: RVConfig
) extends Checker {
  val io = IO(new Bundle {
    val instCommit = Input(new Bundle() {
      val valid = Bool()
      val inst  = UInt(32.W)
      val pc    = UInt(XLEN.W)
      val npc   = UInt(XLEN.W)
    })
    val wb = Input(WriteBack())
    val privilege = Input(new Bundle() {
      val csr = CSR()
      val internal = new Bundle {
        val privilegeMode = UInt(2.W)
      }
    })
    val mem     = if (checkMem) Some(Input(new MemIO)) else None
    val dtlbmem = if (checkMem && config.functions.tlb) Some(Input(new TLBSig)) else None
    val itlbmem = if (checkMem && config.functions.tlb) Some(Input(new TLBSig)) else None
  })

  private val newFormal = {
    val raw     = config.formal.raw
    val updated = raw.toSet
    updated.toSeq
  }

  private val newConfig = RVConfig(
    config.XLEN,
    config.extensions.raw,
    config.fakeExtensions.raw,
    config.initValue,
    config.functions.raw,
    newFormal
  )

  val checker = Module(new CheckerWithAction(enableReg, singleInstMode)(newConfig))

  checker.io.instCommit.valid := io.instCommit.valid
  checker.io.instCommit.excp  := false.B
  checker.io.instCommit.inst  := io.instCommit.inst
  checker.io.instCommit.pc    := io.instCommit.pc
  checker.io.instCommit.npc   := io.instCommit.npc

  checker.io.writeback := io.wb

  checker.io.privilege.mode := io.privilege.internal.privilegeMode
  checker.io.privilege.csr  := io.privilege.csr

  checker.io.mem.foreach(_ := io.mem.get)
  checker.io.dtlbmem.foreach(_ := io.dtlbmem.get)
  checker.io.itlbmem.foreach(_ := io.itlbmem.get)
}

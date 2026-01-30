package rvspeccore.checker

import chisel3._
import chisel3.util._
import rvspeccore.core._
import rvspeccore.core.spec.Inst
import rvspeccore.core.spec.instset.csr.{CSR, CSRInfoSignal, EventSig}
import rvspeccore.core.tool.TLBMemInfo
import rvspeccore.core.tool.TLBSig

abstract class Checker()(implicit config: RVConfig) extends Module {
  implicit val XLEN: Int = config.XLEN
}

class InstCommit()(implicit XLEN: Int) extends Bundle {
  val valid = Bool()
  val inst  = UInt(32.W)
  val pc    = UInt(XLEN.W)

  val npc = UInt(XLEN.W)
}
object InstCommit {
  def apply()(implicit XLEN: Int) = new InstCommit
}
class StoreOrLoadInfo(implicit XLEN: Int) extends Bundle {
  val addr     = UInt(XLEN.W)
  val data     = UInt(XLEN.W)
  val memWidth = UInt(log2Ceil(XLEN + 1).W)
}
class StoreOrLoadInfoTLB(implicit XLEN: Int) extends Bundle {
  val addr  = UInt(XLEN.W)
  val data  = UInt(XLEN.W)
  val level = UInt(log2Ceil(XLEN + 1).W)
}

/** Checker with result port.
  *
  * Check pc of commited instruction and next value of all register. Although
  * `pc` in the result port, but it won't be checked.
  */
class CheckerWithResult(
    val checkMem: Boolean = true,
    enableReg: Boolean = false,
    singleInstMode: Option[Inst] = None
)(implicit
    config: RVConfig
) extends Checker {
  val io = IO(new Bundle {
    val instCommit = Input(InstCommit())
    val result     = Input(State())
    val event      = Input(new EventSig())
    val mem        = if (checkMem) Some(Input(new MemIO)) else None
    val dtlbmem    = if (checkMem && config.functions.tlb) Some(Input(new TLBSig)) else None
    val itlbmem    = if (checkMem && config.functions.tlb) Some(Input(new TLBSig)) else None
  })
  // TODO: io.result has .internal states now, consider use it or not

  /** Delay input data by a register if `delay` is true.
    *
    * This function helps to get signal values from the counterexample that only
    * contains values of registers from model checking.
    */
  def regDelay[T <: Data](data: T): T = {
    if (enableReg) RegNext(data, 0.U.asTypeOf(data.cloneType)) else data
  }

  val checkInst = io.instCommit.valid && (singleInstMode match {
    case Some(inst) => inst(io.instCommit.inst)
    case None       => true.B
  })

  // link to spec core
  val specCore = Module(new RiscvCore(singleInstMode))
  specCore.io.valid := checkInst
  specCore.io.inst  := io.instCommit.inst

  // initial another io.mem.get.Anotherread
  if (config.functions.tlb) {
    for (i <- 0 until 6) {
      specCore.io.tlb.get.Anotherread(i).data := DontCare
    }
  }

  // assertions

  specCore.io.mem.read.data := DontCare
  if (checkMem) {
    val ignoreMem = io.instCommit.valid && !checkInst
    val loadQueue = Module(new Queue(new StoreOrLoadInfo, 1, true, true))
    loadQueue.io.enq.valid         := io.mem.get.read.valid
    loadQueue.io.enq.bits.addr     := io.mem.get.read.addr
    loadQueue.io.enq.bits.data     := io.mem.get.read.data
    loadQueue.io.enq.bits.memWidth := io.mem.get.read.memWidth

    loadQueue.io.deq.ready    := specCore.io.mem.read.valid || ignoreMem
    specCore.io.mem.read.data := loadQueue.io.deq.bits.data
    when(regDelay(specCore.io.mem.read.valid)) {
      // printf("[SpecCore] Load Queue Valid: %x %x %x %x\n", loadQueue.io.deq.valid, loadQueue.io.deq.bits.addr, loadQueue.io.deq.bits.data, loadQueue.io.deq.bits.memWidth)
      assert(regDelay(loadQueue.io.deq.bits.addr) === regDelay(specCore.io.mem.read.addr))
      assert(regDelay(loadQueue.io.deq.bits.memWidth) === regDelay(specCore.io.mem.read.memWidth))
    }

    val storeQueue = Module(new Queue(new StoreOrLoadInfo, 1, true, true))
    storeQueue.io.enq.valid         := io.mem.get.write.valid
    storeQueue.io.enq.bits.addr     := io.mem.get.write.addr
    storeQueue.io.enq.bits.data     := io.mem.get.write.data
    storeQueue.io.enq.bits.memWidth := io.mem.get.write.memWidth

    storeQueue.io.deq.ready    := specCore.io.mem.write.valid || ignoreMem
    when(regDelay(specCore.io.mem.write.valid)) {
      // printf("[SpecCore] store Queue Valid: %x %x %x %x\n", storeQueue.io.deq.valid, storeQueue.io.deq.bits.addr, storeQueue.io.deq.bits.data, storeQueue.io.deq.bits.memWidth)
      assert(regDelay(storeQueue.io.deq.bits.addr) === regDelay(specCore.io.mem.write.addr))
      assert(regDelay(storeQueue.io.deq.bits.data) === regDelay(specCore.io.mem.write.data))
      assert(regDelay(storeQueue.io.deq.bits.memWidth) === regDelay(specCore.io.mem.write.memWidth))
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
    // next pc: hard to get next pc in a pipeline, check it at next instruction
    // next csr:
    if (config.formal.checkCSRs) {
      io.result.privilege.csr.table.zip(specCore.io.next.privilege.csr.table).map {
        case (result, next) => {
          assert(regDelay(result.signal) === regDelay(next.signal))
        }
      }
    }
    // next reg
    for (i <- 0 until 32) {
      assert(regDelay(io.result.reg(i.U)) === regDelay(specCore.io.next.reg(i.U)))
    }
  }

  when(regDelay(io.event.valid) || regDelay(specCore.io.event.valid)) {
    // Make sure DUT and specCore currently occur the same exception
    assert(regDelay(io.event.valid) === regDelay(specCore.io.event.valid))
    assert(regDelay(io.event.intrNO) === regDelay(specCore.io.event.intrNO))
    assert(regDelay(io.event.cause) === regDelay(specCore.io.event.cause))
    assert(regDelay(io.event.exceptionPC) === regDelay(specCore.io.event.exceptionPC))
    assert(regDelay(io.event.exceptionInst) === regDelay(specCore.io.event.exceptionInst))
  }

}

class WriteBack()(implicit XLEN: Int) extends Bundle {
  val valid = Bool()
  val dest  = UInt(5.W)
  val data  = UInt(XLEN.W)

  val r1Addr = UInt(5.W)
  val r2Addr = UInt(5.W)
  val r1Data = UInt(XLEN.W)
  val r2Data = UInt(XLEN.W)

  val csrAddr  = UInt(12.W)
  val csrNdata = UInt(64.W)
  val csrWr    = Bool()
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
class CheckerWithWB(
    val checkMem: Boolean = true,
    enableReg: Boolean = true,
    singleInstMode: Option[Inst] = None,
    checkNPC: Boolean = false
)(implicit
    config: RVConfig
) extends Checker {
  val io = IO(new Bundle {
    val instCommit = Input(InstCommit())
    val wb         = Input(WriteBack())
    val privilege  = Input(PrivilegedState())
    val mem        = if (checkMem) Some(Input(new MemIO)) else None
    val dtlbmem    = if (checkMem && config.functions.tlb) Some(Input(new TLBSig)) else None
    val itlbmem    = if (checkMem && config.functions.tlb) Some(Input(new TLBSig)) else None
  })

  def regDelay[T <: Data](data: T): T = {
    if (enableReg) RegNext(data, 0.U.asTypeOf(data.cloneType)) else data
  }

  val checkInst = io.instCommit.valid && (singleInstMode match {
    case Some(inst) => inst(io.instCommit.inst)
    case None       => true.B
  })
  // link to spec core
  val specCore = Module(new RiscvTrans(singleInstMode))

  specCore.io.now                   := 0.U.asTypeOf(new State)
  specCore.io.now.privilege         := io.privilege
  specCore.io.now.pc                := io.instCommit.pc
  specCore.io.now.reg(io.wb.r1Addr) := io.wb.r1Data
  // if r1addr == r2addr and rs2 is not use, the value of rs1 should not be cover by the value of rs2
  when(io.wb.r1Addr =/= io.wb.r2Addr) {
    specCore.io.now.reg(io.wb.r2Addr) := io.wb.r2Data
  }

  specCore.io.valid := checkInst
  specCore.io.inst  := io.instCommit.inst

  val specCoreWBValid = specCore.io.specWb.rd_en
  val specCoreWBDest  = specCore.io.specWb.rd_addr
  val specCoreWBData  = specCore.io.specWb.rd_data
  val specCoreNpcs    = specCore.io.next.pc
  val specCoreCsrAddr = specCore.io.specWb.csr_addr
  val specCoreCsrWr   = specCore.io.specWb.csr_wr

  // check memory behavior
  specCore.io.mem.read.data := DontCare
  if (checkMem) {
    val ignoreMem = io.instCommit.valid && !checkInst
    val loadQueue = Module(new Queue(new StoreOrLoadInfo, 1, true, true))
    loadQueue.io.enq.valid         := io.mem.get.read.valid
    loadQueue.io.enq.bits.addr     := io.mem.get.read.addr
    loadQueue.io.enq.bits.data     := io.mem.get.read.data
    loadQueue.io.enq.bits.memWidth := io.mem.get.read.memWidth

    loadQueue.io.deq.ready    := specCore.io.mem.read.valid || ignoreMem
    specCore.io.mem.read.data := loadQueue.io.deq.bits.data
    when(regDelay(specCore.io.mem.read.valid)) {
      assert(regDelay(loadQueue.io.deq.bits.addr) === regDelay(specCore.io.mem.read.addr))
      assert(regDelay(loadQueue.io.deq.bits.memWidth) === regDelay(specCore.io.mem.read.memWidth))
    }

    val storeQueue = Module(new Queue(new StoreOrLoadInfo, 1, true, true))
    storeQueue.io.enq.valid         := io.mem.get.write.valid
    storeQueue.io.enq.bits.addr     := io.mem.get.write.addr
    storeQueue.io.enq.bits.data     := io.mem.get.write.data
    storeQueue.io.enq.bits.memWidth := io.mem.get.write.memWidth

    storeQueue.io.deq.ready    := specCore.io.mem.write.valid || ignoreMem
    when(regDelay(specCore.io.mem.write.valid)) {
      assert(regDelay(storeQueue.io.deq.bits.addr) === regDelay(specCore.io.mem.write.addr))
      assert(regDelay(storeQueue.io.deq.bits.data) === regDelay(specCore.io.mem.write.data))
      assert(regDelay(storeQueue.io.deq.bits.memWidth) === regDelay(specCore.io.mem.write.memWidth))
    }

    if (config.functions.tlb) {
      /* tlbLoadQueuess(0) -> level 2
       * tlbLoadQueuess(1) -> level 1
       * tlbLoadQueuess(2) -> level 0
       */
      val tlbLoadQueues = Seq.fill(3)(new Queue(new StoreOrLoadInfoTLB, 1, true, true))
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
    if (checkNPC) {
      assert(regDelay(io.instCommit.npc) === regDelay(specCoreNpcs(31, 0)))
    }

    when(regDelay(specCoreWBValid) && regDelay(io.wb.valid)) {
      // if reference and dut all raise the valid, compare the dest and the data
      assert(regDelay(io.wb.dest) === regDelay(specCoreWBDest))
      assert(regDelay(io.wb.data) === regDelay(specCoreWBData))
      assert(regDelay(io.wb.data) === regDelay(specCore.io.next.reg(io.wb.dest)))
    }.elsewhen(regDelay(io.wb.valid)) {
      // DUT may try to write back to x0, but it should not take effect
      // if DUT dose write in x0, it will be check out at next instruction
      when(regDelay(io.wb.dest) =/= 0.U) {
        assert(regDelay(io.wb.data) === regDelay(specCore.io.next.reg(io.wb.dest)))
      }
    }.elsewhen(regDelay(specCoreWBValid)) {
      // if reference raise but dut does't and the dest is not x0, we think that it's invalid
      assert(regDelay(specCoreWBDest) === 0.U)
    }

    // try to verify two operands of instruction
    when(regDelay(specCore.io.specWb.checkrs1)) {
      when(regDelay(io.wb.r1Addr) === 0.U) {
        assert(regDelay(io.wb.r1Data) === 0.U)
      }
      assert(regDelay(io.wb.r1Addr) === regDelay(specCore.io.specWb.rs1_addr))
    }
    when(regDelay(specCore.io.specWb.checkrs2)) {
      when(regDelay(io.wb.r2Addr) === 0.U) {
        assert(regDelay(io.wb.r2Data) === 0.U)
      }
      assert(regDelay(io.wb.r2Addr) === regDelay(specCore.io.specWb.rs2_addr))
    }

    // try to verify csr write and read
    if (config.formal.checkCSRs) {
      when(regDelay(specCoreCsrWr) || regDelay(io.wb.csrWr)) {
        assert(regDelay(specCoreCsrWr) === regDelay(io.wb.csrWr))
        assert(regDelay(specCoreCsrAddr) === regDelay(io.wb.csrAddr))
        val specCoreCsrNdata = WireInit(0.U(64.W))
        specCore.io.next.privilege.csr.table.foreach { case (CSRInfoSignal(info, nextCSR)) =>
          when(io.wb.csrAddr === info.addr) {
            specCoreCsrNdata := nextCSR
          }
        }
        assert(regDelay(specCoreCsrNdata) === regDelay(io.wb.csrNdata))
      }
    }
  }

}

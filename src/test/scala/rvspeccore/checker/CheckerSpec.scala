package rvspeccore.checker

import chisel3._
import chiseltest._
import org.scalatest._
import org.scalatest.flatspec.AnyFlatSpec

import rvspeccore.core._
import rvspeccore.core.spec.instset.csr.CSRInfoSignal

class CheckerWithResultSpec extends AnyFlatSpec with ChiselScalatestTester {
  behavior of "CheckerWithResult"

  implicit val config = RVConfig(
    XLEN = 64,
    extensions = "MCZifenceiZicsrZbaZbbZbcZbsZbkbZbkcZbkx",
    functions = Seq("Privileged")
  )

  class TestCore(checkMem: Boolean = true, enableReg: Boolean = false) extends RiscvCore(None) {
    val checker = Module(new CheckerWithResult(checkMem = checkMem, enableReg = enableReg))
    checker.io.instCommit.valid    := RegNext(io.valid, false.B)
    checker.io.instCommit.inst     := RegNext(io.inst)
    checker.io.instCommit.pc       := RegNext(state.pc)
    checker.io.instCommit.npc      := DontCare
    checker.io.event.valid         := RegNext(io.event.valid, false.B)
    checker.io.event.intrNO        := RegNext(io.event.intrNO)
    checker.io.event.cause         := RegNext(io.event.cause)
    checker.io.event.exceptionPC   := RegNext(io.event.exceptionPC)
    checker.io.event.exceptionInst := RegNext(io.event.exceptionInst)
    // printf("[  DUT   ] Valid:%x PC: %x Inst: %x\n", checker.io.instCommit.valid, checker.io.instCommit.pc, checker.io.instCommit.inst)
    checker.io.result := state

    checker.io.itlbmem.map(cm => {
      cm := DontCare
    })

    checker.io.dtlbmem.map(cm => {
      cm := DontCare
    })
    // checker.io.tlb.get.Anotherwrite := DontCare
    checker.io.mem.map(cm => {
      cm.read.addr     := RegNext(trans.io.mem.read.addr)
      cm.read.data     := RegNext(trans.io.mem.read.data)
      cm.read.memWidth := RegNext(trans.io.mem.read.memWidth)
      cm.read.valid    := RegNext(trans.io.mem.read.valid)

      cm.write.addr     := RegNext(trans.io.mem.write.addr)
      cm.write.data     := RegNext(trans.io.mem.write.data)
      cm.write.memWidth := RegNext(trans.io.mem.write.memWidth)
      cm.write.valid    := RegNext(trans.io.mem.write.valid)
    })
  }

  behavior of "CheckerWithResult"

  it should "pass RiscvTests without mem check" in {
    val tests = Seq(
      RiscvTests("rv64ui", "rv64ui-addi.hex")
    )
    tests.foreach { testFile =>
      test(new CoreTester(new TestCore(false), testFile.getCanonicalPath())) { c =>
        RiscvTests.stepTest(c, RiscvTests.maxStep)
        RiscvTests.checkReturn(c)
      }
    }
  }

  val tests =
    Seq("rv64ui", "rv64um", "rv64uc", "rv64uzba", "rv64uzbb", "rv64uzbc", "rv64uzbs", "rv64uzbkb", "rv64uzbkx")

  tests.foreach { testCase =>
    RiscvTests(testCase).foreach(f =>
      it should s"pass RiscvTests with mem check @${f.getName}" in {
        test(new CoreTester(new TestCore, f.getCanonicalPath())) { c =>
          RiscvTests.stepTest(c, RiscvTests.maxStep)
          RiscvTests.checkReturn(c)
        }
      }
    )
  }

  tests.foreach { testCase =>
    RiscvTests(testCase).foreach(f =>
      it should s"pass RiscvTests with reg delay @${f.getName}" in {
        test(new CoreTester(new TestCore(true, true), f.getCanonicalPath())) { c =>
          RiscvTests.stepTest(c, RiscvTests.maxStep)
          RiscvTests.checkReturn(c)
        }
      }
    )
  }
}
// We have to extract some signals from RiscvCore, but it certainly modify the structure of the RiscvCore
// This can't be solved until we discuss with YiCheng about it.
class CheckerWithWBSpec extends AnyFlatSpec with ChiselScalatestTester {
  behavior of "CheckerWithWB"

  implicit val config = RVConfig(
    XLEN = 64,
    extensions = "MCZifenceiZicsrZbaZbbZbcZbsZbkbZbkcZbkx",
    functions = Seq("Privileged")
  )

  class TestCore(checkMem: Boolean = true, enableReg: Boolean = false) extends RiscvCore {
    val wb = Wire(new WriteBack)

    wb := 0.U.asTypeOf(new WriteBack)

    wb.valid   := trans.io.specWb.rd_en
    wb.dest    := trans.io.specWb.rd_addr
    wb.data    := trans.io.specWb.rd_data
    wb.csrAddr := trans.io.specWb.csr_addr
    wb.r1Addr  := trans.io.specWb.rs1_addr
    wb.r2Addr  := trans.io.specWb.rs2_addr
    wb.r1Data  := state.reg(wb.r1Addr)
    wb.r2Data  := state.reg(wb.r2Addr)

    trans.io.next.privilege.csr.table.foreach { case (CSRInfoSignal(info, nextCSR)) =>
      when(wb.csrAddr === info.addr) {
        wb.csrNdata := nextCSR
      }
    }
    wb.csrWr := trans.io.specWb.csr_wr

    val checker = Module(new CheckerWithWB(checkMem, enableReg))
    checker.io.instCommit.valid := io.valid
    checker.io.instCommit.inst  := io.inst
    checker.io.instCommit.pc    := state.pc
    checker.io.instCommit.npc   := trans.io.next.pc

    checker.io.wb := wb

    checker.io.privilege := state.privilege

    checker.io.mem.map(_ := trans.io.mem)
  }

  behavior of "CheckerWithWB"

  it should "pass RiscvTests without mem check" in {
    val tests = Seq(
      RiscvTests("rv64ui", "rv64ui-addi.hex")
    )
    tests.foreach { testFile =>
      test(new CoreTester(new TestCore(false), testFile.getCanonicalPath())) { c =>
        RiscvTests.stepTest(c, RiscvTests.maxStep)
        RiscvTests.checkReturn(c)
      }
    }
  }

  val tests =
    Seq("rv64ui", "rv64um", "rv64uc", "rv64uzba", "rv64uzbb", "rv64uzbc", "rv64uzbs", "rv64uzbkb", "rv64uzbkx")

  tests.foreach { testCase =>
    RiscvTests(testCase).foreach(f =>
      it should s"pass RiscvTests with mem check @${f.getName}" in {
        test(new CoreTester(new TestCore, f.getCanonicalPath())) { c =>
          RiscvTests.stepTest(c, RiscvTests.maxStep)
          RiscvTests.checkReturn(c)
        }
      }
    )
  }

  tests.foreach { testCase =>
    RiscvTests(testCase).foreach(f =>
      it should s"pass RiscvTests with reg delay @${f.getName}" in {
        test(new CoreTester(new TestCore(true, true), f.getCanonicalPath())) { c =>
          RiscvTests.stepTest(c, RiscvTests.maxStep)
          RiscvTests.checkReturn(c)
        }
      }
    )
  }

}

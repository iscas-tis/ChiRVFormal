package rvspeccore.checker

import chisel3._
import chiseltest._
import org.scalatest._
import org.scalatest.flatspec.AnyFlatSpec

import rvspeccore.core._
import rvspeccore.core.spec._
import rvspeccore.core.spec.instset._
import rvspeccore.core.spec.instset.csr._

class CheckerWithStateSpec extends AnyFlatSpec with ChiselScalatestTester {
  behavior of "CheckerWithState"

  class TestCore(enableReg: Boolean = false)(implicit val config: RVConfig) extends RiscvCore {
    val checker = Module(new CheckerWithState(enableReg, None))
    checker.io.instCommit.valid := RegNext(io.valid, false.B)
    checker.io.instCommit.excp  := RegNext(trans.io.commit.exception, false.B)
    checker.io.instCommit.inst  := RegNext(io.inst)
    checker.io.instCommit.pc    := RegNext(state.pc)
    checker.io.instCommit.npc   := DontCare
    // printf("[  DUT   ] Valid:%x PC: %x Inst: %x\n", checker.io.instCommit.valid, checker.io.instCommit.pc, checker.io.instCommit.inst)
    checker.io.state := state

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

  it should "pass RiscvTests[mem check: off, reg delay: off]" in {
    val tests = Seq(
      RiscvTests("rv64ui", "rv64ui-addi.hex")
    )
    implicit val config = RVConfig(
      XLEN = 64,
      functions = Seq("Privileged")
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
      it should s"pass RiscvTests[mem check: on, reg delay: off] @${f.getName}" in {
        implicit val config = RVConfig(
          XLEN = 64,
          extensions = "MCZifenceiZicsrZbaZbbZbcZbsZbkbZbkcZbkx",
          functions = Seq("Privileged"),
          formal = Seq("CheckMem")
        )
        test(new CoreTester(new TestCore(false), f.getCanonicalPath())) { c =>
          RiscvTests.stepTest(c, RiscvTests.maxStep)
          RiscvTests.checkReturn(c)
        }
      }
    )
  }

  tests.foreach { testCase =>
    RiscvTests(testCase).foreach(f =>
      it should s"pass RiscvTests[mem check: on, reg delay: on] @${f.getName}" in {
        implicit val config = RVConfig(
          XLEN = 64,
          extensions = "MCZifenceiZicsrZbaZbbZbcZbsZbkbZbkcZbkx",
          functions = Seq("Privileged"),
          formal = Seq("CheckMem")
        )
        test(new CoreTester(new TestCore(true), f.getCanonicalPath())) { c =>
          RiscvTests.stepTest(c, RiscvTests.maxStep)
          RiscvTests.checkReturn(c)
        }
      }
    )
  }
}

// We have to extract some signals from RiscvCore, but it certainly modify the structure of the RiscvCore
// This can't be solved until we discuss with YiCheng about it.
class CheckerWithActionSpec extends AnyFlatSpec with ChiselScalatestTester {
  behavior of "CheckerWithAction"

  class TestCore(enableReg: Boolean = false)(implicit val config: RVConfig) extends RiscvCore {
    val writeback = Wire(WriteBack())

    writeback := 0.U.asTypeOf(WriteBack())

    writeback.rs1Addr  := trans.io.commit.rs1Addr
    writeback.rs2Addr  := trans.io.commit.rs2Addr
    writeback.rs1Data  := state.reg(writeback.rs1Addr)
    writeback.rs2Data  := state.reg(writeback.rs2Addr)
    writeback.rdAddr   := trans.io.commit.rdAddr
    writeback.rdData   := trans.io.commit.rdData
    writeback.csrWr    := trans.io.commit.csrWr
    writeback.csrAddr  := trans.io.commit.csrAddr
    writeback.csrNdata := trans.io.commit.csrNdata

    val checker = Module(new CheckerWithAction(enableReg))
    checker.io.instCommit.valid := io.valid
    checker.io.instCommit.excp  := trans.io.commit.exception
    checker.io.instCommit.inst  := io.inst
    checker.io.instCommit.pc    := state.pc
    checker.io.instCommit.npc   := trans.io.next.pc

    checker.io.csrUpdates.foreach { updates =>
      updates(0).valid := trans.io.commit.csrWr
      updates(0).addr := trans.io.commit.csrAddr
      updates(0).data := trans.io.commit.csrNdata
    }
    checker.io.writeback := writeback

    checker.io.privilege := state.privilege

    checker.io.mem.map(_ := trans.io.mem)
  }

  it should "pass RiscvTests[mem check: off, reg delay: off]" in {
    val tests = Seq(
      RiscvTests("rv64ui", "rv64ui-addi.hex")
    )
    implicit val config = RVConfig(
      XLEN = 64,
      functions = Seq("Privileged")
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
      it should s"pass RiscvTests[mem check: on, reg delay: off] @${f.getName}" in {
        implicit val config = RVConfig(
          XLEN = 64,
          extensions = "MCZifenceiZicsrZbaZbbZbcZbsZbkbZbkcZbkx",
          functions = Seq("Privileged"),
          formal = Seq("CheckMem")
        )
        test(new CoreTester(new TestCore(false), f.getCanonicalPath())).withAnnotations(Seq(WriteVcdAnnotation)) { c =>
          RiscvTests.stepTest(c, RiscvTests.maxStep)
          RiscvTests.checkReturn(c)
        }
      }
    )
  }

  tests.foreach { testCase =>
    RiscvTests(testCase).foreach(f =>
      it should s"pass RiscvTests[mem check: on, reg delay: on] @${f.getName}" in {
        implicit val config = RVConfig(
          XLEN = 64,
          extensions = "MCZifenceiZicsrZbaZbbZbcZbsZbkbZbkcZbkx",
          functions = Seq("Privileged"),
          formal = Seq("CheckMem")
        )
        test(new CoreTester(new TestCore(true), f.getCanonicalPath())) { c =>
          RiscvTests.stepTest(c, RiscvTests.maxStep)
          RiscvTests.checkReturn(c)
        }
      }
    )
  }

}

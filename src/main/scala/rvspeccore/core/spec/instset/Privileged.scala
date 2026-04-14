package rvspeccore.core.spec.instset

import chisel3._
import chisel3.util._

import rvspeccore.core.BaseCore
import rvspeccore.core.RVConfig
import rvspeccore.core.spec._
import rvspeccore.core.tool.BitTool._
import csr._

/** Privileged Instructions
  *
  *   - riscv-privileged-20211203
  *   - Chapter 9: RISC-V Privileged Instruction Set Listings
  *     - Table 9.1: RISC-V Privileged Instructions
  */
trait PrivilegedInsts {
  // - Trap-Return Instructions
  val SRET = Inst("SRET", "b0001000_00010_00000_000_00000_1110011")
  val MRET = Inst("MRET", "b0011000_00010_00000_000_00000_1110011")
  // - Interrupt-Management Instructions
  val WFI = Inst("WFI", "b0001000_00101_00000_000_00000_1110011")
  // - Supervisor Memory-Management Instructions
  val SFANCE_VMA      = Inst("SFANCE.VMA", "b0001001_?????_?????_000_00000_1110011")
  val SINVAL_VMA      = Inst("SINVAL.VMA", "b0001011_?????_?????_000_00000_1110011")      // not support yet
  val SFANCE_W_INVAL  = Inst("SFANCE.W.INVAL", "b0001100_00000_00000_000_00000_1110011")  // not support yet
  val SFANCE_INVAL_IR = Inst("SFANCE.INVAL.IR", "b0001100_00001_00000_000_00000_1110011") // not support yet
  // - Hypervisor Memory-Management Instructions
  val HFANCE_VVMA = Inst("HFANCE.VVMA", "b0010001_?????_?????_000_00000_1110011") // not support yet
  val HFANCE_GVMA = Inst("HFANCE.GVMA", "b0110001_?????_?????_000_00000_1110011") // not support yet
  val HINVAL_VVMA = Inst("HINVAL.VVMA", "b0010011_?????_?????_000_00000_1110011") // not support yet
  val HINVAL_GVMA = Inst("HINVAL.GVMA", "b0110011_?????_?????_000_00000_1110011") // not support yet
  // - Hypervisor Virtual-Machine Load and Store Instructions
  // ...
  // - Hypervisor Virtual-Machine Load and Store Instructions, RV64 only
  // ...

  val rvprivilegedInsts = Seq(SRET, MRET, WFI, SFANCE_VMA)
}

/** “Privileged” Instruction-Fetch Fence Volume II Insts
  */
trait PrivilegedExtension
    extends BaseCore
    with CommonDecode
    with PrivilegedInsts
    with CSRSupport
    with ExceptionSupport { this: IBase =>
  def doRVPrivileged: Unit = {
    val privilegedInsts = Seq(SRET, MRET, WFI, SFANCE_VMA)

    privilegedInsts.map(privilegedInst => when(privilegedInst(inst)) { doPrivileged(privilegedInst) })
  }

  def doPrivileged(singleInst: Inst): Unit = {
    singleInst match {
      // FIXME: need to decode more insts & clearify there actions(not do nothing....)
      case SRET       => decodeI; Sret(); /* then do nothing for now */
      case MRET       => decodeI; Mret(); /* then do nothing for now */
      case WFI        => decodeI;         /* then do nothing for now */
      case SFANCE_VMA => decodeI;         /* then do nothing for now */
      case _          =>
    }
  }
}

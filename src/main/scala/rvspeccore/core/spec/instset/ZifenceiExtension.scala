package rvspeccore.core.spec.instset

import chisel3._
import chisel3.util._

import rvspeccore.core.BaseCore
import rvspeccore.core.spec._
import rvspeccore.core.tool.BitTool._

/** “Zifencei” Instruction-Fetch Fence Instructions
  *
  *   - riscv-spec-20191213
  *   - Chapter 24: RV32/64G Instruction Set Listings
  *     - Table 24.2: Instruction listing for RISC-V
  */
trait ZifenceiExtensionInsts {
  // - RV32/RV64 Zifencei Standard Extension
  val FENCE_I = Inst("b????????????_?????_001_?????_0001111")
}

/** “Zifencei” Instruction-Fetch Fence
  *
  *   - riscv-spec-20191213
  *   - Chapter 3: “Zifencei” Instruction-Fetch Fence, Version 2.0
  */
trait ZifenceiExtension extends BaseCore with CommonDecode with ZifenceiExtensionInsts { this: IBase =>

  def doZifenceiExecute(singleInst: Inst): Unit = {
    singleInst match {
      case FENCE_I => decodeI; /* then do nothing for now */
      case _       =>
    }
  }

  def doRVZifencei: Unit = {
    val rvzifenceiInsts = Seq(FENCE_I)
    rvzifenceiInsts.map { rvzifenceiInst => when(rvzifenceiInst(inst)) { doZifenceiExecute(rvzifenceiInst) } }
  }

}

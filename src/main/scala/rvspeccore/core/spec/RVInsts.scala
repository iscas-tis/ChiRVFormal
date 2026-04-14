package rvspeccore.core.spec

import chisel3._
import chisel3.util._

import instset._

case class Inst(
    mnemonic: String,
    bitPat: Option[BitPat],
    checker: Option[(UInt, Int) => Bool]
) {
  def check(inst: UInt)(implicit XLEN: Int): Bool = {
    (bitPat, checker) match {
      case (Some(x), Some(y)) => inst === x && y(inst, XLEN)
      case (Some(x), None)    => inst === x
      case (None, Some(y))    => y(inst, XLEN)
      case (None, None)       => throw new Exception("bitPat or checker not defined")
    }
  }

  def apply(inst: UInt)(implicit XLEN: Int): Bool = check(inst)
}

object Inst {
  def apply(mnemonic: String, bits: String)                 = new Inst(mnemonic, Some(BitPat(bits)), None)
  def apply(mnemonic: String, checker: (UInt, Int) => Bool) = new Inst(mnemonic, None, Some(checker))
  def apply(mnemonic: String, bits: String, checker: (UInt, Int) => Bool) =
    new Inst(mnemonic, Some(BitPat(bits)), Some(checker))

  def apply(mnemonic: String, bitsPair0: (Int, String), bitsPairN: (Int, String)*) = new Inst(
    mnemonic,
    None,
    Some((inst: UInt, XLEN: Int) => {
      val bitsMap = bitsPair0 +: bitsPairN
      inst === BitPat(
        bitsMap
          .filter(_._1 == XLEN)
          .headOption
          .getOrElse(throw new Exception(s"XLEN `$XLEN` not matched"))
          ._2
      )
    })
  )
}

trait GSetInsts extends IBaseInsts with MExtensionInsts with ZicsrExtensionInsts with ZifenceiExtensionInsts

trait RVInsts extends GSetInsts with CExtensionInsts with BExtensionInsts with PrivilegedInsts

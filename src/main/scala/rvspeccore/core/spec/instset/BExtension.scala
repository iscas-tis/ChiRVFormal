package rvspeccore.core.spec.instset

import chisel3._
import chisel3.util._
import rvspeccore.core.BaseCore
import rvspeccore.core.spec._
import rvspeccore.core.tool.BitTool._
import rvspeccore.core.tool.CheckTool

/** "B" Extension for Bit Manipulation, Version 1.0.0
  *
  *   - riscv-spec-20240411
  *   - Chapter 28: "B" Extension for Bit Manipulation, Version 1.0.0
  *   - 28.5. Instructions (in alphabetical order)
  */
trait BExtensionInsts {
  val ADD_UW = Inst("ADD.UW", "b0000100_?????_?????_000_?????_0111011")
  val ANDN   = Inst("ANDN", "b0100000_?????_?????_111_?????_0110011")
  val BCLR   = Inst("BCLR", "b0100100_?????_?????_001_?????_0110011")
  val BCLRI = Inst(
    "BCLRI",
    32 -> "b0100100_?????_?????_001_?????_0010011",
    64 -> "b010010_??????_?????_001_?????_0010011"
  )
  val BEXT = Inst("BEXT", "b0100100_?????_?????_101_?????_0110011")
  val BEXTI = Inst(
    "BEXTI",
    32 -> "b0100100_?????_?????_101_?????_0010011",
    64 -> "b010010_??????_?????_101_?????_0010011"
  )
  val BINV = Inst("BINV", "b0110100_?????_?????_001_?????_0110011")
  val BINVI = Inst(
    "BINVI",
    32 -> "b0110100_?????_?????_001_?????_0010011",
    64 -> "b011010_??????_?????_001_?????_0010011"
  )
  val BSET = Inst("BSET", "b0010100_?????_?????_001_?????_0110011")
  val BSETI = Inst(
    "BSETI",
    32 -> "b0010100_?????_?????_001_?????_0010011",
    64 -> "b001010_??????_?????_001_?????_0010011"
  )
  val CLMUL  = Inst("CLMUL", "b0000101_?????_?????_001_?????_0110011")
  val CLMULH = Inst("CLMULH", "b0000101_?????_?????_011_?????_0110011")
  val CLMULR = Inst("CLMULR", "b0000101_?????_?????_010_?????_0110011")
  val CLZ    = Inst("CLZ", "b0110000_00000_?????_001_?????_0010011")
  val CLZW   = Inst("CLZW", "b0110000_00000_?????_001_?????_0011011")
  val CPOP   = Inst("CPOP", "b0110000_00010_?????_001_?????_0010011")
  val CPOPW  = Inst("CPOPW", "b0110000_00010_?????_001_?????_0011011")
  val CTZ    = Inst("CTZ", "b0110000_00001_?????_001_?????_0010011")
  val CTZW   = Inst("CTZW", "b0110000_00001_?????_001_?????_0011011")
  val MAX    = Inst("MAX", "b0000101_?????_?????_110_?????_0110011")
  val MAXU   = Inst("MAXU", "b0000101_?????_?????_111_?????_0110011")
  val MIN    = Inst("MIN", "b0000101_?????_?????_100_?????_0110011")
  val MINU   = Inst("MINU", "b0000101_?????_?????_101_?????_0110011")
  val ORC_B  = Inst("ORC.B", "b001010000111_?????_101_?????_0010011")
  val ORN    = Inst("ORN", "b0100000_?????_?????_110_?????_0110011")
  val PACK   = Inst("PACK", "b0000100_?????_?????_100_?????_0110011")
  val PACKH  = Inst("PACKH", "b0000100_?????_?????_111_?????_0110011")
  val PACKW  = Inst("PACKW", "b0000100_?????_?????_100_?????_0111011")
  val REV8 = Inst(
    "REV8",
    32 -> "b011010011000_?????_101_?????_0010011",
    64 -> "b011010111000_?????_101_?????_0010011"
  )
  val BREV8 = Inst("BREV8", "b011010000111_?????_101_?????_0010011")
  val ROL   = Inst("ROL", "b0110000_?????_?????_001_?????_0110011")
  val ROLW  = Inst("ROLW", "b0110000_?????_?????_001_?????_0111011")
  val ROR   = Inst("ROR", "b0110000_?????_?????_101_?????_0110011")
  val RORI = Inst(
    "RORI",
    32 -> "b0110000_?????_?????_101_?????_0010011",
    64 -> "b011000_??????_?????_101_?????_0010011"
  )
  val RORIW     = Inst("RORIW", "b0110000_?????_?????_101_?????_0011011")
  val RORW      = Inst("RORW", "b0110000_?????_?????_101_?????_0111011")
  val SEXT_B    = Inst("SEXT.B", "b0110000_00100_?????_001_?????_0010011")
  val SEXT_H    = Inst("SEXT.H", "b0110000_00101_?????_001_?????_0010011")
  val SH1ADD    = Inst("SH1ADD", "b0010000_?????_?????_010_?????_0110011")
  val SH1ADD_UW = Inst("SH1ADD.UW", "b0010000_?????_?????_010_?????_0111011")
  val SH2ADD    = Inst("SH2ADD", "b0010000_?????_?????_100_?????_0110011")
  val SH2ADD_UW = Inst("SH2ADD.UW", "b0010000_?????_?????_100_?????_0111011")
  val SH3ADD    = Inst("SH3ADD", "b0010000_?????_?????_110_?????_0110011")
  val SH3ADD_UW = Inst("SH3ADD.UW", "b0010000_?????_?????_110_?????_0111011")
  val SLLI_UW   = Inst("SLLI.UW", "b000010_??????_?????_001_?????_0011011")
  val UNZIP     = Inst("UNZIP", "b0000100_01111_?????_101_?????_0010011")
  val XNOR      = Inst("XNOR", "b0100000_?????_?????_100_?????_0110011")
  val XPERM8    = Inst("XPERM8", "b0010100_?????_?????_100_?????_0110011")
  val XPERM4    = Inst("XPERM4", "b0010100_?????_?????_010_?????_0110011")
  val ZEXT_H = Inst(
    "ZEXT.H",
    32 -> "b0000100_00000_?????_100_?????_0110011",
    64 -> "b0000100_00000_?????_100_?????_0111011"
  )
  val ZIP = Inst("ZIP", "b0000100_01111_?????_001_?????_0010011")

  val rv32zbaInsts      = Seq(SH1ADD, SH2ADD, SH3ADD)
  val rv32zbkb_zbbInsts = Seq(ANDN, ORN, XNOR, ROL, ROR, RORI, REV8)
  val rv32zbbInsts      = rv32zbkb_zbbInsts ++ Seq(CLZ, CTZ, CPOP, MAX, MAXU, MIN, MINU, SEXT_B, SEXT_H, ZEXT_H, ORC_B)
  val rv32zbkc_zbcInsts = Seq(CLMUL, CLMULH)
  val rv32zbcInsts      = rv32zbkc_zbcInsts ++ Seq(CLMULR)
  val rv32zbsInsts      = Seq(BCLR, BCLRI, BEXT, BEXTI, BINV, BINVI, BSET, BSETI)
  val rv32zbkbInsts     = rv32zbkb_zbbInsts ++ Seq(PACK, PACKH, BREV8, ZIP, UNZIP)
  val rv32zbkcInsts     = rv32zbkc_zbcInsts ++ Seq(XPERM8, XPERM4)
  val rv32zbkxInsts     = Seq(XPERM8, XPERM4)

  val rv64zbaInsts      = rv32zbaInsts ++ Seq(ADD_UW, SH1ADD_UW, SH2ADD_UW, SH3ADD_UW, SLLI_UW)
  val rv64zbkb_zbbInsts = Seq(ROLW, RORW, RORIW)
  val rv64zbbInsts      = rv32zbbInsts ++ rv64zbkb_zbbInsts ++ Seq(CLZW, CTZW, CPOPW)
  val rv64zbcInsts      = rv32zbcInsts
  val rv64zbsInsts      = rv32zbsInsts
  val rv64zbkbInsts     = rv32zbkbInsts ++ rv64zbkb_zbbInsts ++ Seq(PACKW)
  val rv64zbkcInsts     = rv32zbkcInsts
  val rv64zbkxInsts     = rv32zbkxInsts
}

/** "B" Extension for Bit Manipulation, Version 1.0.0
  *
  *   - riscv-spec-20240411
  *   - Chapter 28: "B" Extension for Bit Manipulation, Version 1.0.0
  *   - 28.4. Extensions
  */
trait BExtension extends BaseCore with CommonDecode with BExtensionInsts with CheckTool { this: IBase =>

  /** Function to select the appropriate bit width based on XLEN */
  def getRotationShamt(value: UInt, xlen: Int): UInt = {
    value(if (xlen == 32) 4 else 5, 0).asUInt
  }

  def xperm8_lookup(idx: UInt, lut: UInt): UInt = {
    val shiftAmt = Cat(idx, 0.U(3.W))
    ((lut >> shiftAmt)(7, 0)).asUInt
  }

  def xperm4_lookup(idx: UInt, lut: UInt): UInt = {
    val shiftAmt = Cat(idx, 0.U(2.W))
    ((lut >> shiftAmt)(3, 0)).asUInt
  }

  def doBExtension(singleInst: Inst): Unit = {
    singleInst match {
      // doRV32B
      // doRV32Zba
      case SH1ADD => decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (getSrc1Reg(rs1) << 1))
      case SH2ADD => decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (getSrc1Reg(rs1) << 2))
      case SH3ADD => decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (getSrc1Reg(rs1) << 3))
      // doRV32Zbb
      case ANDN => decodeR; updateDestReg(rd, getSrc1Reg(rs1) & (~getSrc2Reg(rs2)))
      case ORN  => decodeR; updateDestReg(rd, getSrc1Reg(rs1) | (~getSrc2Reg(rs2)))
      case XNOR => decodeR; updateDestReg(rd, ~(getSrc1Reg(rs1) ^ getSrc2Reg(rs2)))
      case CLZ =>
        decodeI;
        updateDestReg(rd, Mux(getSrc1Reg(rs1) === 0.U, XLEN.U, PriorityEncoder(getSrc1Reg(rs1).asBools.reverse)))
      case CTZ =>
        decodeI; updateDestReg(rd, Mux(getSrc1Reg(rs1) === 0.U, XLEN.U, PriorityEncoder(getSrc1Reg(rs1).asBools)))
      case CPOP => decodeI; updateDestReg(rd, PopCount(getSrc1Reg(rs1)))
      case MAX =>
        decodeR;
        updateDestReg(rd, Mux(getSrc1Reg(rs1).asSInt < getSrc2Reg(rs2).asSInt, getSrc2Reg(rs2), getSrc1Reg(rs1)))
      case MAXU =>
        decodeR;
        updateDestReg(rd, Mux(getSrc1Reg(rs1).asUInt < getSrc2Reg(rs2).asUInt, getSrc2Reg(rs2), getSrc1Reg(rs1)))
      case MIN =>
        decodeR;
        updateDestReg(rd, Mux(getSrc1Reg(rs1).asSInt < getSrc2Reg(rs2).asSInt, getSrc1Reg(rs1), getSrc2Reg(rs2)))
      case MINU =>
        decodeR;
        updateDestReg(rd, Mux(getSrc1Reg(rs1).asUInt < getSrc2Reg(rs2).asUInt, getSrc1Reg(rs1), getSrc2Reg(rs2)))
      case SEXT_B => decodeI; updateDestReg(rd, signExt(getSrc1Reg(rs1)(7, 0), XLEN))
      case SEXT_H => decodeI; updateDestReg(rd, signExt(getSrc1Reg(rs1)(15, 0), XLEN))
      case ZEXT_H if config.XLEN == 32 =>
        decodeI; updateDestReg(rd, zeroExt(getSrc1Reg(rs1)(15, 0), XLEN))
      case ROL =>
        decodeR;
        updateDestReg(
          rd,
          (getSrc1Reg(rs1) << getRotationShamt(getSrc2Reg(rs2), XLEN)) |
            (getSrc1Reg(rs1) >> (XLEN.U - getRotationShamt(getSrc2Reg(rs2), XLEN)))
        )
      case ROR =>
        decodeR;
        updateDestReg(
          rd,
          (getSrc1Reg(rs1) >> getRotationShamt(getSrc2Reg(rs2), XLEN)) |
            (getSrc1Reg(rs1) << (XLEN.U - getRotationShamt(getSrc2Reg(rs2), XLEN)))
        )
      case RORI =>
        decodeI;
        updateDestReg(
          rd,
          (getSrc1Reg(rs1) >> getRotationShamt(imm, XLEN)) |
            (getSrc1Reg(rs1) << (XLEN.U - getRotationShamt(imm, XLEN)))
        )
      case ORC_B =>
        val byteResults = VecInit(Seq.fill(XLEN / 8)(0.U(8.W)))
        for (i <- 0 until XLEN by 8) {
          val byte = getSrc1Reg(rs1)(i + 7, i)
          byteResults(i / 8) := Mux(byte.orR, 0xff.U(8.W), 0x00.U(8.W))
        }
        decodeR; updateDestReg(rd, byteResults.asUInt)
      case REV8 if config.XLEN == 32 =>
        var result = 0.U(XLEN.W)
        var j      = XLEN - 8
        for (i <- 0 until XLEN by 8) {
          result = result | (getSrc1Reg(rs1)(j + 7, j) << i).asUInt
          j -= 8
        }
        decodeR; updateDestReg(rd, result)
      // doRV32Zbc
      case CLMUL =>
        decodeR;
        val partialResults = VecInit(Seq.fill(XLEN)(0.U(XLEN.W)))
        for (i <- 0 until XLEN) {
          when(((getSrc2Reg(rs2) >> i.U) & 1.U) > 0.U) {
            partialResults(i) := getSrc1Reg(rs1) << i
          }
        }
        updateDestReg(rd, partialResults.reduce(_ ^ _))
      case CLMULH =>
        decodeR;
        val partialResults = VecInit(Seq.fill(XLEN)(0.U(XLEN.W)))
        for (i <- 1 to XLEN) {
          when(((getSrc2Reg(rs2) >> i.U) & 1.U) > 0.U) {
            partialResults(i - 1) := getSrc1Reg(rs1) >> (XLEN - i)
          }
        }
        updateDestReg(rd, partialResults.reduce(_ ^ _))
      case CLMULR =>
        decodeR;
        val partialResults = VecInit(Seq.fill(XLEN)(0.U(XLEN.W)))
        for (i <- 0 until XLEN) {
          when(((getSrc2Reg(rs2) >> i.U) & 1.U) > 0.U) {
            partialResults(i) := getSrc1Reg(rs1) >> (XLEN - i - 1)
          }
        }
        updateDestReg(rd, partialResults.reduce(_ ^ _))
      // doRV32Zbs
      case BCLR =>
        decodeR; updateDestReg(rd, getSrc1Reg(rs1) & ~((1.U << getRotationShamt(getSrc2Reg(rs2), XLEN)).asUInt))
      case BCLRI => decodeI; updateDestReg(rd, getSrc1Reg(rs1) & ~((1.U << getRotationShamt(imm, XLEN)).asUInt))
      case BEXT  => decodeR; updateDestReg(rd, (getSrc1Reg(rs1) >> getRotationShamt(getSrc2Reg(rs2), XLEN)) & 1.U)
      case BEXTI => decodeI; updateDestReg(rd, (getSrc1Reg(rs1) >> getRotationShamt(imm, XLEN)) & 1.U)
      case BINV  => decodeR; updateDestReg(rd, getSrc1Reg(rs1) ^ (1.U << getRotationShamt(getSrc2Reg(rs2), XLEN)))
      case BINVI => decodeI; updateDestReg(rd, getSrc1Reg(rs1) ^ (1.U << getRotationShamt(imm, XLEN)))
      case BSET  => decodeR; updateDestReg(rd, getSrc1Reg(rs1) | (1.U << getRotationShamt(getSrc2Reg(rs2), XLEN)))
      case BSETI => decodeI; updateDestReg(rd, getSrc1Reg(rs1) | (1.U << getRotationShamt(imm, XLEN)))
      // doRV32Zbkb
      case PACK =>
        decodeR;
        updateDestReg(rd, getSrc2Reg(rs2)(((XLEN >> 1) - 1), 0) << (XLEN / 2) | getSrc1Reg(rs1)(((XLEN >> 1) - 1), 0))
      case PACKH => decodeR; updateDestReg(rd, zeroExt((getSrc2Reg(rs2)(7, 0) << 8) | getSrc1Reg(rs1)(7, 0), XLEN))
      case BREV8 =>
        decodeR;
        var result = 0.U(XLEN.W)
        for (i <- 0 until XLEN by 8) {
          val swapped = Reverse(getSrc1Reg(rs1)(i + 7, i))
          result = (result | (swapped << i)).asUInt
        }
        updateDestReg(rd, result)
      case ZIP if config.XLEN == 32 =>
        decodeR;
        var result = 0.U(XLEN.W)
        for (i <- 0 until XLEN / 2) {
          val lower = getSrc1Reg(rs1)(i)            // 低 halfSize 位的第 i 位
          val upper = getSrc1Reg(rs1)(i + XLEN / 2) // 高 halfSize 位的第 i 位
          result = (result | (upper << ((i << 1) + 1)) | (lower << (i << 1))).asUInt
        }
        updateDestReg(rd, result)
      case UNZIP if config.XLEN == 32 =>
        decodeR;
        var result = 0.U(XLEN.W)
        for (i <- 0 until XLEN / 2) {
          val lower = getSrc1Reg(rs1)(i << 1)
          val upper = getSrc1Reg(rs1)((i << 1) + 1)
          result = (result | (upper << (i + XLEN / 2)) | (lower << i)).asUInt
        }
        updateDestReg(rd, result)
      // doRV32Zbkx
      case XPERM8 =>
        decodeR;
        var result = 0.U(XLEN.W)
        for (i <- 0 until XLEN by 8) {
          val index    = getSrc2Reg(rs2)(i + 7, i)
          val bitValue = xperm8_lookup(index, getSrc1Reg(rs1))
          result = (result | (bitValue << i)).asUInt
        }
        updateDestReg(rd, result)
      case XPERM4 =>
        decodeR;
        var result = 0.U(XLEN.W)
        for (i <- 0 until XLEN by 4) {
          val index    = getSrc2Reg(rs2)(i + 3, i)
          val bitValue = xperm4_lookup(index, getSrc1Reg(rs1))
          result = (result | (bitValue << i)).asUInt
        }
        updateDestReg(rd, result)
      // doRV64B
      // doRV64Zba
      case ADD_UW if config.XLEN == 64 =>
        decodeR; updateDestReg(rd, getSrc2Reg(rs2) + zeroExt(getSrc1Reg(rs1)(31, 0), XLEN))
      case SH1ADD_UW if config.XLEN == 64 =>
        decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (zeroExt(getSrc1Reg(rs1)(31, 0), XLEN) << 1))
      case SH2ADD_UW if config.XLEN == 64 =>
        decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (zeroExt(getSrc1Reg(rs1)(31, 0), XLEN) << 2))
      case SH3ADD_UW if config.XLEN == 64 =>
        decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (zeroExt(getSrc1Reg(rs1)(31, 0), XLEN) << 3))
      case SLLI_UW if config.XLEN == 64 =>
        decodeI; updateDestReg(rd, zeroExt(getSrc1Reg(rs1)(31, 0), XLEN) << imm(5, 0))
      // doRV64Zbb
      case CLZW if config.XLEN == 64 =>
        decodeI;
        updateDestReg(rd, Mux(getSrc1Reg(rs1) === 0.U, 32.U, PriorityEncoder(getSrc1Reg(rs1)(31, 0).asBools.reverse)))
      case CTZW if config.XLEN == 64 =>
        decodeI; updateDestReg(rd, Mux(getSrc1Reg(rs1) === 0.U, 32.U, PriorityEncoder(getSrc1Reg(rs1)(31, 0).asBools)))
      case CPOPW if config.XLEN == 64 =>
        decodeI; updateDestReg(rd, PopCount(getSrc1Reg(rs1)(31, 0)))
      case ZEXT_H if config.XLEN == 64 =>
        decodeI; updateDestReg(rd, zeroExt(getSrc1Reg(rs1)(15, 0), XLEN))
      case ROLW if config.XLEN == 64 =>
        decodeR
        val rs1_data = zeroExt(getSrc1Reg(rs1)(31, 0), XLEN)
        val result = ((rs1_data << getSrc2Reg(rs2)(4, 0)).asUInt | (rs1_data >> (32.U - getSrc2Reg(rs2)(4, 0))).asUInt)
        updateDestReg(rd, signExt(result(31, 0), XLEN))
      case RORIW if config.XLEN == 64 =>
        decodeI
        val rs1_data = zeroExt(getSrc1Reg(rs1)(31, 0), XLEN)
        val result   = (rs1_data >> imm(4, 0)).asUInt | (rs1_data << (32.U - imm(4, 0))).asUInt
        updateDestReg(rd, signExt(result(31, 0), XLEN))
      case RORW if config.XLEN == 64 =>
        decodeR
        val rs1_data = zeroExt(getSrc1Reg(rs1)(31, 0), XLEN)
        val result   = (rs1_data >> getSrc2Reg(rs2)(4, 0)).asUInt | (rs1_data << (32.U - getSrc2Reg(rs2)(4, 0))).asUInt
        updateDestReg(rd, signExt(result(31, 0), XLEN))
      case REV8 if config.XLEN == 64 =>
        decodeR
        var result = 0.U(XLEN.W)
        var j      = XLEN - 8
        for (i <- 0 until XLEN by 8) {
          result = result | (getSrc1Reg(rs1)(j + 7, j) << i).asUInt
          j -= 8
        }
        updateDestReg(rd, result)
      // doRV64Zbkb
      case PACKW if config.XLEN == 64 =>
        decodeR; updateDestReg(rd, signExt((getSrc2Reg(rs2)(15, 0) << 16) | getSrc1Reg(rs1)(15, 0), XLEN))
      case _ =>
    }
  }

  def doRVB(): Unit = {
    val rv32zbInsts = Seq(
      (config.extensions.Zba, rv32zbaInsts),
      (config.extensions.Zbb, rv32zbbInsts),
      (config.extensions.Zbc, rv32zbcInsts),
      (config.extensions.Zbs, rv32zbsInsts),
      (config.extensions.Zbkb, rv32zbkbInsts),
      (config.extensions.Zbkc, rv32zbkcInsts),
      (config.extensions.Zbkx, rv32zbkxInsts)
    ).collect { case (true, insts) => insts.toSeq }.foldLeft(Set.empty[Inst])(_ ++ _)
    val rv64zbInsts = Seq(
      (config.extensions.Zba, rv64zbaInsts),
      (config.extensions.Zbb, rv64zbbInsts),
      (config.extensions.Zbc, rv64zbcInsts),
      (config.extensions.Zbs, rv64zbsInsts),
      (config.extensions.Zbkb, rv64zbkbInsts),
      (config.extensions.Zbkc, rv64zbkcInsts),
      (config.extensions.Zbkx, rv64zbkxInsts)
    ).collect { case (true, insts) => insts.toSeq }.foldLeft(Set.empty[Inst])(_ ++ _)

    config.XLEN match {
      case 32 => rv32zbInsts.map { rv32zbInst => when(rv32zbInst(inst)) { doBExtension(rv32zbInst) } }
      case 64 => rv64zbInsts.map { rv64zbInst => when(rv64zbInst(inst)) { doBExtension(rv64zbInst) } }
    }
  }

}

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
  val add_uw = Inst("b0000100_?????_?????_000_?????_0111011")
  val andn   = Inst("b0100000_?????_?????_111_?????_0110011")
  val bclr   = Inst("b0100100_?????_?????_001_?????_0110011")
  val bclri = Inst(
    32 -> "b0100100_?????_?????_001_?????_0010011",
    64 -> "b010010_??????_?????_001_?????_0010011"
  )
  val bext = Inst("b0100100_?????_?????_101_?????_0110011")
  val bexti = Inst(
    32 -> "b0100100_?????_?????_101_?????_0010011",
    64 -> "b010010_??????_?????_101_?????_0010011"
  )
  val binv = Inst("b0110100_?????_?????_001_?????_0110011")
  val binvi = Inst(
    32 -> "b0110100_?????_?????_001_?????_0010011",
    64 -> "b011010_??????_?????_001_?????_0010011"
  )
  val bset = Inst("b0010100_?????_?????_001_?????_0110011")
  val bseti = Inst(
    32 -> "b0010100_?????_?????_001_?????_0010011",
    64 -> "b001010_??????_?????_001_?????_0010011"
  )
  val clmul  = Inst("b0000101_?????_?????_001_?????_0110011")
  val clmulh = Inst("b0000101_?????_?????_011_?????_0110011")
  val clmulr = Inst("b0000101_?????_?????_010_?????_0110011")
  val clz    = Inst("b0110000_00000_?????_001_?????_0010011")
  val clzw   = Inst("b0110000_00000_?????_001_?????_0011011")
  val cpop   = Inst("b0110000_00010_?????_001_?????_0010011")
  val cpopw  = Inst("b0110000_00010_?????_001_?????_0011011")
  val ctz    = Inst("b0110000_00001_?????_001_?????_0010011")
  val ctzw   = Inst("b0110000_00001_?????_001_?????_0011011")
  val max    = Inst("b0000101_?????_?????_110_?????_0110011")
  val maxu   = Inst("b0000101_?????_?????_111_?????_0110011")
  val min    = Inst("b0000101_?????_?????_100_?????_0110011")
  val minu   = Inst("b0000101_?????_?????_101_?????_0110011")
  val orc_b  = Inst("b001010000111_?????_101_?????_0010011")
  val orn    = Inst("b0100000_?????_?????_110_?????_0110011")
  val pack   = Inst("b0000100_?????_?????_100_?????_0110011")
  val packh  = Inst("b0000100_?????_?????_111_?????_0110011")
  val packw  = Inst("b0000100_?????_?????_100_?????_0111011")
  val rev8 = Inst(
    32 -> "b011010011000_?????_101_?????_0010011",
    64 -> "b011010111000_?????_101_?????_0010011"
  )
  val brev8 = Inst("b011010000111_?????_101_?????_0010011")
  val rol   = Inst("b0110000_?????_?????_001_?????_0110011")
  val rolw  = Inst("b0110000_?????_?????_001_?????_0111011")
  val ror   = Inst("b0110000_?????_?????_101_?????_0110011")
  val rori = Inst(
    32 -> "b0110000_?????_?????_101_?????_0010011",
    64 -> "b011000_??????_?????_101_?????_0010011"
  )
  val roriw     = Inst("b0110000_?????_?????_101_?????_0011011")
  val rorw      = Inst("b0110000_?????_?????_101_?????_0111011")
  val sext_b    = Inst("b0110000_00100_?????_001_?????_0010011")
  val sext_h    = Inst("b0110000_00101_?????_001_?????_0010011")
  val sh1add    = Inst("b0010000_?????_?????_010_?????_0110011")
  val sh1add_uw = Inst("b0010000_?????_?????_010_?????_0111011")
  val sh2add    = Inst("b0010000_?????_?????_100_?????_0110011")
  val sh2add_uw = Inst("b0010000_?????_?????_100_?????_0111011")
  val sh3add    = Inst("b0010000_?????_?????_110_?????_0110011")
  val sh3add_uw = Inst("b0010000_?????_?????_110_?????_0111011")
  val slli_uw   = Inst("b000010_??????_?????_001_?????_0011011")
  val unzip     = Inst("b0000100_01111_?????_101_?????_0010011")
  val xnor      = Inst("b0100000_?????_?????_100_?????_0110011")
  val xperm8    = Inst("b0010100_?????_?????_100_?????_0110011")
  val xperm4    = Inst("b0010100_?????_?????_010_?????_0110011")
  val zext_h = Inst(
    32 -> "b0000100_00000_?????_100_?????_0110011",
    64 -> "b0000100_00000_?????_100_?????_0111011"
  )
  val zip = Inst("b0000100_01111_?????_001_?????_0010011")
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
      case `sh1add` => decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (getSrc1Reg(rs1) << 1))
      case `sh2add` => decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (getSrc1Reg(rs1) << 2))
      case `sh3add` => decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (getSrc1Reg(rs1) << 3))
      // doRV32Zbb
      case `andn` => decodeR; updateDestReg(rd, getSrc1Reg(rs1) & (~getSrc2Reg(rs2)))
      case `orn`  => decodeR; updateDestReg(rd, getSrc1Reg(rs1) | (~getSrc2Reg(rs2)))
      case `xnor` => decodeR; updateDestReg(rd, ~(getSrc1Reg(rs1) ^ getSrc2Reg(rs2)))
      case `clz` =>
        decodeI;
        updateDestReg(rd, Mux(getSrc1Reg(rs1) === 0.U, XLEN.U, PriorityEncoder(getSrc1Reg(rs1).asBools.reverse)))
      case `ctz` =>
        decodeI; updateDestReg(rd, Mux(getSrc1Reg(rs1) === 0.U, XLEN.U, PriorityEncoder(getSrc1Reg(rs1).asBools)))
      case `cpop` => decodeI; updateDestReg(rd, PopCount(getSrc1Reg(rs1)))
      case `max` =>
        decodeR;
        updateDestReg(rd, Mux(getSrc1Reg(rs1).asSInt < getSrc2Reg(rs2).asSInt, getSrc2Reg(rs2), getSrc1Reg(rs1)))
      case `maxu` =>
        decodeR;
        updateDestReg(rd, Mux(getSrc1Reg(rs1).asUInt < getSrc2Reg(rs2).asUInt, getSrc2Reg(rs2), getSrc1Reg(rs1)))
      case `min` =>
        decodeR;
        updateDestReg(rd, Mux(getSrc1Reg(rs1).asSInt < getSrc2Reg(rs2).asSInt, getSrc1Reg(rs1), getSrc2Reg(rs2)))
      case `minu` =>
        decodeR;
        updateDestReg(rd, Mux(getSrc1Reg(rs1).asUInt < getSrc2Reg(rs2).asUInt, getSrc1Reg(rs1), getSrc2Reg(rs2)))
      case `sext_b` => decodeI; updateDestReg(rd, signExt(getSrc1Reg(rs1)(7, 0), XLEN))
      case `sext_h` => decodeI; updateDestReg(rd, signExt(getSrc1Reg(rs1)(15, 0), XLEN))
      case `zext_h` if config.XLEN == 32 =>
        decodeI; updateDestReg(rd, zeroExt(getSrc1Reg(rs1)(15, 0), XLEN))
      case `rol` =>
        decodeR;
        updateDestReg(
          rd,
          (getSrc1Reg(rs1) << getRotationShamt(getSrc2Reg(rs2), XLEN)) |
            (getSrc1Reg(rs1) >> (XLEN.U - getRotationShamt(getSrc2Reg(rs2), XLEN)))
        )
      case `ror` =>
        decodeR;
        updateDestReg(
          rd,
          (getSrc1Reg(rs1) >> getRotationShamt(getSrc2Reg(rs2), XLEN)) |
            (getSrc1Reg(rs1) << (XLEN.U - getRotationShamt(getSrc2Reg(rs2), XLEN)))
        )
      case `rori` =>
        decodeI;
        updateDestReg(
          rd,
          (getSrc1Reg(rs1) >> getRotationShamt(imm, XLEN)) |
            (getSrc1Reg(rs1) << (XLEN.U - getRotationShamt(imm, XLEN)))
        )
      case `orc_b` =>
        val byteResults = VecInit(Seq.fill(XLEN / 8)(0.U(8.W)))
        for (i <- 0 until XLEN by 8) {
          val byte = getSrc1Reg(rs1)(i + 7, i)
          byteResults(i / 8) := Mux(byte.orR, 0xff.U(8.W), 0x00.U(8.W))
        }
        decodeR; updateDestReg(rd, byteResults.asUInt)
      case `rev8` if config.XLEN == 32 =>
        var result = 0.U(XLEN.W)
        var j      = XLEN - 8
        for (i <- 0 until XLEN by 8) {
          result = result | (getSrc1Reg(rs1)(j + 7, j) << i).asUInt
          j -= 8
        }
        decodeR; updateDestReg(rd, result)
      // doRV32Zbc
      case `clmul` =>
        decodeR;
        val partialResults = VecInit(Seq.fill(XLEN)(0.U(XLEN.W)))
        for (i <- 0 until XLEN) {
          when(((getSrc2Reg(rs2) >> i.U) & 1.U) > 0.U) {
            partialResults(i) := getSrc1Reg(rs1) << i
          }
        }
        updateDestReg(rd, partialResults.reduce(_ ^ _))
      case `clmulh` =>
        decodeR;
        val partialResults = VecInit(Seq.fill(XLEN)(0.U(XLEN.W)))
        for (i <- 1 to XLEN) {
          when(((getSrc2Reg(rs2) >> i.U) & 1.U) > 0.U) {
            partialResults(i - 1) := getSrc1Reg(rs1) >> (XLEN - i)
          }
        }
        updateDestReg(rd, partialResults.reduce(_ ^ _))
      case `clmulr` =>
        decodeR;
        val partialResults = VecInit(Seq.fill(XLEN)(0.U(XLEN.W)))
        for (i <- 0 until XLEN) {
          when(((getSrc2Reg(rs2) >> i.U) & 1.U) > 0.U) {
            partialResults(i) := getSrc1Reg(rs1) >> (XLEN - i - 1)
          }
        }
        updateDestReg(rd, partialResults.reduce(_ ^ _))
      // doRV32Zbs
      case `bclr` =>
        decodeR; updateDestReg(rd, getSrc1Reg(rs1) & ~((1.U << getRotationShamt(getSrc2Reg(rs2), XLEN)).asUInt))
      case `bclri` => decodeI; updateDestReg(rd, getSrc1Reg(rs1) & ~((1.U << getRotationShamt(imm, XLEN)).asUInt))
      case `bext`  => decodeR; updateDestReg(rd, (getSrc1Reg(rs1) >> getRotationShamt(getSrc2Reg(rs2), XLEN)) & 1.U)
      case `bexti` => decodeI; updateDestReg(rd, (getSrc1Reg(rs1) >> getRotationShamt(imm, XLEN)) & 1.U)
      case `binv`  => decodeR; updateDestReg(rd, getSrc1Reg(rs1) ^ (1.U << getRotationShamt(getSrc2Reg(rs2), XLEN)))
      case `binvi` => decodeI; updateDestReg(rd, getSrc1Reg(rs1) ^ (1.U << getRotationShamt(imm, XLEN)))
      case `bset`  => decodeR; updateDestReg(rd, getSrc1Reg(rs1) | (1.U << getRotationShamt(getSrc2Reg(rs2), XLEN)))
      case `bseti` => decodeI; updateDestReg(rd, getSrc1Reg(rs1) | (1.U << getRotationShamt(imm, XLEN)))
      // doRV32Zbkb
      case `pack` =>
        decodeR;
        updateDestReg(rd, getSrc2Reg(rs2)(((XLEN >> 1) - 1), 0) << (XLEN / 2) | getSrc1Reg(rs1)(((XLEN >> 1) - 1), 0))
      case `packh` => decodeR; updateDestReg(rd, zeroExt((getSrc2Reg(rs2)(7, 0) << 8) | getSrc1Reg(rs1)(7, 0), XLEN))
      case `brev8` =>
        decodeR;
        var result = 0.U(XLEN.W)
        for (i <- 0 until XLEN by 8) {
          val swapped = Reverse(getSrc1Reg(rs1)(i + 7, i))
          result = (result | (swapped << i)).asUInt
        }
        updateDestReg(rd, result)
      case `zip` if config.XLEN == 32 =>
        decodeR;
        var result = 0.U(XLEN.W)
        for (i <- 0 until XLEN / 2) {
          val lower = getSrc1Reg(rs1)(i)            // 低 halfSize 位的第 i 位
          val upper = getSrc1Reg(rs1)(i + XLEN / 2) // 高 halfSize 位的第 i 位
          result = (result | (upper << ((i << 1) + 1)) | (lower << (i << 1))).asUInt
        }
        updateDestReg(rd, result)
      case `unzip` if config.XLEN == 32 =>
        decodeR;
        var result = 0.U(XLEN.W)
        for (i <- 0 until XLEN / 2) {
          val lower = getSrc1Reg(rs1)(i << 1)
          val upper = getSrc1Reg(rs1)((i << 1) + 1)
          result = (result | (upper << (i + XLEN / 2)) | (lower << i)).asUInt
        }
        updateDestReg(rd, result)
      // doRV32Zbkx
      case `xperm8` =>
        decodeR;
        var result = 0.U(XLEN.W)
        for (i <- 0 until XLEN by 8) {
          val index    = getSrc2Reg(rs2)(i + 7, i)
          val bitValue = xperm8_lookup(index, getSrc1Reg(rs1))
          result = (result | (bitValue << i)).asUInt
        }
        updateDestReg(rd, result)
      case `xperm4` =>
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
      case `add_uw` if config.XLEN == 64 =>
        decodeR; updateDestReg(rd, getSrc2Reg(rs2) + zeroExt(getSrc1Reg(rs1)(31, 0), XLEN))
      case `sh1add_uw` if config.XLEN == 64 =>
        decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (zeroExt(getSrc1Reg(rs1)(31, 0), XLEN) << 1))
      case `sh2add_uw` if config.XLEN == 64 =>
        decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (zeroExt(getSrc1Reg(rs1)(31, 0), XLEN) << 2))
      case `sh3add_uw` if config.XLEN == 64 =>
        decodeR; updateDestReg(rd, getSrc2Reg(rs2) + (zeroExt(getSrc1Reg(rs1)(31, 0), XLEN) << 3))
      case `slli_uw` if config.XLEN == 64 =>
        decodeI; updateDestReg(rd, zeroExt(getSrc1Reg(rs1)(31, 0), XLEN) << imm(5, 0))
      // doRV64Zbb
      case `clzw` if config.XLEN == 64 =>
        decodeI;
        updateDestReg(rd, Mux(getSrc1Reg(rs1) === 0.U, 32.U, PriorityEncoder(getSrc1Reg(rs1)(31, 0).asBools.reverse)))
      case `ctzw` if config.XLEN == 64 =>
        decodeI; updateDestReg(rd, Mux(getSrc1Reg(rs1) === 0.U, 32.U, PriorityEncoder(getSrc1Reg(rs1)(31, 0).asBools)))
      case `cpopw` if config.XLEN == 64 =>
        decodeI; updateDestReg(rd, PopCount(getSrc1Reg(rs1)(31, 0)))
      case `zext_h` if config.XLEN == 64 =>
        decodeI; updateDestReg(rd, zeroExt(getSrc1Reg(rs1)(15, 0), XLEN))
      case `rolw` if config.XLEN == 64 =>
        decodeR
        val rs1_data = zeroExt(getSrc1Reg(rs1)(31, 0), XLEN)
        val result = ((rs1_data << getSrc2Reg(rs2)(4, 0)).asUInt | (rs1_data >> (32.U - getSrc2Reg(rs2)(4, 0))).asUInt)
        updateDestReg(rd, signExt(result(31, 0), XLEN))
      case `roriw` if config.XLEN == 64 =>
        decodeI
        val rs1_data = zeroExt(getSrc1Reg(rs1)(31, 0), XLEN)
        val result   = (rs1_data >> imm(4, 0)).asUInt | (rs1_data << (32.U - imm(4, 0))).asUInt
        updateDestReg(rd, signExt(result(31, 0), XLEN))
      case `rorw` if config.XLEN == 64 =>
        decodeR
        val rs1_data = zeroExt(getSrc1Reg(rs1)(31, 0), XLEN)
        val result   = (rs1_data >> getSrc2Reg(rs2)(4, 0)).asUInt | (rs1_data << (32.U - getSrc2Reg(rs2)(4, 0))).asUInt
        updateDestReg(rd, signExt(result(31, 0), XLEN))
      case `rev8` if config.XLEN == 64 =>
        decodeR
        var result = 0.U(XLEN.W)
        var j      = XLEN - 8
        for (i <- 0 until XLEN by 8) {
          result = result | (getSrc1Reg(rs1)(j + 7, j) << i).asUInt
          j -= 8
        }
        updateDestReg(rd, result)
      // doRV64Zbkb
      case `packw` if config.XLEN == 64 =>
        decodeR; updateDestReg(rd, signExt((getSrc2Reg(rs2)(15, 0) << 16) | getSrc1Reg(rs1)(15, 0), XLEN))
      case _ =>
    }
  }

  def doRVB(): Unit = {
    val rv32zbaInsts      = Seq(sh1add, sh2add, sh3add)
    val rv32zbkb_zbbInsts = Seq(andn, orn, xnor, rol, ror, rori, rev8)
    val rv32zbbInsts = rv32zbkb_zbbInsts ++ Seq(clz, ctz, cpop, max, maxu, min, minu, sext_b, sext_h, zext_h, orc_b)
    val rv32zbkc_zbcInsts = Seq(clmul, clmulh)
    val rv32zbcInsts      = rv32zbkc_zbcInsts ++ Seq(clmulr)
    val rv32zbsInsts      = Seq(bclr, bclri, bext, bexti, binv, binvi, bset, bseti)
    val rv32zbkbInsts     = rv32zbkb_zbbInsts ++ Seq(pack, packh, brev8, zip, unzip)
    val rv32zbkcInsts     = rv32zbkc_zbcInsts ++ Seq(xperm8, xperm4)
    val rv32zbksInsts     = Seq(xperm8, xperm4)

    val rv64zbaInsts      = rv32zbaInsts ++ Seq(add_uw, sh1add_uw, sh2add_uw, sh3add_uw, slli_uw)
    val rv64zbkb_zbbInsts = Seq(rolw, rorw, roriw)
    val rv64zbbInsts      = rv32zbbInsts ++ rv64zbkb_zbbInsts ++ Seq(clzw, ctzw, cpopw)
    val rv64zbcInsts      = rv32zbcInsts
    val rv64zbsInsts      = rv32zbsInsts
    val rv64zbkbInsts     = rv32zbkbInsts ++ rv64zbkb_zbbInsts ++ Seq(packw)
    val rv64zbkcInsts     = rv32zbkcInsts
    val rv64zbkxInsts     = rv32zbksInsts

    val rv32zbInsts = Seq(
      (config.extensions.Zba, rv32zbaInsts),
      (config.extensions.Zbb, rv32zbbInsts),
      (config.extensions.Zbc, rv32zbcInsts),
      (config.extensions.Zbs, rv32zbsInsts),
      (config.extensions.Zbkb, rv32zbkbInsts),
      (config.extensions.Zbkc, rv32zbkcInsts),
      (config.extensions.Zbkx, rv32zbksInsts)
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

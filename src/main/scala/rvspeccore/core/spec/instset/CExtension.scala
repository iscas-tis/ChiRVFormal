package rvspeccore.core.spec.instset

import chisel3._
import chisel3.util._

import rvspeccore.core.BaseCore
import rvspeccore.core.spec._
import rvspeccore.core.tool.BitTool._

trait CExtensionInsts {
  val rdNotZero    = (inst: UInt, xlen: Int) => { inst(11, 7) =/= 0.U }
  val nzimmNotZero = (inst: UInt, xlen: Int) => { Cat(inst(12), inst(6, 2)) =/= 0.U }
  val shamtCheck = (inst: UInt, xlen: Int) => {
    (xlen match {
      case 32 => inst(12) === 0.U
      case 64 => true.B
    }) && Cat(inst(12), inst(6, 2)) =/= 0.U
  }

  // scalafmt: { maxColumn = 200 }
  // 00
  val C_Illegal  = Inst("b????????????????_000_00000000_000_00")
  val C_ADDI4SPN = Inst("b????????????????_000_????????_???_00", (inst, xlen) => { inst(12, 5) =/= 0.U })

  val C_FLD = Inst("b????????????????_001_???_???_??_???_00")
  val C_LQ  = Inst("b????????????????_001_???_???_??_???_00")
  val C_LW  = Inst("b????????????????_010_???_???_??_???_00")
  val C_FLW = Inst("b????????????????_011_???_???_??_???_00")
  val C_LD  = Inst("b????????????????_011_???_???_??_???_00")
  // Reserved
  val C_FSD = Inst("b????????????????_101_???_???_??_???_00")
  val C_SQ  = Inst("b????????????????_101_???_???_??_???_00")
  val C_SW  = Inst("b????????????????_110_???_???_??_???_00")
  val C_FSW = Inst("b????????????????_111_???_???_??_???_00")
  val C_SD  = Inst("b????????????????_111_???_???_??_???_00")

  // 01
  val C_NOP      = Inst("b????????????????_000_?_00000_?????_01")
  val C_ADDI     = Inst("b????????????????_000_?_?????_?????_01", (inst, xlen) => { rdNotZero(inst, xlen) && nzimmNotZero(inst, xlen) })
  val C_JAL      = Inst("b????????????????_001_???????????_01", (inst, xlen) => (xlen == 32).B) // RV32 only
  val C_ADDIW    = Inst("b????????????????_001_?_?????_?????_01", rdNotZero)
  val C_LI       = Inst("b????????????????_010_?_?????_?????_01", rdNotZero)
  val C_ADDI16SP = Inst("b????????????????_011_?_00010_?????_01", nzimmNotZero)
  val C_LUI      = Inst("b????????????????_011_?_?????_?????_01", (inst, xlen) => { rdNotZero(inst, xlen) && inst(11, 7) =/= 2.U && nzimmNotZero(inst, xlen) })

  val C_SRLI   = Inst("b????????????????_100_?_00_???_?????_01", shamtCheck)
  val C_SRLI64 = Inst("b????????????????_100_0_00_???_00000_01")
  val C_SRAI   = Inst("b????????????????_100_?_01_???_?????_01", shamtCheck)
  val C_SAI64  = Inst("b????????????????_100_0_01_???_00000_01")
  val C_ANDI   = Inst("b????????????????_100_?_10_???_?????_01")

  val C_SUB  = Inst("b????????????????_100_0_11_???_00_???_01")
  val C_XOR  = Inst("b????????????????_100_0_11_???_01_???_01")
  val C_OR   = Inst("b????????????????_100_0_11_???_10_???_01")
  val C_AND  = Inst("b????????????????_100_0_11_???_11_???_01")
  val C_SUBW = Inst("b????????????????_100_1_11_???_00_???_01")
  val C_ADDW = Inst("b????????????????_100_1_11_???_01_???_01")
  // Reserved
  // Reserved
  val C_J    = Inst("b????????????????_101_???????????_01")
  val C_BEQZ = Inst("b????????????????_110_???_???_?????_01")
  val C_BNEZ = Inst("b????????????????_111_???_???_?????_01")

  // 10
  val C_SLLI   = Inst("b????????????????_000_?_?????_?????_10", (inst, xlen) => { rdNotZero(inst, xlen) && shamtCheck(inst, xlen) })
  val C_SLLI64 = Inst("b????????????????_000_0_?????_00000_10", rdNotZero)
  val C_FLDSP  = Inst("b????????????????_001_?_?????_?????_10")
  val C_LQSP   = Inst("b????????????????_001_?_?????_?????_10", rdNotZero)
  val C_LWSP   = Inst("b????????????????_010_?_?????_?????_10", rdNotZero)
  val C_FLWSP  = Inst("b????????????????_011_?_?????_?????_10")
  val C_LDSP   = Inst("b????????????????_011_?_?????_?????_10", rdNotZero)
  val C_JR     = Inst("b????????????????_100_0_?????_00000_10", rdNotZero)
  val C_MV     = Inst("b????????????????_100_0_?????_?????_10", (inst, xlen) => { rdNotZero(inst, xlen) && inst(6, 2) =/= 0.U })
  val C_EBREAK = Inst("b????????????????_100_1_00000_00000_10")
  val C_JALR   = Inst("b????????????????_100_1_?????_00000_10", rdNotZero)
  val C_ADD    = Inst("b????????????????_100_1_?????_?????_10", (inst, xlen) => { rdNotZero(inst, xlen) && inst(6, 2) =/= 0.U })

  val C_FSDSP = Inst("b????????????????_101_??????_?????_10")
  val C_SQSP  = Inst("b????????????????_101_??????_?????_10")
  val C_SWSP  = Inst("b????????????????_110_??????_?????_10")
  val C_FSWSP = Inst("b????????????????_111_??????_?????_10")
  val C_SDSP  = Inst("b????????????????_111_??????_?????_10")
  // scalafmt: { maxColumn = 120 } (back to defaults)
}

/** Decode part
  *
  *   - riscv-spec-20191213
  *   - Chapter 16: “C” Standard Extension for Compressed Instructions, Version
  *     2.0
  *   - 16.2 Compressed Instruction Formats
  */
trait CDecode extends BaseCore with CommonDecode {
  val funct2 = WireInit(0.U(2.W))
  val funct4 = WireInit(0.U(4.W))
  val funct6 = WireInit(0.U(6.W))
  val op     = WireInit(0.U(2.W))
  val rdP    = WireInit(0.U(3.W))
  val rs1P   = WireInit(0.U(3.W))
  val rs2P   = WireInit(0.U(3.W))

  // ph for placeholder, should not be used after decode
  val ph1  = WireInit(0.U(1.W)); val ph5 = WireInit(0.U(5.W))
  val ph6  = WireInit(0.U(6.W))
  val ph8  = WireInit(0.U(8.W))
  val ph3  = WireInit(0.U(3.W)); val ph2 = WireInit(0.U(2.W))
  val ph11 = WireInit(0.U(11.W))

  // Table 16.1: Compressed 16-bit RVC instruction formats.
  // format: off
  //                                       / 15  13 | 12  | 11   7 | 6           2 | 1 0 \
  def decodeCR  = { decodeInit; unpack(List(    funct4    ,  rs1   ,      rs2      , op  ), inst(15, 0)); rd := rs1     }
  def decodeCI  = { decodeInit; unpack(List( funct3 , ph1 ,  rs1   ,      ph5      , op  ), inst(15, 0)); rd := rs1     }
  def decodeCSS = { decodeInit; unpack(List( funct3 ,     ph6      ,      rs2      , op  ), inst(15, 0))                }
  def decodeCIW = { decodeInit; unpack(List( funct3 ,         ph8           , rdP  , op  ), inst(15, 0))                }
  def decodeCL  = { decodeInit; unpack(List( funct3 ,  ph3  , rs1P ,  ph2   , rdP  , op  ), inst(15, 0))                }
  def decodeCS  = { decodeInit; unpack(List( funct3 ,  ph3  , rs1P ,  ph2   , rs2P , op  ), inst(15, 0))                }
  def decodeCA  = { decodeInit; unpack(List(     funct6     , rs1P , funct2 , rs2P , op  ), inst(15, 0)); rdP := rs1P }
  def decodeCB  = { decodeInit; unpack(List( funct3 ,  ph3  , rs1P ,      ph5      , op  ), inst(15, 0)); rdP := rs1P } // rdP := rs1P described in C.SRLI
  def decodeCJ  = { decodeInit; unpack(List( funct3 ,             ph11             , op  ), inst(15, 0))                }
  //                                       \ 15  13 | 12 10 | 9  7 | 6    5 | 4  2 | 1 0 /
  // format: on
}

/** “C” Standard Extension for Compressed Instructions
  *
  *   - riscv-spec-20191213
  *   - Chapter 16: “C” Standard Extension for Compressed Instructions, Version
  *     2.0
  */
trait CExtension extends BaseCore with CDecode with CExtensionInsts { this: IBase =>

  def cat01(x: UInt): UInt = Cat("b01".U(2.W), x)

  def doCExtension(singleInst: Inst): Unit = {
    singleInst match {
      case C_LWSP =>
        decodeCI
        imm          := zeroExt(reorder(5, (4, 2), (7, 6))(inst, 12, (6, 2)), XLEN)
        next.reg(rd) := signExt(memRead(now.reg(2.U) + imm, 32.U)(31, 0), XLEN)
      case C_SWSP =>
        decodeCSS
        imm := zeroExt(reorder((5, 2), (7, 6))(inst, (12, 7)), XLEN)
        memWrite(now.reg(2.U) + imm, 32.U, now.reg(rs2)(31, 0))
      case C_LW =>
        decodeCL
        imm                  := zeroExt(reorder((5, 3), 2, (6, 6))(inst, (12, 10), (6, 5)), XLEN)
        next.reg(cat01(rdP)) := signExt(memRead(now.reg(cat01(rs1P)) + imm, 32.U)(31, 0), XLEN)
      case C_SW =>
        decodeCS
        imm := zeroExt(reorder((5, 3), 2, 6)(inst, (12, 10), (6, 5)), XLEN)
        memWrite(now.reg(cat01(rs1P)) + imm, 32.U, now.reg(cat01(rs2P)))
      case C_J =>
        decodeCJ
        imm               := signExt(reorder(11, 4, (9, 8), 10, 6, 7, (3, 1), 5)(inst, (12, 2)), XLEN)
        global_data.setpc := true.B
        next.pc           := now.pc + imm
      case C_JAL =>
        decodeCJ
        imm               := signExt(reorder(11, 4, (9, 8), 10, 6, 7, (3, 1), 5)(inst, (12, 2)), XLEN)
        global_data.setpc := true.B
        next.pc           := now.pc + imm
        next.reg(1.U)     := now.pc + 2.U
      case C_JR =>
        decodeCR
        global_data.setpc := true.B
        // setting the least-significant to zero according to JALR in RVI
        next.pc := Cat(now.reg(rs1)(XLEN - 1, 1), 0.U(1.W))
      case C_JALR =>
        decodeCR
        global_data.setpc := true.B
        // setting the least-significant to zero according to JALR in RVI
        next.pc       := Cat(now.reg(rs1)(XLEN - 1, 1), 0.U(1.W))
        next.reg(1.U) := now.pc + 2.U
      case C_BEQZ =>
        decodeCB
        imm := signExt(reorder(8, (4, 3), (7, 6), (2, 1), 5)(inst, (12, 10), (6, 2)), XLEN)
        when(now.reg(cat01(rs1P)) === 0.U) {
          global_data.setpc := true.B
          next.pc           := now.pc + imm
        }
      case C_BNEZ =>
        decodeCB
        imm := signExt(reorder(8, (4, 3), (7, 6), (2, 1), 5)(inst, (12, 10), (6, 2)), XLEN)
        when(now.reg(cat01(rs1P)) =/= 0.U) {
          global_data.setpc := true.B
          next.pc           := now.pc + imm
        }
      case C_LI =>
        decodeCI
        imm          := signExt(reorder(5, (4, 0))(inst, 12, (6, 2)), XLEN)
        next.reg(rd) := imm
      case C_LUI =>
        decodeCI
        val nzimm_C_LUI = signExt(reorder(17, (16, 12))(inst, 12, (6, 2)), XLEN)
        next.reg(rd) := nzimm_C_LUI
      case C_ADDI =>
        decodeCI
        val nzimm_C_ADDI = signExt(reorder(5, (4, 0))(inst, 12, (6, 2)), XLEN)
        next.reg(rd) := now.reg(rd) + nzimm_C_ADDI
      case C_ADDI16SP =>
        decodeCI
        val nzimm_C_ADDI16SP = signExt(reorder(9, 4, 6, (8, 7), 5)(inst, 12, (6, 2)), XLEN)
        next.reg(2.U) := now.reg(2.U) + nzimm_C_ADDI16SP
      case C_ADDI4SPN =>
        decodeCIW
        val nzimm_C_ADDI4SPN = zeroExt(reorder((5, 4), (9, 6), 2, 3)(inst, (12, 5)), XLEN)
        next.reg(cat01(rdP)) := now.reg(2.U) + nzimm_C_ADDI4SPN
      case C_SLLI =>
        decodeCI
        imm          := reorder(5, (4, 0))(inst, 12, (6, 2))
        next.reg(rd) := now.reg(rd) << imm(5, 0)
      case C_SRLI =>
        decodeCB
        imm                  := reorder(5, (4, 0))(inst, 12, (6, 2))
        next.reg(cat01(rdP)) := now.reg(cat01(rdP)) >> imm(5, 0)
      case C_SRAI =>
        decodeCB
        imm                  := reorder(5, (4, 0))(inst, 12, (6, 2))
        next.reg(cat01(rdP)) := (now.reg(cat01(rdP)).asSInt >> imm(5, 0)).asUInt
      case C_ANDI =>
        decodeCB
        imm                  := signExt(reorder(5, (4, 0))(inst, 12, (6, 2)), XLEN)
        next.reg(cat01(rdP)) := now.reg(cat01(rdP)) & imm
      case C_MV  => decodeCR; next.reg(rd) := now.reg(0.U) + now.reg(rs2)
      case C_ADD => decodeCR; next.reg(rd) := now.reg(rd) + now.reg(rs2)
      case C_AND => decodeCA; next.reg(cat01(rdP)) := now.reg(cat01(rdP)) & now.reg(cat01(rs2P))
      case C_OR  => decodeCA; next.reg(cat01(rdP)) := now.reg(cat01(rdP)) | now.reg(cat01(rs2P))
      case C_XOR => decodeCA; next.reg(cat01(rdP)) := now.reg(cat01(rdP)) ^ now.reg(cat01(rs2P))
      case C_SUB => decodeCA; next.reg(cat01(rdP)) := now.reg(cat01(rdP)) - now.reg(cat01(rs2P))
      case C_NOP => decodeCI /* then do nothing */
      case C_LDSP if config.XLEN == 64 =>
        decodeCI
        imm          := zeroExt(reorder(5, (4, 3), (8, 6))(inst, 12, (6, 2)), XLEN)
        next.reg(rd) := signExt(memRead(now.reg(2.U) + imm, 64.U)(63, 0), XLEN)
      case C_SDSP if config.XLEN == 64 =>
        decodeCSS
        imm := zeroExt(reorder((5, 3), (8, 6))(inst, (12, 7)), XLEN)
        memWrite(now.reg(2.U) + imm, 64.U, now.reg(rs2)(63, 0))
      case C_LD if config.XLEN == 64 =>
        decodeCL
        imm                  := zeroExt(reorder((5, 3), (7, 6))(inst, (12, 10), (6, 5)), XLEN)
        next.reg(cat01(rdP)) := signExt(memRead(now.reg(cat01(rs1P)) + imm, 64.U)(63, 0), XLEN)
      case C_SD if config.XLEN == 64 =>
        decodeCS
        imm := zeroExt(reorder((5, 3), (7, 6))(inst, (12, 10), (6, 5)), XLEN)
        memWrite(now.reg(cat01(rs1P)), 64.U, now.reg(cat01(rs2P)))
      case C_ADDIW if config.XLEN == 64 =>
        decodeCI
        imm          := signExt(reorder(5, (4, 0))(inst, 12, (6, 2)), XLEN)
        next.reg(rd) := signExt((now.reg(rd) + imm)(31, 0), XLEN)
      case C_ADDW if config.XLEN == 64 =>
        decodeCA
        next.reg(cat01(rdP)) := signExt(now.reg(cat01(rdP))(31, 0) + now.reg(cat01(rs2P))(31, 0), XLEN)
      case C_SUBW if config.XLEN == 64 =>
        decodeCA
        next.reg(cat01(rdP)) := signExt(now.reg(cat01(rdP))(31, 0) - now.reg(cat01(rs2P))(31, 0), XLEN)
      case _ =>
    }
  }

  def doRVC: Unit = {
    // format: off
    val rv32cInsts = Seq(
      C_LWSP,   C_SWSP,   C_LW,     C_SW,     C_J,        C_JAL,      C_JR,      C_JALR,  C_BEQZ,
      C_BNEZ,   C_LI,     C_LUI,    C_ADDI,   C_ADDI16SP, C_ADDI4SPN, C_SLLI,    C_SRLI,  C_SRAI,
      C_ANDI,   C_MV,     C_ADD,    C_AND,    C_OR,       C_XOR,      C_SUB,     C_NOP,
    )
    // format: on
    val rv64cInsts = rv32cInsts ++ Seq(C_LDSP, C_SDSP, C_LD, C_SD, C_ADDIW, C_ADDW, C_SUBW)

    config.XLEN match {
      case 32 => rv32cInsts.map(rv32cInst => when(rv32cInst(inst)) { doCExtension(rv32cInst) })
      case 64 => rv64cInsts.map(rv64cInst => when(rv64cInst(inst)) { doCExtension(rv64cInst) })
    }
  }

}

package rvspeccore.core.spec.instset

import chisel3._
import chisel3.util._
import rvspeccore.core.BaseCore
import rvspeccore.core.spec._
import rvspeccore.core.tool.BitTool._
import rvspeccore.core.tool.{CheckTool, LoadStore}
import rvspeccore.core.spec.instset.csr._

/** Base Integer Instructions
  *
  *   - riscv-spec-20191213
  *   - Chapter 24: RV32/64G Instruction Set Listings
  *     - Table 24.2: Instruction listing for RISC-V
  */
trait IBaseInsts {
  // - RV32I Base Instruction Set
  val LUI   = Inst("b????????????????????_?????_0110111")
  val AUIPC = Inst("b????????????????????_?????_0010111")
  val JAL   = Inst("b????????????????????_?????_1101111")
  val JALR  = Inst("b????????????_?????_000_?????_1100111")

  val BEQ  = Inst("b???????_?????_?????_000_?????_1100011")
  val BNE  = Inst("b???????_?????_?????_001_?????_1100011")
  val BLT  = Inst("b???????_?????_?????_100_?????_1100011")
  val BGE  = Inst("b???????_?????_?????_101_?????_1100011")
  val BLTU = Inst("b???????_?????_?????_110_?????_1100011")
  val BGEU = Inst("b???????_?????_?????_111_?????_1100011")

  val LB  = Inst("b????????????_?????_000_?????_0000011")
  val LH  = Inst("b????????????_?????_001_?????_0000011")
  val LW  = Inst("b????????????_?????_010_?????_0000011")
  val LBU = Inst("b????????????_?????_100_?????_0000011")
  val LHU = Inst("b????????????_?????_101_?????_0000011")
  val SB  = Inst("b???????_?????_?????_000_?????_0100011")
  val SH  = Inst("b???????_?????_?????_001_?????_0100011")
  val SW  = Inst("b???????_?????_?????_010_?????_0100011")

  val ADDI  = Inst("b????????????_?????_000_?????_0010011")
  val SLTI  = Inst("b????????????_?????_010_?????_0010011")
  val SLTIU = Inst("b????????????_?????_011_?????_0010011")
  val XORI  = Inst("b????????????_?????_100_?????_0010011")
  val ORI   = Inst("b????????????_?????_110_?????_0010011")
  val ANDI  = Inst("b????????????_?????_111_?????_0010011")

  val SLLI = Inst(
    32 -> "b0000000_?????_?????_001_?????_0010011",
    64 -> "b000000_??????_?????_001_?????_0010011"
  )
  val SRLI = Inst(
    32 -> "b0000000_?????_?????_101_?????_0010011",
    64 -> "b000000_??????_?????_101_?????_0010011"
  )
  val SRAI = Inst(
    32 -> "b0100000_?????_?????_101_?????_0010011",
    64 -> "b010000_??????_?????_101_?????_0010011"
  )

  val ADD  = Inst("b0000000_?????_?????_000_?????_0110011")
  val SUB  = Inst("b0100000_?????_?????_000_?????_0110011")
  val SLL  = Inst("b0000000_?????_?????_001_?????_0110011")
  val SLT  = Inst("b0000000_?????_?????_010_?????_0110011")
  val SLTU = Inst("b0000000_?????_?????_011_?????_0110011")
  val XOR  = Inst("b0000000_?????_?????_100_?????_0110011")
  val SRL  = Inst("b0000000_?????_?????_101_?????_0110011")
  val SRA  = Inst("b0100000_?????_?????_101_?????_0110011")
  val OR   = Inst("b0000000_?????_?????_110_?????_0110011")
  val AND  = Inst("b0000000_?????_?????_111_?????_0110011")

  val FENCE = Inst("b????????????_?????_000_?????_0001111")

  val ECALL  = Inst("b000000000000_00000_000_00000_1110011")
  val EBREAK = Inst("b000000000001_00000_000_00000_1110011")

  // - RV64I Base Instruction Set (in addition to RV32I)
  val LWU = Inst("b???????_?????_?????_110_?????_0000011")
  val LD  = Inst("b???????_?????_?????_011_?????_0000011")
  val SD  = Inst("b???????_?????_?????_011_?????_0100011")

  // SLLI, SRLI, SRAI defined earlier

  val ADDIW = Inst("b????????????_?????_000_?????_0011011")
  val SLLIW = Inst("b0000000_?????_?????_001_?????_0011011")
  val SRLIW = Inst("b0000000_?????_?????_101_?????_0011011")
  val SRAIW = Inst("b0100000_?????_?????_101_?????_0011011")

  val ADDW = Inst("b0000000_?????_?????_000_?????_0111011")
  val SUBW = Inst("b0100000_?????_?????_000_?????_0111011")
  val SLLW = Inst("b0000000_?????_?????_001_?????_0111011")
  val SRLW = Inst("b0000000_?????_?????_101_?????_0111011")
  val SRAW = Inst("b0100000_?????_?????_101_?????_0111011")
}

// scalafmt: { maxColumn = 200 }
object SizeOp {
  def b = "b00".U
  def h = "b01".U
  def w = "b10".U
  def d = "b11".U
}
trait IBase extends BaseCore with CommonDecode with IBaseInsts with ExceptionSupport with LoadStore with CheckTool {
  // val setPc = WireInit(false.B)

  def addrAligned(size: UInt, addr: UInt): Bool = {
    MuxLookup(size, false.B)(
      Seq(
        "b00".U -> true.B,               // b
        "b01".U -> (addr(0) === 0.U),    // h
        "b10".U -> (addr(1, 0) === 0.U), // w
        "b11".U -> (addr(2, 0) === 0.U)  // d
      )
    )
  }

  def getfetchSize(): UInt = {
    MuxLookup(now.privilege.csr.misa(CSR.getMisaExtInt('C')), SizeOp.w)(
      Seq(
        "b0".U -> SizeOp.w,
        "b1".U -> SizeOp.h
      )
    )
  }

  def opArithLogic(rd: UInt, op1: UInt, op2: UInt, func: (UInt, UInt) => UInt): Unit = {
    updateDestReg(rd, func(op1, op2))
  }

  def opJumpLink(rd: UInt, target: UInt): Unit = {
    when(addrAligned(getfetchSize(), target)) {
      global_data.setpc := true.B;
      next.pc           := target;
      updateDestReg(rd, now.pc + 4.U)
    }.otherwise {
      next.privilege.csr.mtval := target;
      raiseException(MExceptionCode.instructionAddressMisaligned)
    }
  }

  def opBranch(rs1: UInt, rs2: UInt, compare: (UInt, UInt) => Bool): Unit = {
    when(compare(getSrc1Reg(rs1), getSrc2Reg(rs2))) {
      val npc = now.pc + imm
      when(addrAligned(getfetchSize(), npc)) {
        global_data.setpc := true.B
        next.pc           := npc
      }.otherwise {
        next.privilege.csr.mtval := npc
        raiseException(MExceptionCode.instructionAddressMisaligned)
      }
    }
  }

  def opLoad(rd: UInt, rs1: UInt, imm: UInt, sizeOp: UInt, isUnsigned: Boolean): Unit = {
    val width   = 8 * math.pow(2, sizeOp.litValue.toDouble).toInt
    val extFunc = if (isUnsigned) zeroExt _ else signExt _
    when(addrAligned(sizeOp, getSrc1Reg(rs1) + imm)) {
      updateDestReg(rd, extFunc(memRead(getSrc1Reg(rs1) + imm, width.U)(width - 1, 0), XLEN))
    }.otherwise {
      mem.read.addr := getSrc1Reg(rs1) + imm
      raiseException(MExceptionCode.loadAddressMisaligned)
    }
  }

  def opStore(rs1: UInt, rs2: UInt, imm: UInt, sizeOp: UInt): Unit = {
    val width = 8 * math.pow(2, sizeOp.litValue.toDouble).toInt
    when(addrAligned(sizeOp, getSrc1Reg(rs1) + imm)) {
      memWrite(getSrc1Reg(rs1) + imm, width.U, getSrc2Reg(rs2)(width - 1, 0))
    }.otherwise {
      mem.write.addr := getSrc1Reg(rs1) + imm
      raiseException(MExceptionCode.storeOrAMOAddressMisaligned)
    }
  }

  def doIBase(singleInst: Inst): Unit = {
    singleInst match {
      case ADD  => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), _ + _)
      case SLT  => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), (a, b) => Mux(a.asSInt < b.asSInt, 1.U, 0.U))
      case SLTU => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), (a, b) => Mux(a < b, 1.U, 0.U))
      case AND  => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), _ & _)
      case OR   => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), _ | _)
      case XOR  => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), _ ^ _)
      case SLL =>
        decodeR;
        config.XLEN match {
          case 32 => opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), _ << _(4, 0))
          case 64 => opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), _ << _(5, 0))
        }
      case SRL =>
        decodeR;
        config.XLEN match {
          case 32 => opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), _ >> _(4, 0))
          case 64 => opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), _ >> _(5, 0))
        }
      case SUB => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), _ - _)
      case SRA =>
        decodeR;
        config.XLEN match {
          case 32 => opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), (a, b) => (a.asSInt >> b(4, 0)).asUInt)
          case 64 => opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), (a, b) => (a.asSInt >> b(5, 0)).asUInt)
        }
      case ADDI  => decodeI; opArithLogic(rd, getSrc1Reg(rs1), imm, _ + _)
      case SLTI  => decodeI; opArithLogic(rd, getSrc1Reg(rs1), imm, (a, b) => Mux(a.asSInt < b.asSInt, 1.U, 0.U))
      case SLTIU => decodeI; opArithLogic(rd, getSrc1Reg(rs1), imm, (a, b) => Mux(a < b, 1.U, 0.U))
      case ANDI  => decodeI; opArithLogic(rd, getSrc1Reg(rs1), imm, _ & _)
      case ORI   => decodeI; opArithLogic(rd, getSrc1Reg(rs1), imm, _ | _)
      case XORI  => decodeI; opArithLogic(rd, getSrc1Reg(rs1), imm, _ ^ _)
      case SLLI =>
        decodeI;
        config.XLEN match {
          case 32 => opArithLogic(rd, getSrc1Reg(rs1), imm, _ << _(4, 0))
          case 64 => opArithLogic(rd, getSrc1Reg(rs1), imm, _ << _(5, 0))
        }
      case SRLI =>
        decodeI;
        config.XLEN match {
          case 32 => opArithLogic(rd, getSrc1Reg(rs1), imm, _ >> _(4, 0))
          case 64 => opArithLogic(rd, getSrc1Reg(rs1), imm, _ >> _(5, 0))
        }
      case SRAI =>
        decodeI;
        config.XLEN match {
          case 32 => opArithLogic(rd, getSrc1Reg(rs1), imm, (a, b) => (a.asSInt >> b(4, 0)).asUInt)
          case 64 => opArithLogic(rd, getSrc1Reg(rs1), imm, (a, b) => (a.asSInt >> b(5, 0)).asUInt)
        }
      case LUI    => decodeU; opArithLogic(rd, imm, 0.U, _ + _)
      case AUIPC  => decodeU; opArithLogic(rd, imm, now.pc, _ + _)
      case JAL    => decodeJ; opJumpLink(rd, now.pc + imm)
      case JALR   => decodeI; opJumpLink(rd, Cat((getSrc1Reg(rs1) + imm)(XLEN - 1, 1), 0.U(1.W)))
      case BEQ    => decodeB; opBranch(rs1, rs2, _ === _)
      case BNE    => decodeB; opBranch(rs1, rs2, _ =/= _)
      case BLT    => decodeB; opBranch(rs1, rs2, _.asSInt < _.asSInt)
      case BLTU   => decodeB; opBranch(rs1, rs2, _ < _)
      case BGE    => decodeB; opBranch(rs1, rs2, _.asSInt >= _.asSInt)
      case BGEU   => decodeB; opBranch(rs1, rs2, _ >= _)
      case LB     => decodeI; opLoad(rd, rs1, imm, SizeOp.b, false)
      case LH     => decodeI; opLoad(rd, rs1, imm, SizeOp.h, false)
      case LW     => decodeI; opLoad(rd, rs1, imm, SizeOp.w, false)
      case LBU    => decodeI; opLoad(rd, rs1, imm, SizeOp.b, true)
      case LHU    => decodeI; opLoad(rd, rs1, imm, SizeOp.h, true)
      case SB     => decodeS; opStore(rs1, rs2, imm, SizeOp.b)
      case SH     => decodeS; opStore(rs1, rs2, imm, SizeOp.h)
      case SW     => decodeS; opStore(rs1, rs2, imm, SizeOp.w)
      case EBREAK => decodeI; raiseException(MExceptionCode.breakpoint)
      case ECALL =>
        decodeI;
        switch(now.privilege.internal.privilegeMode) {
          is(0x3.U) { raiseException(MExceptionCode.environmentCallFromMmode) }
          is(0x1.U) { raiseException(MExceptionCode.environmentCallFromSmode) }
          is(0x0.U) { raiseException(MExceptionCode.environmentCallFromUmode) }
        }
      case FENCE                      => decodeI
      case ADDIW if config.XLEN == 64 => decodeI; opArithLogic(rd, getSrc1Reg(rs1), imm, (a, b) => signExt((a + b(31, 0))(31, 0), XLEN))
      case SLLIW if config.XLEN == 64 => decodeI; opArithLogic(rd, getSrc1Reg(rs1), imm, (a, b) => signExt((a(31, 0) << b(4, 0))(31, 0), XLEN))
      case SRLIW if config.XLEN == 64 => decodeI; opArithLogic(rd, getSrc1Reg(rs1), imm, (a, b) => signExt((a(31, 0) >> b(4, 0))(31, 0), XLEN))
      case SRAIW if config.XLEN == 64 => decodeI; opArithLogic(rd, getSrc1Reg(rs1), imm, (a, b) => signExt((a(31, 0).asSInt >> b(4, 0)).asUInt, XLEN))
      case ADDW if config.XLEN == 64  => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), (a, b) => signExt((a(31, 0) + b(31, 0))(31, 0), XLEN))
      case SUBW if config.XLEN == 64  => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), (a, b) => signExt((a(31, 0) - b(31, 0))(31, 0), XLEN))
      case SLLW if config.XLEN == 64  => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), (a, b) => signExt((a(31, 0) << b(4, 0))(31, 0), XLEN))
      case SRLW if config.XLEN == 64  => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), (a, b) => signExt((a(31, 0) >> b(4, 0))(31, 0), XLEN))
      case SRAW if config.XLEN == 64  => decodeR; opArithLogic(rd, getSrc1Reg(rs1), getSrc2Reg(rs2), (a, b) => signExt((a(31, 0).asSInt >> b(4, 0)).asUInt, XLEN))
      case LWU if config.XLEN == 64   => decodeI; opLoad(rd, rs1, imm, SizeOp.w, true)
      case LD if config.XLEN == 64    => decodeI; opLoad(rd, rs1, imm, SizeOp.d, false)
      case SD if config.XLEN == 64    => decodeS; opStore(rs1, rs2, imm, SizeOp.d)
      case _                          =>
    }
  }

  def doRVI: Unit = {
    // format: off
    val rv32iInsts = Seq(
      LUI,    AUIPC,  JAL,    JALR,   BEQ,    BNE,    BLT,    BGE,    BLTU,   BGEU,
      LB,     LH,     LW,     LBU,    LHU,    SB,     SH,     SW,     ADDI,   SLTI,
      SLTIU,  XORI,   ORI,    ANDI,   SLLI,   SRLI,   SRAI,   ADD,    SUB,    SLL,
      SLT,    SLTU,   XOR,    SRL,    SRA,    OR,     AND,    FENCE,  ECALL,  EBREAK,
    )
    // format: on
    val rv64iInsts = rv32iInsts ++ Seq(LWU, LD, SD, ADDIW, SLLIW, SRLIW, SRAIW, ADDW, SUBW, SLLW, SRLW, SRAW)

    config.XLEN match {
      case 32 => rv32iInsts.map(rv32iInst => when(rv32iInst(inst)) { doIBase(rv32iInst) })
      case 64 => rv64iInsts.map(rv64iInst => when(rv64iInst(inst)) { doIBase(rv64iInst) })
    }
  }

}

// scalafmt: { maxColumn = 120 } (back to defaults)

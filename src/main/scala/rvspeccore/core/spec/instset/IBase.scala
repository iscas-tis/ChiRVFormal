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
  def alignedException(method: String, size: UInt, addr: UInt): Unit = {
    when(!addrAligned(size, addr)) {
      method match {
        case "Store" => {
          raiseException(MExceptionCode.storeOrAMOAddressMisaligned)
        }
        case "Load" => {
          raiseException(MExceptionCode.loadAddressMisaligned)
        }
        case "Instr" => {
          raiseException(MExceptionCode.instructionAddressMisaligned)
        }
      }
    }

  }
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

  def doIBase(singleInst: Inst): Unit = {
    singleInst match {
      case ADD =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := now.reg(rs1) + now.reg(rs2); updateNextWrite(rd)
      case SLT =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := Mux(now.reg(rs1).asSInt < now.reg(rs2).asSInt, 1.U, 0.U); updateNextWrite(rd)
      case SLTU =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := Mux(now.reg(rs1) < now.reg(rs2), 1.U, 0.U); updateNextWrite(rd)
      case AND =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := now.reg(rs1) & now.reg(rs2); updateNextWrite(rd)
      case OR =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := now.reg(rs1) | now.reg(rs2); updateNextWrite(rd)
      case XOR =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := now.reg(rs1) ^ now.reg(rs2); updateNextWrite(rd)
      case SLL =>
        decodeR; checkSrcReg(rs1, rs2);
        config.XLEN match {
          case 32 => next.reg(rd) := now.reg(rs1) << now.reg(rs2)(4, 0)
          case 64 => next.reg(rd) := now.reg(rs1) << now.reg(rs2)(5, 0)
        }
        updateNextWrite(rd)
      case SRL =>
        decodeR; checkSrcReg(rs1, rs2);
        config.XLEN match {
          case 32 => next.reg(rd) := now.reg(rs1) >> now.reg(rs2)(4, 0)
          case 64 => next.reg(rd) := now.reg(rs1) >> now.reg(rs2)(5, 0)
        }
        updateNextWrite(rd)
      case SUB =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := now.reg(rs1) - now.reg(rs2); updateNextWrite(rd)
      case SRA =>
        decodeR; checkSrcReg(rs1, rs2);
        config.XLEN match {
          case 32 => next.reg(rd) := (now.reg(rs1).asSInt >> now.reg(rs2)(4, 0)).asUInt
          case 64 => next.reg(rd) := (now.reg(rs1).asSInt >> now.reg(rs2)(5, 0)).asUInt
        }
        updateNextWrite(rd)
      case ADDI =>
        decodeI; checkSrcImm(rs1); next.reg(rd) := now.reg(rs1) + imm; updateNextWrite(rd)
      case SLTI =>
        decodeI; checkSrcImm(rs1); next.reg(rd) := Mux(now.reg(rs1).asSInt < imm.asSInt, 1.U, 0.U); updateNextWrite(rd)
      case SLTIU =>
        decodeI; checkSrcImm(rs1); next.reg(rd) := Mux(now.reg(rs1) < imm, 1.U, 0.U); updateNextWrite(rd)
      case ANDI =>
        decodeI; checkSrcImm(rs1); next.reg(rd) := now.reg(rs1) & imm; updateNextWrite(rd)
      case ORI =>
        decodeI; checkSrcImm(rs1); next.reg(rd) := now.reg(rs1) | imm; updateNextWrite(rd)
      case XORI =>
        decodeI; checkSrcImm(rs1); next.reg(rd) := now.reg(rs1) ^ imm; updateNextWrite(rd)
      case SLLI =>
        decodeI; checkSrcImm(rs1);
        config.XLEN match {
          case 32 => next.reg(rd) := now.reg(rs1) << imm(4, 0)
          case 64 => next.reg(rd) := now.reg(rs1) << imm(5, 0)
        }
        updateNextWrite(rd)
      case SRLI =>
        decodeI; checkSrcImm(rs1);
        config.XLEN match {
          case 32 => next.reg(rd) := now.reg(rs1) >> imm(4, 0)
          case 64 => next.reg(rd) := now.reg(rs1) >> imm(5, 0)
        }
        updateNextWrite(rd)
      case SRAI =>
        decodeI; checkSrcImm(rs1);
        config.XLEN match {
          case 32 => next.reg(rd) := (now.reg(rs1).asSInt >> imm(4, 0)).asUInt
          case 64 => next.reg(rd) := (now.reg(rs1).asSInt >> imm(5, 0)).asUInt
        }
        updateNextWrite(rd)
      case LUI =>
        decodeU; next.reg(rd) := imm; updateNextWrite(rd)
      case AUIPC =>
        decodeU; next.reg(rd) := now.pc + imm; updateNextWrite(rd)
      case JAL =>
        decodeJ;
        when(addrAligned(getfetchSize(), now.pc + imm)) {
          global_data.setpc := true.B;
          next.pc           := now.pc + imm;
          next.reg(rd)      := now.pc + 4.U;
          updateNextWrite(rd)
        }.otherwise {
          next.privilege.csr.mtval := now.pc + imm;
          raiseException(MExceptionCode.instructionAddressMisaligned)
        }
      case JALR =>
        decodeI; checkSrcImm(rs1);
        when(addrAligned(getfetchSize(), Cat((now.reg(rs1) + imm)(XLEN - 1, 1), 0.U(1.W)))) {
          global_data.setpc := true.B;
          next.pc           := Cat((now.reg(rs1) + imm)(XLEN - 1, 1), 0.U(1.W));
          next.reg(rd)      := now.pc + 4.U;
          updateNextWrite(rd)
        }.otherwise {
          next.privilege.csr.mtval := Cat((now.reg(rs1) + imm)(XLEN - 1, 1), 0.U(1.W))
          raiseException(MExceptionCode.instructionAddressMisaligned)
        }
      case BEQ =>
        decodeB; checkSrcReg(rs1, rs2);
        when(now.reg(rs1) === now.reg(rs2)) {
          when(addrAligned(getfetchSize(), now.pc + imm)) {
            global_data.setpc := true.B;
            next.pc           := now.pc + imm;
          }.otherwise {
            next.privilege.csr.mtval := now.pc + imm;
            raiseException(MExceptionCode.instructionAddressMisaligned)
          }
        }
      case BNE =>
        decodeB; checkSrcReg(rs1, rs2);
        when(now.reg(rs1) =/= now.reg(rs2)) {
          when(addrAligned(getfetchSize(), now.pc + imm)) {
            global_data.setpc := true.B;
            next.pc           := now.pc + imm;
          }.otherwise {
            next.privilege.csr.mtval := now.pc + imm;
            raiseException(MExceptionCode.instructionAddressMisaligned)
          }
        }
      case BLT =>
        decodeB; checkSrcReg(rs1, rs2);
        when(now.reg(rs1).asSInt < now.reg(rs2).asSInt) {
          when(addrAligned(getfetchSize(), now.pc + imm)) {
            global_data.setpc := true.B;
            next.pc           := now.pc + imm
          }.otherwise {
            next.privilege.csr.mtval := now.pc + imm;
            raiseException(MExceptionCode.instructionAddressMisaligned)
          }
        }
      case BLTU =>
        decodeB; checkSrcReg(rs1, rs2);
        when(now.reg(rs1) < now.reg(rs2)) {
          when(addrAligned(getfetchSize(), now.pc + imm)) {
            global_data.setpc := true.B;
            next.pc           := now.pc + imm
          }.otherwise {
            next.privilege.csr.mtval := now.pc + imm;
            raiseException(MExceptionCode.instructionAddressMisaligned)
          }
        }
      case BGE =>
        decodeB; checkSrcReg(rs1, rs2);
        when(now.reg(rs1).asSInt >= now.reg(rs2).asSInt) {
          when(addrAligned(getfetchSize(), now.pc + imm)) {
            global_data.setpc := true.B;
            next.pc           := now.pc + imm
          }.otherwise {
            next.privilege.csr.mtval := now.pc + imm;
            raiseException(MExceptionCode.instructionAddressMisaligned)
          }
        }
      case BGEU =>
        decodeB; checkSrcReg(rs1, rs2);
        when(now.reg(rs1) >= now.reg(rs2)) {
          when(addrAligned(getfetchSize(), now.pc + imm)) {
            global_data.setpc := true.B;
            next.pc           := now.pc + imm
          }.otherwise {
            next.privilege.csr.mtval := now.pc + imm;
            raiseException(MExceptionCode.instructionAddressMisaligned)
          }
        }
      case LB =>
        decodeI; checkSrcImm(rs1);
        when(addrAligned(SizeOp.b, now.reg(rs1) + imm)) {
          next.reg(rd) := signExt(memRead(now.reg(rs1) + imm, 8.U)(7, 0), XLEN)
          updateNextWrite(rd)
        }.otherwise {
          // TODO: LB doesn't seem to get an exception for unaligned access
          mem.read.addr := now.reg(rs1) + imm
          raiseException(MExceptionCode.loadAddressMisaligned)
        }
      case LH =>
        decodeI; checkSrcImm(rs1);
        when(addrAligned(SizeOp.h, now.reg(rs1) + imm)) {
          next.reg(rd) := signExt(memRead(now.reg(rs1) + imm, 16.U)(15, 0), XLEN)
          updateNextWrite(rd)
        }.otherwise {
          mem.read.addr := now.reg(rs1) + imm
          raiseException(MExceptionCode.loadAddressMisaligned)
        }
      case LW =>
        decodeI; checkSrcImm(rs1);
        when(addrAligned(SizeOp.w, now.reg(rs1) + imm)) {
          next.reg(rd) := signExt(memRead(now.reg(rs1) + imm, 32.U)(31, 0), XLEN)
          updateNextWrite(rd)
        }.otherwise {
          mem.read.addr := now.reg(rs1) + imm
          raiseException(MExceptionCode.loadAddressMisaligned)
        }
      case LBU =>
        decodeI; checkSrcImm(rs1); alignedException("Load", SizeOp.b, rs2); next.reg(rd) := zeroExt(memRead(now.reg(rs1) + imm, 8.U)(7, 0), XLEN); updateNextWrite(rd)
      case LHU =>
        decodeI; checkSrcImm(rs1);
        when(addrAligned(SizeOp.h, now.reg(rs1) + imm)) {
          next.reg(rd) := zeroExt(memRead(now.reg(rs1) + imm, 16.U)(15, 0), XLEN)
          updateNextWrite(rd)
        }.otherwise {
          mem.read.addr := now.reg(rs1) + imm
          raiseException(MExceptionCode.loadAddressMisaligned)
        }
      case SB =>
        decodeS; checkSrcImm(rs1); alignedException("Store", SizeOp.b, rs2); memWrite(now.reg(rs1) + imm, 8.U, now.reg(rs2)(7, 0))
      case SH =>
        decodeS; checkSrcImm(rs1);
        when(addrAligned(SizeOp.h, now.reg(rs1) + imm)) {
          memWrite(now.reg(rs1) + imm, 16.U, now.reg(rs2)(15, 0))
        }.otherwise {
          mem.write.addr := now.reg(rs1) + imm
          raiseException(MExceptionCode.storeOrAMOAddressMisaligned)
        }
      case SW =>
        decodeS; checkSrcImm(rs1);
        when(addrAligned(SizeOp.w, now.reg(rs1) + imm)) {
          memWrite(now.reg(rs1) + imm, 32.U, now.reg(rs2)(31, 0))
        }.otherwise {
          mem.write.addr := now.reg(rs1) + imm
          raiseException(MExceptionCode.storeOrAMOAddressMisaligned)
        }
      case EBREAK =>
        decodeI;
        raiseException(MExceptionCode.breakpoint)
      case ECALL =>
        decodeI;
        switch(now.privilege.internal.privilegeMode) {
          is(0x3.U) { raiseException(MExceptionCode.environmentCallFromMmode) }
          is(0x1.U) { raiseException(MExceptionCode.environmentCallFromSmode) }
          is(0x0.U) { raiseException(MExceptionCode.environmentCallFromUmode) }
        }
      case FENCE =>
        decodeI;
      case ADDIW if config.XLEN == 64 =>
        decodeI; checkSrcImm(rs1); next.reg(rd) := signExt((now.reg(rs1) + imm)(31, 0), XLEN); updateNextWrite(rd)
      case SLLIW if config.XLEN == 64 =>
        decodeI; checkSrcImm(rs1); next.reg(rd) := signExt((now.reg(rs1)(31, 0) << imm(4, 0))(31, 0), XLEN); updateNextWrite(rd)
      case SRLIW if config.XLEN == 64 =>
        decodeI; checkSrcImm(rs1); next.reg(rd) := signExt((now.reg(rs1)(31, 0) >> imm(4, 0))(31, 0), XLEN); updateNextWrite(rd)
      case SRAIW if config.XLEN == 64 =>
        decodeI; checkSrcImm(rs1); next.reg(rd) := signExt((now.reg(rs1)(31, 0).asSInt >> imm(4, 0)).asUInt, XLEN); updateNextWrite(rd)
      case ADDW if config.XLEN == 64 =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := signExt((now.reg(rs1)(31, 0) + now.reg(rs2)(31, 0))(31, 0), XLEN); updateNextWrite(rd)
      case SUBW if config.XLEN == 64 =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := signExt((now.reg(rs1)(31, 0) - now.reg(rs2)(31, 0))(31, 0), XLEN); updateNextWrite(rd)
      case SLLW if config.XLEN == 64 =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := signExt((now.reg(rs1)(31, 0) << now.reg(rs2)(4, 0))(31, 0), XLEN); updateNextWrite(rd)
      case SRLW if config.XLEN == 64 =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := signExt((now.reg(rs1)(31, 0) >> now.reg(rs2)(4, 0))(31, 0), XLEN); updateNextWrite(rd)
      case SRAW if config.XLEN == 64 =>
        decodeR; checkSrcReg(rs1, rs2); next.reg(rd) := signExt((now.reg(rs1)(31, 0).asSInt >> now.reg(rs2)(4, 0)).asUInt, XLEN); updateNextWrite(rd)
      case LWU if config.XLEN == 64 =>
        decodeI; checkSrcImm(rs1);
        when(addrAligned(SizeOp.w, now.reg(rs1) + imm)) {
          next.reg(rd) := zeroExt(memRead(now.reg(rs1) + imm, 32.U)(31, 0), XLEN)
          updateNextWrite(rd)
        }.otherwise {
          mem.read.addr := now.reg(rs1) + imm
          raiseException(MExceptionCode.loadAddressMisaligned)
        }
      case LD if config.XLEN == 64 =>
        decodeI; checkSrcImm(rs1);
        when(addrAligned(SizeOp.d, now.reg(rs1) + imm)) {
          next.reg(rd) := memRead(now.reg(rs1) + imm, 64.U)
          updateNextWrite(rd)
        }.otherwise {
          mem.read.addr := now.reg(rs1) + imm
          raiseException(MExceptionCode.loadAddressMisaligned)
        }
      case SD if config.XLEN == 64 =>
        decodeS; checkSrcImm(rs1);
        when(addrAligned(SizeOp.d, now.reg(rs1) + imm)) {
          memWrite(now.reg(rs1) + imm, 64.U, now.reg(rs2)(63, 0))
        }.otherwise {
          mem.write.addr := now.reg(rs1) + imm
          raiseException(MExceptionCode.storeOrAMOAddressMisaligned)
        }
      case _ =>
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

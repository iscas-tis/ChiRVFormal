package rvspeccore.core.tool

import chisel3._
import rvspeccore.core.BaseCore

trait CheckTool extends BaseCore {
  def updateDestReg(rd_addr: UInt, rd_data: UInt): Unit = {
    specWb.rd_en      := true.B
    specWb.rd_addr    := rd_addr
    specWb.rd_data    := next.reg(rd_addr)
    next.reg(rd_addr) := rd_data
  }

  def getSrc1Reg(rs1_addr: UInt): UInt = {
    specWb.rs1_addr := rs1_addr
    specWb.checkrs1 := true.B
    now.reg(rs1_addr)
  }

  def getSrc2Reg(rs2_addr: UInt): UInt = {
    specWb.rs2_addr := rs2_addr
    specWb.checkrs2 := true.B
    now.reg(rs2_addr)
  }

  def updateDestCsr(csr_addr: UInt): Unit = {
    specWb.csr_addr := csr_addr
    specWb.csr_wr   := true.B
  }
}

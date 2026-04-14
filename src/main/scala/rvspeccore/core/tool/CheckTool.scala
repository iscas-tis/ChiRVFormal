package rvspeccore.core.tool

import chisel3._
import rvspeccore.core.BaseCore

trait CheckTool extends BaseCore {
  def setPC(target: UInt): Unit = {
    setpc   := true.B
    next.pc := target
  }

  def updateDestReg(addr: UInt, data: UInt): Unit = {
    commit.rdAddr := addr
    when(addr =/= 0.U) {
      commit.rdData  := data
      next.reg(addr) := data
    }
  }

  def getSrc1Reg(addr: UInt): UInt = {
    commit.readRs1 := true.B
    commit.rs1Addr := addr
    now.reg(addr)
  }

  def getSrc2Reg(addr: UInt): UInt = {
    commit.readRs2 := true.B
    commit.rs2Addr := addr
    now.reg(addr)
  }

  def accessCsr(addr: UInt, data: UInt): Unit = {
    commit.csrWr    := true.B
    commit.csrAddr  := addr
    commit.csrNdata := data
  }
}

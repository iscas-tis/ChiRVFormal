package rvspeccore.core.spec.instset.csr

import chisel3._
import chisel3.util._

import rvspeccore.core.BaseCore
import rvspeccore.core.spec._
import rvspeccore.core.tool.BitTool._
import rvspeccore.core.RVConfig

object PrivilegeLevel extends ChiselEnum {
  val User       = Value(0.U(2.W))
  val Supervisor = Value(1.U(2.W))
  val Machine    = Value(3.U(2.W))

  def initLevel = Machine
}

class MisaStruct(implicit XLEN: Int) extends Bundle {
  val mxl        = UInt(2.W)           // MXLEN - 1 ~ MXLEN - 2
  val pad        = UInt((XLEN - 28).W) // MXLEN - 3 ~ 26
  val extensions = UInt(26.W)          // 25 ~ 0
}

class MstatusStruct(implicit XLEN: Int) extends Bundle {
  val sd    = UInt(1.W) // MXLEN - 1
  val pad5  = if (XLEN == 64) UInt(20.W) else null
  val mdt   = if (XLEN == 64) UInt(1.W) else null
  val mpelp = if (XLEN == 64) UInt(1.W) else null
  val pad4  = if (XLEN == 64) UInt(1.W) else null
  val mpv   = if (XLEN == 64) UInt(1.W) else null
  val gva   = if (XLEN == 64) UInt(1.W) else null
  val mbe   = if (XLEN == 64) UInt(1.W) else null
  val sbe   = if (XLEN == 64) UInt(1.W) else null
  val sxl   = if (XLEN == 64) UInt(2.W) else null
  val uxl   = if (XLEN == 64) UInt(2.W) else null
  val pad3  = if (XLEN == 64) UInt(7.W) else UInt(6.W)
  val sdt   = UInt(1.W) // 24
  val spelp = UInt(1.W) // 23
  val tsr   = UInt(1.W) // 22
  val tw    = UInt(1.W) // 21
  val tvm   = UInt(1.W) // 20
  val mxr   = UInt(1.W) // 19
  val sum   = UInt(1.W) // 18
  val mprv  = UInt(1.W) // 17
  val xs    = UInt(2.W) // 16 ~ 15
  val fs    = UInt(2.W) // 14 ~ 13
  val mpp   = UInt(2.W) // 12 ~ 11
  val vs    = UInt(2.W) // 10 ~ 9
  val spp   = UInt(1.W) // 8
  val mpie  = UInt(1.W) // 7
  val ube   = UInt(1.W) // 6
  val spie  = UInt(1.W) // 5
  val pad2  = UInt(1.W) // 4
  val mie   = UInt(1.W) // 3
  val pad1  = UInt(1.W) // 2
  val sie   = UInt(1.W) // 1
  val pad0  = UInt(1.W) // 0
}

class MstatushStruct(implicit XLEN: Int) extends Bundle {
  val pad2  = UInt(21.W) // 31 ~ 11
  val mdt   = UInt(1.W)  // 10
  val mpelp = UInt(1.W)  // 9
  val pad1  = UInt(1.W)  // 8
  val mpv   = UInt(1.W)  // 7
  val gva   = UInt(1.W)  // 6
  val mbe   = UInt(1.W)  // 5
  val sbe   = UInt(1.W)  // 4
  val pad0  = UInt(4.W)  // 3 ~ 0
}

class SatpStruct(implicit XLEN: Int) extends Bundle {
  val mode = if (XLEN == 32) UInt(1.W) else UInt(4.W)
  val asid = if (XLEN == 32) UInt(9.W) else UInt(16.W)
  val ppn  = if (XLEN == 32) UInt(22.W) else UInt(44.W)
}

case class CSRInfo(
    addr: UInt,
    width: Option[Int],
    rmask: RVConfig => UInt,
    wmask: RVConfig => UInt,
    wse: Option[RVConfig => UInt => UInt]
) {
  def makeUInt(implicit XLEN: Int) = width match {
    case Some(value) => UInt(value.W)
    case None        => UInt(XLEN.W)
  }
}

object CSRInfo {
  def apply(
      addrStr: String,
      width: Option[Int] = None,
      rmask: RVConfig => UInt = config => Fill(config.XLEN, 1.B),
      wmask: RVConfig => UInt = config => Fill(config.XLEN, 1.B),
      wse: Option[RVConfig => UInt => UInt] = Some(_ => csr => csr)
  ): CSRInfo = {
    new CSRInfo(addrStr.U(12.W), width, rmask, wmask, wse)
  }
}

/** All CSR informations
  *
  *   - riscv-privileged-20211203
  *
  * addr:
  *
  *   - Chapter 2: Control and Status Registers (CSRs)
  *   - 2.2 CSR Listing
  *     - Table 2.1 ~ 2.6
  *
  * width: The `xxx` CSR is a `xxx`-bit register
  */
trait CSRInfos {
  // SideEffect
  val mstatusUpdateSideEffect: Option[RVConfig => UInt => UInt] = Some(implicit config =>
    mstatus => {
      implicit val XLEN = config.XLEN
      val mstatusOld    = WireInit(mstatus.asTypeOf(new MstatusStruct))
      // mstatusOld.mpp := "b11".U
      // if (XLEN == 64){
      //   // FIXME: nutshell 认为u mode 的uxl为全0 存疑 暂时修改参考模型 使其不报错
      //   if(config.CSRMisaExtList.contains('S')){
      //     mstatusOld.sxl := "b10".U
      //   }
      //   if(config.CSRMisaExtList.contains('U')){
      //     mstatusOld.uxl := "b10".U
      //   }
      // }
      // FIXME: 临时mpp只能为M状态 之后要时刻保持其值为能够支持的状态
      // 需要读Config来继续进行 当前三个模式都有 所以这一行要注释掉
      val mstatusNew = Cat(mstatusOld.fs === "b11".U, mstatusOld.asUInt(XLEN - 2, 0))
      mstatusNew
    }
  )

  /* RISC-V unprivileged CSR */

  // - Unprivileged Floating-Point CSRs
  // TODO
  val fflags = CSRInfo("h001")
  val frm    = CSRInfo("h002")
  val fcsr   = CSRInfo("h003")

  // - Unprivileged Vector CSRs
  // TODO
  val vstart = CSRInfo("h008")
  val vxsat  = CSRInfo("h009")
  val vxrm   = CSRInfo("h00A")
  val vcsr   = CSRInfo("h00B")
  val vl     = CSRInfo("hC20")
  val vtype  = CSRInfo("hC21")
  val vlenb  = CSRInfo("hC22")

  // - Unprivileged Zicfiss extension CSR
  // TODO
  val ssp = CSRInfo("h011")

  // - Unprivileged Entropy Source Extension CSR
  // TODO
  val seed = CSRInfo("h015")

  // - Unprivileged Zcmt Extension CSR
  // TODO
  val jvt = CSRInfo("h017")

  // - Unprivileged Counter/Timers
  val cycle       = CSRInfo("hc00")
  val time        = CSRInfo("hc01")
  val instret     = CSRInfo("hc02")
  val hpmcounter  = (3 to 31).map(i => CSRInfo(s"h${(0xc00 + i).toHexString}"))
  val cycleh      = CSRInfo("hc80")
  val timeh       = CSRInfo("hc81")
  val instreth    = CSRInfo("hc82")
  val hpmcounterh = (3 to 31).map(i => CSRInfo(s"h${(0xc80 + i).toHexString}"))

  /* RISC-V supervisor-level CSR */

  // - Supervisor Trap Setup
  // Sstatus Write Mask
  // -------------------------------------------------------
  //    19           9   5     2
  // 0  1100 0000 0001 0010 0010
  // 0  c    0    1    2    2
  // -------------------------------------------------------
  // val sieMask = "h222".U & mideleg
  // val sipMask = "h222".U & mideleg
  // MaskedRegMap(Sstatus, mstatus, sstatusWmask, mstatusUpdateSideEffect, sstatusRmask),
  val sstatus = CSRInfo(
    "h100",
    rmask = config => "hc6122".U(config.XLEN.W) | "h8000000300018000".U,
    wmask = config => "hc6122".U(config.XLEN.W),
    wse = mstatusUpdateSideEffect
  ) // TODO

  // MaskedRegMap(Sie, mie, sieMask, MaskedRegMap.NoSideEffect, sieMask),
  val sie = CSRInfo(
    "h104",
    rmask = config => "h222".U(config.XLEN.W),
    wmask = config => "h222".U(config.XLEN.W)
  ) // TODO
  val stvec      = CSRInfo("h105") // TODO
  val scounteren = CSRInfo("h106") // TODO

  // - Supervisor Configuration
  val senvcfg = CSRInfo("h10A") // TODO

  // - Supervisor Counter Setup
  val scountinhibit = CSRInfo("h120") // TODO

  // - Supervisor Trap Handling
  val sscratch = CSRInfo("h140") // TODO
  val sepc     = CSRInfo("h141") // TODO
  val scause   = CSRInfo("h142") // TODO
  val stval    = CSRInfo("h143") // TODO
  // MaskedRegMap(Sip, mip.asUInt, sipMask, MaskedRegMap.Unwritable, sipMask),
  val sip = CSRInfo(
    "h144",
    rmask = config => "h222".U(config.XLEN.W),
    wmask = config => "h222".U(config.XLEN.W)
  ) // FIXME: h222 is a error impl 忘了为啥说是错误的了
  val scountovf = CSRInfo("hDA0") // TODO

  // - Supervisor Indirect
  val siselect = CSRInfo("h150")                                            // TODO
  val sireg    = (1 to 6).map(i => CSRInfo(s"h${(0x150 + i).toHexString}")) // TODO

  // - Supervisor Protection and Translation
  val satp = CSRInfo("h180") // TODO

  // - Supervisor Timer Compare
  val stimecmp  = CSRInfo("h14D") // TODO
  val stimecmph = CSRInfo("h15D") // TODO

  // - Debug/Trace Registers
  val scontext = CSRInfo("h5A8") // TODO

  // - Supervisor Resource Management Configuration
  val srmcfg = CSRInfo("h181") // TODO

  // - Supervisor State Enable Registers
  val sstateen0 = CSRInfo("h10C") // TODO
  val sstateen1 = CSRInfo("h10D") // TODO
  val sstateen2 = CSRInfo("h10E") // TODO
  val sstateen3 = CSRInfo("h10F") // TODO

  // - Supervisor Control Transfer Records Configuration
  val sctrctl    = CSRInfo("h14E") // TODO
  val sctrstatus = CSRInfo("h14F") // TODO
  val sctrdepth  = CSRInfo("h15F") // TODO

  /* RISC-V hypervisor and VS CSR */
  // TODO

  /* RISC-V machine-level CSR */

  // - Machine Information Registers
  val mvendorid  = CSRInfo("hf11", width = Some(32), wmask = config => 0.U(config.XLEN.W))
  val marchid    = CSRInfo("hf12", wmask = config => 0.U(config.XLEN.W))
  val mimpid     = CSRInfo("hf13", wmask = config => 0.U(config.XLEN.W))
  val mhartid    = CSRInfo("hf14", wmask = config => 0.U(config.XLEN.W))
  val mconfigptr = CSRInfo("hf15", wmask = config => 0.U(config.XLEN.W))

  // - Machine Trap Setup
  val mstatus = CSRInfo(
    "h300",
    rmask = config =>
      if (config.XLEN == 64) "hffff_ffff_ffff_ffff".U(config.XLEN.W)
      else
        "h0000_1888".U(config.XLEN.W) |
          (if (config.extensions.U) "h0022_0040".U(config.XLEN.W) else 0.U(config.XLEN.W)) |
          (if (config.extensions.S) "h007c_0122".U(config.XLEN.W) else 0.U(config.XLEN.W)),
    wmask = config =>
      if (config.XLEN == 64) "hffff_ffff_ffff_ffff".U(config.XLEN.W)
      else
        "h0000_0088".U(config.XLEN.W) |
          (if (config.extensions.U) "h0022_1840".U(config.XLEN.W) else 0.U(config.XLEN.W)) |
          (if (config.extensions.S) "h007c_0122".U(config.XLEN.W) else 0.U(config.XLEN.W)),
    wse = mstatusUpdateSideEffect
  ) // TODO
  val misa = CSRInfo(
    "h301",
    rmask = config => if (config.XLEN == 64) "hc000_0000_03ff_ffff".U(config.XLEN.W) else "hc3ff_ffff".U(config.XLEN.W),
    wmask = config => 0.U(config.XLEN.W)
    // 0.U(config.XLEN.W) |
    //   (if (config.extensions.B) 1.U(config.XLEN.W) << 1 else 0.U(config.XLEN.W)) |
    //   (if (config.extensions.C) 1.U(config.XLEN.W) << 2 else 0.U(config.XLEN.W)) |
    //   (if (config.extensions.M) 1.U(config.XLEN.W) << 12 else 0.U(config.XLEN.W)) |
    //   (if (config.extensions.S) 1.U(config.XLEN.W) << 18 else 0.U(config.XLEN.W)) |
    //   (if (config.extensions.U) 1.U(config.XLEN.W) << 20 else 0.U(config.XLEN.W))
  )
  val medeleg =
    CSRInfo(
      "h302",
      wmask = config => "hbbff".U(config.XLEN.W)
    ) // FIXME: NutShell: medeleg[11] is read-only zero
  val mideleg = CSRInfo(
    "h303",
    wmask = config => "h222".U(config.XLEN.W)
  ) // FIXME: simple impl use nutshell write mask
  val mie = CSRInfo(
    "h304",
    rmask = config =>
      "h0000_0888".U(config.XLEN.W) |
        (if (config.extensions.S) "h0000_0222".U(config.XLEN.W) else 0.U(config.XLEN.W)),
    wmask = config =>
      "h0000_0888".U(config.XLEN.W) |
        (if (config.extensions.S) "h0000_0222".U(config.XLEN.W) else 0.U(config.XLEN.W))
  )
  val mtvec = CSRInfo(
    "h305",
    rmask = config => if (config.XLEN == 64) "hffff_ffff_ffff_fffd".U(config.XLEN.W) else "hffff_fffd".U(config.XLEN.W),
    wmask = config => if (config.XLEN == 64) "hffff_ffff_ffff_fffd".U(config.XLEN.W) else "hffff_fffd".U(config.XLEN.W)
  )
  val mcounteren = CSRInfo("h306") // TODO
  val mstatush = CSRInfo(
    "h310",
    width = Some(32),
    rmask = config =>
      "h0000_0020".U(config.XLEN.W) |
        (if (config.extensions.S) "h0000_0010".U(config.XLEN.W) else 0.U(config.XLEN.W)),
    wmask = config => 0.U(config.XLEN.W)
    // wmask = config => "h0000_0020".U(config.XLEN.W) | (if (config.extensions.S) "h0000_0010".U(config.XLEN.W) else 0.U(config.XLEN.W))
  ) // TODO
  val medelegh = CSRInfo("h312")

  // - Machine Trap Handling
  val mscratch = CSRInfo("h340") // TODO
  val mepc = CSRInfo(
    "h341",
    rmask = config =>
      if (config.XLEN == 64)
        "hffff_ffff_ffff_fffc".U(config.XLEN.W) |
          (if (config.extensions.C) "h0000_0000_0000_0002".U(config.XLEN.W) else 0.U(config.XLEN.W))
      else
        "hffff_fffc".U(config.XLEN.W) |
          (if (config.extensions.C) "h0000_0002".U(config.XLEN.W) else 0.U(config.XLEN.W)),
    wmask = config =>
      if (config.XLEN == 64)
        "hffff_ffff_ffff_fffc".U(config.XLEN.W) |
          (if (config.extensions.C) "h0000_0000_0000_0002".U(config.XLEN.W) else 0.U(config.XLEN.W))
      else
        "hffff_fffc".U(config.XLEN.W) | (if (config.extensions.C) "h0000_0002".U(config.XLEN.W) else 0.U(config.XLEN.W))
  )
  val mcause = CSRInfo("h342") // TODO
  val mtval  = CSRInfo("h343")
  val mip = CSRInfo(
    "h344",
    rmask = config =>
      "h0000_0888".U(config.XLEN.W) |
        (if (config.extensions.S) "h0000_0222".U(config.XLEN.W) else 0.U(config.XLEN.W)),
    wmask = config =>
      "h0000_0888".U(config.XLEN.W) |
        (if (config.extensions.S) "h0000_0222".U(config.XLEN.W) else 0.U(config.XLEN.W))
  )
  val mtinst = CSRInfo("h34A")
  val mtval2 = CSRInfo("h34B")

  // - Machine Indirect
  // TODO
  val miselect = CSRInfo("h350")
  val mireg    = (1 to 6).map(i => CSRInfo(s"h${(0x350 + i).toHexString}"))

  // - Machine Configuration
  val menvcfg  = CSRInfo("h30A") // TODO
  val menvcfgh = CSRInfo("h31A") // TODO
  val mseccfg  = CSRInfo("h747") // TODO
  val mseccfgh = CSRInfo("h757") // TODO

  // - Machine Memory Protection
  val pmpcfg  = (0 to 15).map(i => CSRInfo(s"h${(0x3a0 + i).toHexString}")) // TODO
  val pmpaddr = (0 to 63).map(i => CSRInfo(s"h${(0x3b0 + i).toHexString}")) // TODO

  // - Machine State Enable Registers
  // TODO
  val mstateen0  = CSRInfo("h30C")
  val mstateen1  = CSRInfo("h30D")
  val mstateen2  = CSRInfo("h30E")
  val mstateen3  = CSRInfo("h30F")
  val mstateen0h = CSRInfo("h31C")
  val mstateen1h = CSRInfo("h31D")
  val mstateen2h = CSRInfo("h31E")
  val mstateen3h = CSRInfo("h31F")

  // - Machine Non-Maskable Interrupt Handling
  // TODO
  val mnscratch = CSRInfo("h740")
  val mnepc     = CSRInfo("h741")
  val mncause   = CSRInfo("h742")
  val mnstatus  = CSRInfo("h743")

  // - Machine Counter/Timers
  val mcycle   = CSRInfo("hb00")
  val minstret = CSRInfo("hb02")
  val mhpmcounter = (3 to 31).map(i =>
    CSRInfo(
      s"h${(0xb00 + i).toHexString}",
      rmask = config => 0.U(config.XLEN.W),
      wmask = config => 0.U(config.XLEN.W)
    )
  )
  val mcycleh   = CSRInfo("hb80")
  val minstreth = CSRInfo("hb82")
  val mhpmcounterh = (3 to 31).map(i =>
    CSRInfo(
      s"h${(0xb80 + i).toHexString}",
      rmask = config => 0.U(config.XLEN.W),
      wmask = config => 0.U(config.XLEN.W)
    )
  )

  // - Machine Counter Setup
  val mcountinhibit = CSRInfo("h320")
  // TODO
  val mcyclecfg   = CSRInfo("h321")
  val minstretcfg = CSRInfo("h322")
  val mhpmevent = (3 to 31).map(i =>
    CSRInfo(
      s"h${(0x320 + i).toHexString}",
      rmask = config => 0.U(config.XLEN.W),
      wmask = config => 0.U(config.XLEN.W)
    )
  )
  val mcyclecfgh   = CSRInfo("h721")
  val minstretcfgh = CSRInfo("h722")
  val mhpmeventh = (3 to 31).map(i =>
    CSRInfo(
      s"h${(0x720 + i).toHexString}",
      rmask = config => 0.U(config.XLEN.W),
      wmask = config => 0.U(config.XLEN.W)
    )
  )

  // - Machine Control Transfer Records Configuration
  // TODO
  val mctrctl = CSRInfo("h34E")

  // - Debug/Trace Registers (shared with Debug Mode)
  // TODO
  val tselect  = CSRInfo("h7A0")
  val tdata1   = CSRInfo("h7A1")
  val tdata2   = CSRInfo("h7A2")
  val tdata3   = CSRInfo("h7A3")
  val mcontext = CSRInfo("h7A8")

  // - Debug Mode Registers
  // TODO
  val dcsr      = CSRInfo("h7B0")
  val dpc       = CSRInfo("h7B1")
  val dscratch0 = CSRInfo("h7B2")
  val dscratch1 = CSRInfo("h7B3")

}

object CSRInfos extends CSRInfos

case class CSRInfoSignal(info: CSRInfo, signal: UInt)

class CSR()(implicit config: RVConfig) extends Bundle with IgnoreSeqInBundle {
  implicit val XLEN: Int = config.XLEN

  // make default value for registers
  val mvendorid  = CSRInfos.mvendorid.makeUInt
  val marchid    = CSRInfos.marchid.makeUInt
  val mimpid     = CSRInfos.mimpid.makeUInt
  val mhartid    = CSRInfos.mhartid.makeUInt
  val mconfigptr = CSRInfos.mconfigptr.makeUInt

  val mstatus    = CSRInfos.mstatus.makeUInt
  val misa       = CSRInfos.misa.makeUInt
  val medeleg    = CSRInfos.medeleg.makeUInt
  val mideleg    = CSRInfos.mideleg.makeUInt
  val mie        = CSRInfos.mie.makeUInt
  val mtvec      = CSRInfos.mtvec.makeUInt
  val mcounteren = CSRInfos.mcounteren.makeUInt
  val mstatush   = CSRInfos.mstatush.makeUInt
  val medelegh   = CSRInfos.medelegh.makeUInt

  val mscratch = CSRInfos.mscratch.makeUInt
  val mepc     = CSRInfos.mepc.makeUInt
  val mcause   = CSRInfos.mcause.makeUInt
  val mip      = CSRInfos.mip.makeUInt
  val mtval    = CSRInfos.mtval.makeUInt
  // val mtinst   = CSRInfos.mtinst.makeUInt
  // val mtval2   = CSRInfos.mtval2.makeUInt

  // val miselect = CSRInfos.miselect.makeUInt
  // val mireg    = CSRInfos.mireg.map(_.makeUInt)

  val menvcfg  = CSRInfos.menvcfg.makeUInt
  val menvcfgh = CSRInfos.menvcfgh.makeUInt
  val mseccfg  = CSRInfos.mseccfg.makeUInt
  val mseccfgh = CSRInfos.mseccfgh.makeUInt

  val pmpcfg  = Vec(CSRInfos.pmpcfg.size, CSRInfos.pmpcfg(0).makeUInt)
  val pmpaddr = Vec(CSRInfos.pmpaddr.size, CSRInfos.pmpaddr(0).makeUInt)

  // val mstateen0  = CSRInfos.mstateen0.makeUInt
  // val mstateen1  = CSRInfos.mstateen1.makeUInt
  // val mstateen2  = CSRInfos.mstateen2.makeUInt
  // val mstateen3  = CSRInfos.mstateen3.makeUInt
  // val mstateen0h = CSRInfos.mstateen0h.makeUInt
  // val mstateen1h = CSRInfos.mstateen1h.makeUInt
  // val mstateen2h = CSRInfos.mstateen2h.makeUInt
  // val mstateen3h = CSRInfos.mstateen3h.makeUInt

  // val mnscratch = CSRInfos.mnscratch.makeUInt
  // val mnepc     = CSRInfos.mnepc.makeUInt
  // val mncause   = CSRInfos.mncause.makeUInt
  // val mnstatus  = CSRInfos.mnstatus.makeUInt

  val mcycle       = CSRInfos.mcycle.makeUInt
  val minstret     = CSRInfos.minstret.makeUInt
  val mhpmcounter  = Vec(CSRInfos.mhpmcounter.size, CSRInfos.mhpmcounter(0).makeUInt)
  val mcycleh      = CSRInfos.mcycleh.makeUInt
  val minstreth    = CSRInfos.minstreth.makeUInt
  val mhpmcounterh = Vec(CSRInfos.mhpmcounterh.size, CSRInfos.mhpmcounterh(0).makeUInt)

  val mcountinhibit = CSRInfos.mcountinhibit.makeUInt
  // val mcyclecfg     = CSRInfos.mcyclecfg.makeUInt
  // val minstretcfg   = CSRInfos.minstretcfg.makeUInt
  val mhpmevent = Vec(CSRInfos.mhpmevent.size, CSRInfos.mhpmevent(0).makeUInt)
  // val mcyclecfgh    = CSRInfos.mcyclecfgh.makeUInt
  // val minstretcfgh  = CSRInfos.minstretcfgh.makeUInt
  val mhpmeventh = Vec(CSRInfos.mhpmeventh.size, CSRInfos.mhpmeventh(0).makeUInt)

  // val mctrctl = CSRInfos.mctrctl.makeUInt

  // val tselect = CSRInfos.tselect.makeUInt
  // val tdata1 = CSRInfos.tdata1.makeUInt
  // val tdata2 = CSRInfos.tdata2.makeUInt
  // val tdata3 = CSRInfos.tdata3.makeUInt
  // val mcontext = CSRInfos.mcontext.makeUInt

  // val dcsr = CSRInfos.dcsr.makeUInt
  // val dpc = CSRInfos.dpc.makeUInt
  // val dscratch0 = CSRInfos.dscratch0.makeUInt
  // val dscratch1 = CSRInfos.dscratch1.makeUInt

  val stvec      = CSRInfos.stvec.makeUInt
  val scounteren = CSRInfos.scounteren.makeUInt

  val senvcfg = CSRInfos.senvcfg.makeUInt

  val scountinhibit = CSRInfos.scountinhibit.makeUInt

  val sscratch = CSRInfos.sscratch.makeUInt
  val sepc     = CSRInfos.sepc.makeUInt
  val scause   = CSRInfos.scause.makeUInt
  val stval    = CSRInfos.stval.makeUInt
  // val scountovf = CSRInfos.scountovf.makeUInt

  // val siselect = CSRInfos.siselect.makeUInt
  // val sireg    = CSRInfos.sireg.map(_.makeUInt)

  val satp = CSRInfos.satp.makeUInt

  val stimecmp  = CSRInfos.stimecmp.makeUInt
  val stimecmph = CSRInfos.stimecmph.makeUInt

  // val scontext = CSRInfos.scontext.makeUInt

  // val srmcfg = CSRInfos.srmcfg.makeUInt

  // val sstateen0 = CSRInfos.sstateen0.makeUInt
  // val sstateen1 = CSRInfos.sstateen1.makeUInt
  // val sstateen2 = CSRInfos.sstateen2.makeUInt
  // val sstateen3 = CSRInfos.sstateen3.makeUInt

  // val sctrctl    = CSRInfos.sctrctl.makeUInt
  // val sctrstatus = CSRInfos.sctrstatus.makeUInt
  // val sctrdepth  = CSRInfos.sctrdepth.makeUInt

  // val fflags  = CSRInfos.fflags.makeUInt
  // val frm     = CSRInfos.frm.makeUInt
  // val fcsr    = CSRInfos.fcsr.makeUInt

  // val vstart  = CSRInfos.vstart.makeUInt
  // val vxsat   = CSRInfos.vxsat.makeUInt
  // val vxrm    = CSRInfos.vxrm.makeUInt
  // val vcsr    = CSRInfos.vcsr.makeUInt
  // val vl      = CSRInfos.vl.makeUInt
  // val vtype   = CSRInfos.vtype.makeUInt
  // val vlenb   = CSRInfos.vlenb.makeUInt

  // val ssp = CSRInfos.ssp.makeUInt

  // val seed  = CSRInfos.seed.makeUInt

  // val jvt = CSRInfos.jvt.makeUInt

  /** Table for all CSR signals in this Bundle CSRs in this table can be read or
    * write
    */
  val table = {
    val table_U_32 = List(
      CSRInfoSignal(CSRInfos.cycleh, mcycleh),
      CSRInfoSignal(CSRInfos.instreth, minstreth),
      CSRInfoSignal(CSRInfos.menvcfgh, menvcfgh)
    )
    val table_U = List(
      CSRInfoSignal(CSRInfos.cycle, mcycle),
      CSRInfoSignal(CSRInfos.instret, minstret),
      CSRInfoSignal(CSRInfos.menvcfg, menvcfg),
      CSRInfoSignal(CSRInfos.mcounteren, mcounteren)
    ) ++
      (if (XLEN == 32) table_U_32 else List())

    val table_M_32 = List(
      CSRInfoSignal(CSRInfos.mstatush, mstatush),
      CSRInfoSignal(CSRInfos.mseccfgh, mseccfgh),
      CSRInfoSignal(CSRInfos.mcycleh, mcycleh),
      CSRInfoSignal(CSRInfos.minstreth, minstreth)
    ) ++
      CSRInfos.mhpmcounterh.zip(mhpmcounterh).map { case (info, signal) => CSRInfoSignal(info, signal) } ++
      CSRInfos.mhpmeventh.zip(mhpmeventh).map { case (info, signal) => CSRInfoSignal(info, signal) }
    val table_M = List(
      CSRInfoSignal(CSRInfos.mvendorid, mvendorid),
      CSRInfoSignal(CSRInfos.marchid, marchid),
      CSRInfoSignal(CSRInfos.mimpid, mimpid),
      CSRInfoSignal(CSRInfos.mhartid, mhartid),
      CSRInfoSignal(CSRInfos.mconfigptr, mconfigptr),
      CSRInfoSignal(CSRInfos.mstatus, mstatus),
      CSRInfoSignal(CSRInfos.misa, misa),
      CSRInfoSignal(CSRInfos.mie, mie),
      CSRInfoSignal(CSRInfos.mtvec, mtvec),
      CSRInfoSignal(CSRInfos.mscratch, mscratch),
      CSRInfoSignal(CSRInfos.mepc, mepc),
      CSRInfoSignal(CSRInfos.mcause, mcause),
      CSRInfoSignal(CSRInfos.mip, mip),
      CSRInfoSignal(CSRInfos.mtval, mtval),
      CSRInfoSignal(CSRInfos.mseccfg, mseccfg),
      CSRInfoSignal(CSRInfos.mcycle, mcycle),
      CSRInfoSignal(CSRInfos.minstret, minstret),
      CSRInfoSignal(CSRInfos.mcountinhibit, mcountinhibit)
    ) ++
      CSRInfos.mhpmcounter.zip(mhpmcounter).map { case (info, signal) => CSRInfoSignal(info, signal) } ++
      CSRInfos.mhpmevent.zip(mhpmevent).map { case (info, signal) => CSRInfoSignal(info, signal) } ++
      CSRInfos.pmpcfg.zip(pmpcfg).map { case (info, signal) => CSRInfoSignal(info, signal) } ++
      CSRInfos.pmpaddr.zip(pmpaddr).map { case (info, signal) =>
        CSRInfoSignal(info, signal)
      } ++
      (if (XLEN == 32) table_M_32 else List())

    val table_S_32 = List(
      CSRInfoSignal(CSRInfos.stimecmph, stimecmph)
    )
    val table_S = List(
      CSRInfoSignal(CSRInfos.sstatus, mstatus),
      CSRInfoSignal(CSRInfos.sie, mie),
      CSRInfoSignal(CSRInfos.stvec, stvec),
      CSRInfoSignal(CSRInfos.scounteren, scounteren),
      CSRInfoSignal(CSRInfos.senvcfg, senvcfg),
      CSRInfoSignal(CSRInfos.scountinhibit, scountinhibit),
      CSRInfoSignal(CSRInfos.sscratch, sscratch),
      CSRInfoSignal(CSRInfos.sepc, sepc),
      CSRInfoSignal(CSRInfos.scause, scause),
      CSRInfoSignal(CSRInfos.stval, stval),
      CSRInfoSignal(CSRInfos.sip, mip),
      CSRInfoSignal(CSRInfos.satp, satp),
      CSRInfoSignal(CSRInfos.stimecmp, stimecmp),
      // Ch3.1.8  In systems without S-mode, the medeleg and mideleg registers should not exist.
      CSRInfoSignal(CSRInfos.medeleg, medeleg),
      CSRInfoSignal(CSRInfos.mideleg, mideleg)
    ) ++
      (if (XLEN == 32) table_S_32 else List())

    table_M ++
      (if (config.extensions.U) table_U else List()) ++
      (if (config.extensions.S) table_S else List())
  }

  // the native base integer ISA width
  def MXLEN = MuxLookup(misa.asTypeOf(new MisaStruct).mxl, 32.U(8.W))(
    Seq(
      1.U(2.W) -> 32.U(8.W),
      2.U(2.W) -> 64.U(8.W)
    )
  )
  def SXLEN = if (config.extensions.S)
    MuxLookup(MXLEN, 32.U(8.W))(
      Seq(
        32.U(8.W) -> 32.U(8.W),
        64.U(8.W) -> MuxLookup(mstatus.asTypeOf(new MstatusStruct).sxl, 32.U(8.W))(
          Seq(
            1.U(2.W) -> 32.U(8.W),
            2.U(2.W) -> 64.U(8.W)
          )
        )
      )
    )
  else null
  def UXLEN = if (config.extensions.U)
    MuxLookup(MXLEN, 32.U(8.W))(
      Seq(
        32.U(8.W) -> 32.U(8.W),
        64.U(8.W) -> MuxLookup(mstatus.asTypeOf(new MstatusStruct).uxl, 32.U(8.W))(
          Seq(
            1.U(2.W) -> 32.U(8.W),
            2.U(2.W) -> 64.U(8.W)
          )
        )
      )
    )
  else null
  // the instruction-address alignment constraint the implementation enforces
  def IALIGN = Mux(misa(2), 16.U(8.W), 32.U(8.W))
  // the maximum instruction length supported by an implementation
  def ILEN = 32.U(8.W)

  /** Table for all environment variable in this Bundle
    *
    * These environment variables may be changed when CSR changed.
    */
  def vTable = List(
    MXLEN,
    SXLEN,
    UXLEN,
    IALIGN,
    ILEN
  )
}

object CSR {
  def apply()(implicit config: RVConfig): CSR = new CSR
  def getMisaMxl(xlen: Int): UInt = {
    xlen match {
      case 32  => 1.U << (xlen - 2)
      case 64  => 2.U << (xlen - 2)
      case 128 => 3.U << (xlen - 2)
    }
  }
  def getMisaExt(ext: Char): UInt   = { 1.U << (ext.toInt - 'A'.toInt) }
  def getMisaExtInt(ext: Char): Int = { (ext.toInt - 'A'.toInt) }
  def wireInit()(implicit config: RVConfig): CSR = {
    implicit val XLEN: Int = config.XLEN

    // TODO: finish the sideEffect func
    // Initial the value of CSR Regs

    // TODO: End
    // Set initial value to CSRs
    // CSR Class is just a Bundle, need to transfer to Wire
    val csr = Wire(CSR())

    // mvendorid value 0 means non-commercial implementation
    csr.mvendorid := 0.U
    // marchid allocated globally by RISC-V International 0 means not implementation
    csr.marchid := 0.U
    // mimpid 0 means not implementation
    csr.mimpid     := 0.U
    csr.mhartid    := 0.U
    csr.mconfigptr := 0.U

    csr.mstatus := config.initValue.getOrElse("mstatus", "h0000_1800").U
    val mstatusStruct = csr.mstatus.asTypeOf(new MstatusStruct)
    // val mstatus_change = csr.mstatus.asTypeOf(new MstatusStruct)
    // printf("mpp---------------:%b\n",mstatus_change.mpp)
    // Misa Initial Begin -----------------
    // default: "h8000000000141105".U
    val misaInitVal = getMisaMxl(XLEN) | config.csr.MisaExtList.foldLeft(0.U)((sum, i) => sum | getMisaExt(i))
    csr.misa := misaInitVal
    // Misa Initial End -----------------
    csr.medeleg    := 0.U // 302
    csr.mideleg    := 0.U // 303
    csr.mie        := 0.U // 304
    csr.mtvec      := config.initValue.getOrElse("mtvec", "h0000_0000").U
    csr.mcounteren := 0.U
    csr.mstatush   := 0.U // 310
    csr.medelegh   := 0.U

    csr.mscratch := 0.U
    csr.mepc     := 0.U
    csr.mcause   := 0.U
    csr.mip      := 0.U // 344
    csr.mtval    := 0.U

    csr.menvcfg  := 0.U
    csr.menvcfgh := 0.U
    csr.mseccfg  := 0.U
    csr.mseccfgh := 0.U

    csr.pmpcfg.map(_ := 0.U)
    csr.pmpaddr.map(_ := 0.U)

    csr.mcycle   := 0.U // Warn TODO: NutShell not implemented
    csr.minstret := 0.U
    csr.mhpmcounter.map(_ := 0.U)
    csr.mcycleh   := 0.U
    csr.minstreth := 0.U
    csr.mhpmcounterh.map(_ := 0.U)

    csr.mcountinhibit := 0.U
    csr.mhpmevent.map(_ := 0.U)
    csr.mhpmeventh.map(_ := 0.U)

    // TODO: S Mode modify (if case)
    csr.stvec      := 0.U
    csr.scounteren := 0.U // TODO: Need to modify

    csr.senvcfg := 0.U

    csr.scountinhibit := 0.U

    csr.sscratch := 0.U
    csr.sepc     := 0.U // TODO: Need to modify
    csr.scause   := 0.U
    csr.stval    := 0.U

    csr.satp := 0.U
    // // for test in NutShell
    // // TODO: need a correct if condition
    // if(XLEN == 64){
    //   csr.satp      :="h8000000000080002".U
    // }else{
    //   csr.satp      := 0.U
    // }

    csr.stimecmp  := 0.U
    csr.stimecmph := 0.U

    csr
  }
}

// // TODO: WARL and ....

// object mtvec{
//   def apply()(implicit XLEN: Int): CSR = new CSR
//   def wireInit()(implicit XLEN: Int, config: RVConfig): CSR = {
//     // Volume II Page 29 3.1.7
//     // Value 0: Direct
//     // Value 1: Vectored
//     // Value >=2: Reserved
//     val reg_value  = UInt(0.W)
//   }
// }
// Level | Encoding |       Name       | Abbreviation
//   0   |    00    | User/Application |      U
//   1   |    01    |    Supervisor    |      S
//   2   |    10    |     Reserved     |
//   3   |    11    |     Machine      |      M

class SV39PTE() extends Bundle {
  val reserved = UInt(10.W)
  val ppn      = UInt(44.W)
  val rsw      = UInt(2.W)
  val flag     = UInt(8.W)
}

class PTEFlag() extends Bundle {
  val d = Bool()
  val a = Bool()
  val g = Bool()
  val u = Bool()
  val x = Bool()
  val w = Bool()
  val r = Bool()
  val v = Bool()
}

// TODO: FIXME: Merge to ours tools csr
// NutShell
// io.imemMMU.privilegeMode := privilegeMode
// io.dmemMMU.privilegeMode := Mux(mstatusStruct.mprv.asBool, mstatusStruct.mpp, privilegeMode)
// XiangShan
// tlbBundle.priv.imode := privilegeMode
// tlbBundle.priv.dmode := Mux(debugMode && dcsr.asTypeOf(new DcsrStruct).mprven, ModeM, Mux(mstatusStruct.mprv.asBool, mstatusStruct.mpp, privilegeMode))
// 当前还没有Debug Mode 因此按照NutShell 来讲 我认为是一致的

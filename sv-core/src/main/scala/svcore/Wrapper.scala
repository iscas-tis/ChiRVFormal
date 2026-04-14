package svcore

import chisel3._
import chisel3.util._
import chisel3.experimental._
import rvspeccore.core._
import rvspeccore.checker._
import rvspeccore.core.spec.instset.csr._
import rvspeccore.core.spec.Inst

class CSRWrapperIO(implicit config: RVConfig) extends Bundle {
  implicit val XLEN: Int = config.XLEN

  val mvendorid  = CSRInfos.mvendorid.makeUInt
  val marchid    = CSRInfos.marchid.makeUInt
  val mimpid     = CSRInfos.mimpid.makeUInt
  val mhartid    = CSRInfos.mhartid.makeUInt
  val mconfigptr = CSRInfos.mconfigptr.makeUInt

  val mstatus    = CSRInfos.mstatus.makeUInt
  val misa       = CSRInfos.misa.makeUInt
  val medeleg    = if (config.extensions.S) Some(CSRInfos.medeleg.makeUInt) else None
  val mideleg    = if (config.extensions.S) Some(CSRInfos.mideleg.makeUInt) else None
  val mie        = CSRInfos.mie.makeUInt
  val mtvec      = CSRInfos.mtvec.makeUInt
  val mcounteren = if (config.extensions.U) Some(CSRInfos.mcounteren.makeUInt) else None
  val mstatush   = if (XLEN == 32) Some(CSRInfos.mstatush.makeUInt) else None
  val medelegh   = if (config.extensions.S && XLEN == 32) Some(CSRInfos.medelegh.makeUInt) else None

  val mscratch = CSRInfos.mscratch.makeUInt
  val mepc     = CSRInfos.mepc.makeUInt
  val mcause   = CSRInfos.mcause.makeUInt
  val mip      = CSRInfos.mip.makeUInt
  val mtval    = CSRInfos.mtval.makeUInt

  val menvcfg  = if (config.extensions.U) Some(CSRInfos.menvcfg.makeUInt) else None
  val menvcfgh = if (config.extensions.U && XLEN == 32) Some(CSRInfos.menvcfgh.makeUInt) else None
  val mseccfg  = CSRInfos.mseccfg.makeUInt
  val mseccfgh = if (XLEN == 32) Some(CSRInfos.mseccfgh.makeUInt) else None

  val pmpcfg0   = CSRInfos.pmpcfg(0).makeUInt
  val pmpcfg1   = CSRInfos.pmpcfg(1).makeUInt
  val pmpcfg2   = CSRInfos.pmpcfg(2).makeUInt
  val pmpcfg3   = CSRInfos.pmpcfg(3).makeUInt
  val pmpcfg4   = CSRInfos.pmpcfg(4).makeUInt
  val pmpcfg5   = CSRInfos.pmpcfg(5).makeUInt
  val pmpcfg6   = CSRInfos.pmpcfg(6).makeUInt
  val pmpcfg7   = CSRInfos.pmpcfg(7).makeUInt
  val pmpcfg8   = CSRInfos.pmpcfg(8).makeUInt
  val pmpcfg9   = CSRInfos.pmpcfg(9).makeUInt
  val pmpcfg10  = CSRInfos.pmpcfg(10).makeUInt
  val pmpcfg11  = CSRInfos.pmpcfg(11).makeUInt
  val pmpcfg12  = CSRInfos.pmpcfg(12).makeUInt
  val pmpcfg13  = CSRInfos.pmpcfg(13).makeUInt
  val pmpcfg14  = CSRInfos.pmpcfg(14).makeUInt
  val pmpcfg15  = CSRInfos.pmpcfg(15).makeUInt
  val pmpaddr0  = CSRInfos.pmpaddr(0).makeUInt
  val pmpaddr1  = CSRInfos.pmpaddr(1).makeUInt
  val pmpaddr2  = CSRInfos.pmpaddr(2).makeUInt
  val pmpaddr3  = CSRInfos.pmpaddr(3).makeUInt
  val pmpaddr4  = CSRInfos.pmpaddr(4).makeUInt
  val pmpaddr5  = CSRInfos.pmpaddr(5).makeUInt
  val pmpaddr6  = CSRInfos.pmpaddr(6).makeUInt
  val pmpaddr7  = CSRInfos.pmpaddr(7).makeUInt
  val pmpaddr8  = CSRInfos.pmpaddr(8).makeUInt
  val pmpaddr9  = CSRInfos.pmpaddr(9).makeUInt
  val pmpaddr10 = CSRInfos.pmpaddr(10).makeUInt
  val pmpaddr11 = CSRInfos.pmpaddr(11).makeUInt
  val pmpaddr12 = CSRInfos.pmpaddr(12).makeUInt
  val pmpaddr13 = CSRInfos.pmpaddr(13).makeUInt
  val pmpaddr14 = CSRInfos.pmpaddr(14).makeUInt
  val pmpaddr15 = CSRInfos.pmpaddr(15).makeUInt
  val pmpaddr16 = CSRInfos.pmpaddr(16).makeUInt
  val pmpaddr17 = CSRInfos.pmpaddr(17).makeUInt
  val pmpaddr18 = CSRInfos.pmpaddr(18).makeUInt
  val pmpaddr19 = CSRInfos.pmpaddr(19).makeUInt
  val pmpaddr20 = CSRInfos.pmpaddr(20).makeUInt
  val pmpaddr21 = CSRInfos.pmpaddr(21).makeUInt
  val pmpaddr22 = CSRInfos.pmpaddr(22).makeUInt
  val pmpaddr23 = CSRInfos.pmpaddr(23).makeUInt
  val pmpaddr24 = CSRInfos.pmpaddr(24).makeUInt
  val pmpaddr25 = CSRInfos.pmpaddr(25).makeUInt
  val pmpaddr26 = CSRInfos.pmpaddr(26).makeUInt
  val pmpaddr27 = CSRInfos.pmpaddr(27).makeUInt
  val pmpaddr28 = CSRInfos.pmpaddr(28).makeUInt
  val pmpaddr29 = CSRInfos.pmpaddr(29).makeUInt
  val pmpaddr30 = CSRInfos.pmpaddr(30).makeUInt
  val pmpaddr31 = CSRInfos.pmpaddr(31).makeUInt
  val pmpaddr32 = CSRInfos.pmpaddr(32).makeUInt
  val pmpaddr33 = CSRInfos.pmpaddr(33).makeUInt
  val pmpaddr34 = CSRInfos.pmpaddr(34).makeUInt
  val pmpaddr35 = CSRInfos.pmpaddr(35).makeUInt
  val pmpaddr36 = CSRInfos.pmpaddr(36).makeUInt
  val pmpaddr37 = CSRInfos.pmpaddr(37).makeUInt
  val pmpaddr38 = CSRInfos.pmpaddr(38).makeUInt
  val pmpaddr39 = CSRInfos.pmpaddr(39).makeUInt
  val pmpaddr40 = CSRInfos.pmpaddr(40).makeUInt
  val pmpaddr41 = CSRInfos.pmpaddr(41).makeUInt
  val pmpaddr42 = CSRInfos.pmpaddr(42).makeUInt
  val pmpaddr43 = CSRInfos.pmpaddr(43).makeUInt
  val pmpaddr44 = CSRInfos.pmpaddr(44).makeUInt
  val pmpaddr45 = CSRInfos.pmpaddr(45).makeUInt
  val pmpaddr46 = CSRInfos.pmpaddr(46).makeUInt
  val pmpaddr47 = CSRInfos.pmpaddr(47).makeUInt
  val pmpaddr48 = CSRInfos.pmpaddr(48).makeUInt
  val pmpaddr49 = CSRInfos.pmpaddr(49).makeUInt
  val pmpaddr50 = CSRInfos.pmpaddr(50).makeUInt
  val pmpaddr51 = CSRInfos.pmpaddr(51).makeUInt
  val pmpaddr52 = CSRInfos.pmpaddr(52).makeUInt
  val pmpaddr53 = CSRInfos.pmpaddr(53).makeUInt
  val pmpaddr54 = CSRInfos.pmpaddr(54).makeUInt
  val pmpaddr55 = CSRInfos.pmpaddr(55).makeUInt
  val pmpaddr56 = CSRInfos.pmpaddr(56).makeUInt
  val pmpaddr57 = CSRInfos.pmpaddr(57).makeUInt
  val pmpaddr58 = CSRInfos.pmpaddr(58).makeUInt
  val pmpaddr59 = CSRInfos.pmpaddr(59).makeUInt
  val pmpaddr60 = CSRInfos.pmpaddr(60).makeUInt
  val pmpaddr61 = CSRInfos.pmpaddr(61).makeUInt
  val pmpaddr62 = CSRInfos.pmpaddr(62).makeUInt
  val pmpaddr63 = CSRInfos.pmpaddr(63).makeUInt

  val mcycle         = CSRInfos.mcycle.makeUInt
  val minstret       = CSRInfos.minstret.makeUInt
  val mhpmcounter3   = CSRInfos.mhpmcounter(0).makeUInt
  val mhpmcounter4   = CSRInfos.mhpmcounter(1).makeUInt
  val mhpmcounter5   = CSRInfos.mhpmcounter(2).makeUInt
  val mhpmcounter6   = CSRInfos.mhpmcounter(3).makeUInt
  val mhpmcounter7   = CSRInfos.mhpmcounter(4).makeUInt
  val mhpmcounter8   = CSRInfos.mhpmcounter(5).makeUInt
  val mhpmcounter9   = CSRInfos.mhpmcounter(6).makeUInt
  val mhpmcounter10  = CSRInfos.mhpmcounter(7).makeUInt
  val mhpmcounter11  = CSRInfos.mhpmcounter(8).makeUInt
  val mhpmcounter12  = CSRInfos.mhpmcounter(9).makeUInt
  val mhpmcounter13  = CSRInfos.mhpmcounter(10).makeUInt
  val mhpmcounter14  = CSRInfos.mhpmcounter(11).makeUInt
  val mhpmcounter15  = CSRInfos.mhpmcounter(12).makeUInt
  val mhpmcounter16  = CSRInfos.mhpmcounter(13).makeUInt
  val mhpmcounter17  = CSRInfos.mhpmcounter(14).makeUInt
  val mhpmcounter18  = CSRInfos.mhpmcounter(15).makeUInt
  val mhpmcounter19  = CSRInfos.mhpmcounter(16).makeUInt
  val mhpmcounter20  = CSRInfos.mhpmcounter(17).makeUInt
  val mhpmcounter21  = CSRInfos.mhpmcounter(18).makeUInt
  val mhpmcounter22  = CSRInfos.mhpmcounter(19).makeUInt
  val mhpmcounter23  = CSRInfos.mhpmcounter(20).makeUInt
  val mhpmcounter24  = CSRInfos.mhpmcounter(21).makeUInt
  val mhpmcounter25  = CSRInfos.mhpmcounter(22).makeUInt
  val mhpmcounter26  = CSRInfos.mhpmcounter(23).makeUInt
  val mhpmcounter27  = CSRInfos.mhpmcounter(24).makeUInt
  val mhpmcounter28  = CSRInfos.mhpmcounter(25).makeUInt
  val mhpmcounter29  = CSRInfos.mhpmcounter(26).makeUInt
  val mhpmcounter30  = CSRInfos.mhpmcounter(27).makeUInt
  val mhpmcounter31  = CSRInfos.mhpmcounter(28).makeUInt
  val mcycleh        = if (XLEN == 32) Some(CSRInfos.mcycleh.makeUInt) else None
  val minstreth      = if (XLEN == 32) Some(CSRInfos.minstreth.makeUInt) else None
  val mhpmcounter3h  = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(0).makeUInt) else None
  val mhpmcounter4h  = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(1).makeUInt) else None
  val mhpmcounter5h  = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(2).makeUInt) else None
  val mhpmcounter6h  = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(3).makeUInt) else None
  val mhpmcounter7h  = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(4).makeUInt) else None
  val mhpmcounter8h  = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(5).makeUInt) else None
  val mhpmcounter9h  = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(6).makeUInt) else None
  val mhpmcounter10h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(7).makeUInt) else None
  val mhpmcounter11h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(8).makeUInt) else None
  val mhpmcounter12h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(9).makeUInt) else None
  val mhpmcounter13h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(10).makeUInt) else None
  val mhpmcounter14h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(11).makeUInt) else None
  val mhpmcounter15h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(12).makeUInt) else None
  val mhpmcounter16h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(13).makeUInt) else None
  val mhpmcounter17h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(14).makeUInt) else None
  val mhpmcounter18h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(15).makeUInt) else None
  val mhpmcounter19h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(16).makeUInt) else None
  val mhpmcounter20h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(17).makeUInt) else None
  val mhpmcounter21h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(18).makeUInt) else None
  val mhpmcounter22h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(19).makeUInt) else None
  val mhpmcounter23h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(20).makeUInt) else None
  val mhpmcounter24h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(21).makeUInt) else None
  val mhpmcounter25h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(22).makeUInt) else None
  val mhpmcounter26h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(23).makeUInt) else None
  val mhpmcounter27h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(24).makeUInt) else None
  val mhpmcounter28h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(25).makeUInt) else None
  val mhpmcounter29h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(26).makeUInt) else None
  val mhpmcounter30h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(27).makeUInt) else None
  val mhpmcounter31h = if (XLEN == 32) Some(CSRInfos.mhpmcounterh(28).makeUInt) else None

  val mcountinhibit = CSRInfos.mcountinhibit.makeUInt
  val mhpmevent3    = CSRInfos.mhpmevent(0).makeUInt
  val mhpmevent4    = CSRInfos.mhpmevent(1).makeUInt
  val mhpmevent5    = CSRInfos.mhpmevent(2).makeUInt
  val mhpmevent6    = CSRInfos.mhpmevent(3).makeUInt
  val mhpmevent7    = CSRInfos.mhpmevent(4).makeUInt
  val mhpmevent8    = CSRInfos.mhpmevent(5).makeUInt
  val mhpmevent9    = CSRInfos.mhpmevent(6).makeUInt
  val mhpmevent10   = CSRInfos.mhpmevent(7).makeUInt
  val mhpmevent11   = CSRInfos.mhpmevent(8).makeUInt
  val mhpmevent12   = CSRInfos.mhpmevent(9).makeUInt
  val mhpmevent13   = CSRInfos.mhpmevent(10).makeUInt
  val mhpmevent14   = CSRInfos.mhpmevent(11).makeUInt
  val mhpmevent15   = CSRInfos.mhpmevent(12).makeUInt
  val mhpmevent16   = CSRInfos.mhpmevent(13).makeUInt
  val mhpmevent17   = CSRInfos.mhpmevent(14).makeUInt
  val mhpmevent18   = CSRInfos.mhpmevent(15).makeUInt
  val mhpmevent19   = CSRInfos.mhpmevent(16).makeUInt
  val mhpmevent20   = CSRInfos.mhpmevent(17).makeUInt
  val mhpmevent21   = CSRInfos.mhpmevent(18).makeUInt
  val mhpmevent22   = CSRInfos.mhpmevent(19).makeUInt
  val mhpmevent23   = CSRInfos.mhpmevent(20).makeUInt
  val mhpmevent24   = CSRInfos.mhpmevent(21).makeUInt
  val mhpmevent25   = CSRInfos.mhpmevent(22).makeUInt
  val mhpmevent26   = CSRInfos.mhpmevent(23).makeUInt
  val mhpmevent27   = CSRInfos.mhpmevent(24).makeUInt
  val mhpmevent28   = CSRInfos.mhpmevent(25).makeUInt
  val mhpmevent29   = CSRInfos.mhpmevent(26).makeUInt
  val mhpmevent30   = CSRInfos.mhpmevent(27).makeUInt
  val mhpmevent31   = CSRInfos.mhpmevent(28).makeUInt
  val mhpmevent3h   = if (XLEN == 32) Some(CSRInfos.mhpmeventh(0).makeUInt) else None
  val mhpmevent4h   = if (XLEN == 32) Some(CSRInfos.mhpmeventh(1).makeUInt) else None
  val mhpmevent5h   = if (XLEN == 32) Some(CSRInfos.mhpmeventh(2).makeUInt) else None
  val mhpmevent6h   = if (XLEN == 32) Some(CSRInfos.mhpmeventh(3).makeUInt) else None
  val mhpmevent7h   = if (XLEN == 32) Some(CSRInfos.mhpmeventh(4).makeUInt) else None
  val mhpmevent8h   = if (XLEN == 32) Some(CSRInfos.mhpmeventh(5).makeUInt) else None
  val mhpmevent9h   = if (XLEN == 32) Some(CSRInfos.mhpmeventh(6).makeUInt) else None
  val mhpmevent10h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(7).makeUInt) else None
  val mhpmevent11h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(8).makeUInt) else None
  val mhpmevent12h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(9).makeUInt) else None
  val mhpmevent13h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(10).makeUInt) else None
  val mhpmevent14h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(11).makeUInt) else None
  val mhpmevent15h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(12).makeUInt) else None
  val mhpmevent16h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(13).makeUInt) else None
  val mhpmevent17h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(14).makeUInt) else None
  val mhpmevent18h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(15).makeUInt) else None
  val mhpmevent19h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(16).makeUInt) else None
  val mhpmevent20h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(17).makeUInt) else None
  val mhpmevent21h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(18).makeUInt) else None
  val mhpmevent22h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(19).makeUInt) else None
  val mhpmevent23h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(20).makeUInt) else None
  val mhpmevent24h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(21).makeUInt) else None
  val mhpmevent25h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(22).makeUInt) else None
  val mhpmevent26h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(23).makeUInt) else None
  val mhpmevent27h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(24).makeUInt) else None
  val mhpmevent28h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(25).makeUInt) else None
  val mhpmevent29h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(26).makeUInt) else None
  val mhpmevent30h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(27).makeUInt) else None
  val mhpmevent31h  = if (XLEN == 32) Some(CSRInfos.mhpmeventh(28).makeUInt) else None

  val stvec      = if (config.extensions.S) Some(CSRInfos.stvec.makeUInt) else None
  val scounteren = if (config.extensions.S) Some(CSRInfos.scounteren.makeUInt) else None

  val senvcfg = if (config.extensions.S) Some(CSRInfos.senvcfg.makeUInt) else None

  val scountinhibit = if (config.extensions.S) Some(CSRInfos.scountinhibit.makeUInt) else None

  val sscratch = if (config.extensions.S) Some(CSRInfos.sscratch.makeUInt) else None
  val sepc     = if (config.extensions.S) Some(CSRInfos.sepc.makeUInt) else None
  val scause   = if (config.extensions.S) Some(CSRInfos.scause.makeUInt) else None
  val stval    = if (config.extensions.S) Some(CSRInfos.stval.makeUInt) else None

  val satp = if (config.extensions.S) Some(CSRInfos.satp.makeUInt) else None

  val stimecmp  = if (config.extensions.S) Some(CSRInfos.stimecmp.makeUInt) else None
  val stimecmph = if (config.extensions.S && XLEN == 32) Some(CSRInfos.stimecmph.makeUInt) else None

  def toCSRWire(): CSR = {
    val csr = Wire(CSR())
    csr.mvendorid  := mvendorid
    csr.marchid    := marchid
    csr.mimpid     := mimpid
    csr.mhartid    := mhartid
    csr.mconfigptr := mconfigptr

    csr.mstatus    := mstatus
    csr.misa       := misa
    csr.medeleg    := medeleg.getOrElse(0.U)
    csr.mideleg    := mideleg.getOrElse(0.U)
    csr.mie        := mie
    csr.mtvec      := mtvec
    csr.mcounteren := mcounteren.getOrElse(0.U)
    csr.mstatush   := mstatush.getOrElse(0.U)
    csr.medelegh   := medelegh.getOrElse(0.U)

    csr.mscratch := mscratch
    csr.mepc     := mepc
    csr.mcause   := mcause
    csr.mip      := mip
    csr.mtval    := mtval

    csr.menvcfg  := menvcfg.getOrElse(0.U)
    csr.menvcfgh := menvcfgh.getOrElse(0.U)
    csr.mseccfg  := mseccfg
    csr.mseccfgh := mseccfgh.getOrElse(0.U)

    csr.pmpcfg(0)   := pmpcfg0
    csr.pmpcfg(1)   := pmpcfg1
    csr.pmpcfg(2)   := pmpcfg2
    csr.pmpcfg(3)   := pmpcfg3
    csr.pmpcfg(4)   := pmpcfg4
    csr.pmpcfg(5)   := pmpcfg5
    csr.pmpcfg(6)   := pmpcfg6
    csr.pmpcfg(7)   := pmpcfg7
    csr.pmpcfg(8)   := pmpcfg8
    csr.pmpcfg(9)   := pmpcfg9
    csr.pmpcfg(10)  := pmpcfg10
    csr.pmpcfg(11)  := pmpcfg11
    csr.pmpcfg(12)  := pmpcfg12
    csr.pmpcfg(13)  := pmpcfg13
    csr.pmpcfg(14)  := pmpcfg14
    csr.pmpcfg(15)  := pmpcfg15
    csr.pmpaddr(0)  := pmpaddr0
    csr.pmpaddr(1)  := pmpaddr1
    csr.pmpaddr(2)  := pmpaddr2
    csr.pmpaddr(3)  := pmpaddr3
    csr.pmpaddr(4)  := pmpaddr4
    csr.pmpaddr(5)  := pmpaddr5
    csr.pmpaddr(6)  := pmpaddr6
    csr.pmpaddr(7)  := pmpaddr7
    csr.pmpaddr(8)  := pmpaddr8
    csr.pmpaddr(9)  := pmpaddr9
    csr.pmpaddr(10) := pmpaddr10
    csr.pmpaddr(11) := pmpaddr11
    csr.pmpaddr(12) := pmpaddr12
    csr.pmpaddr(13) := pmpaddr13
    csr.pmpaddr(14) := pmpaddr14
    csr.pmpaddr(15) := pmpaddr15
    csr.pmpaddr(16) := pmpaddr16
    csr.pmpaddr(17) := pmpaddr17
    csr.pmpaddr(18) := pmpaddr18
    csr.pmpaddr(19) := pmpaddr19
    csr.pmpaddr(20) := pmpaddr20
    csr.pmpaddr(21) := pmpaddr21
    csr.pmpaddr(22) := pmpaddr22
    csr.pmpaddr(23) := pmpaddr23
    csr.pmpaddr(24) := pmpaddr24
    csr.pmpaddr(25) := pmpaddr25
    csr.pmpaddr(26) := pmpaddr26
    csr.pmpaddr(27) := pmpaddr27
    csr.pmpaddr(28) := pmpaddr28
    csr.pmpaddr(29) := pmpaddr29
    csr.pmpaddr(30) := pmpaddr30
    csr.pmpaddr(31) := pmpaddr31
    csr.pmpaddr(32) := pmpaddr32
    csr.pmpaddr(33) := pmpaddr33
    csr.pmpaddr(34) := pmpaddr34
    csr.pmpaddr(35) := pmpaddr35
    csr.pmpaddr(36) := pmpaddr36
    csr.pmpaddr(37) := pmpaddr37
    csr.pmpaddr(38) := pmpaddr38
    csr.pmpaddr(39) := pmpaddr39
    csr.pmpaddr(40) := pmpaddr40
    csr.pmpaddr(41) := pmpaddr41
    csr.pmpaddr(42) := pmpaddr42
    csr.pmpaddr(43) := pmpaddr43
    csr.pmpaddr(44) := pmpaddr44
    csr.pmpaddr(45) := pmpaddr45
    csr.pmpaddr(46) := pmpaddr46
    csr.pmpaddr(47) := pmpaddr47
    csr.pmpaddr(48) := pmpaddr48
    csr.pmpaddr(49) := pmpaddr49
    csr.pmpaddr(50) := pmpaddr50
    csr.pmpaddr(51) := pmpaddr51
    csr.pmpaddr(52) := pmpaddr52
    csr.pmpaddr(53) := pmpaddr53
    csr.pmpaddr(54) := pmpaddr54
    csr.pmpaddr(55) := pmpaddr55
    csr.pmpaddr(56) := pmpaddr56
    csr.pmpaddr(57) := pmpaddr57
    csr.pmpaddr(58) := pmpaddr58
    csr.pmpaddr(59) := pmpaddr59
    csr.pmpaddr(60) := pmpaddr60
    csr.pmpaddr(61) := pmpaddr61
    csr.pmpaddr(62) := pmpaddr62
    csr.pmpaddr(63) := pmpaddr63

    csr.mcycle           := mcycle
    csr.minstret         := minstret
    csr.mhpmcounter(0)   := mhpmcounter3
    csr.mhpmcounter(1)   := mhpmcounter4
    csr.mhpmcounter(2)   := mhpmcounter5
    csr.mhpmcounter(3)   := mhpmcounter6
    csr.mhpmcounter(4)   := mhpmcounter7
    csr.mhpmcounter(5)   := mhpmcounter8
    csr.mhpmcounter(6)   := mhpmcounter9
    csr.mhpmcounter(7)   := mhpmcounter10
    csr.mhpmcounter(8)   := mhpmcounter11
    csr.mhpmcounter(9)   := mhpmcounter12
    csr.mhpmcounter(10)  := mhpmcounter13
    csr.mhpmcounter(11)  := mhpmcounter14
    csr.mhpmcounter(12)  := mhpmcounter15
    csr.mhpmcounter(13)  := mhpmcounter16
    csr.mhpmcounter(14)  := mhpmcounter17
    csr.mhpmcounter(15)  := mhpmcounter18
    csr.mhpmcounter(16)  := mhpmcounter19
    csr.mhpmcounter(17)  := mhpmcounter20
    csr.mhpmcounter(18)  := mhpmcounter21
    csr.mhpmcounter(19)  := mhpmcounter22
    csr.mhpmcounter(20)  := mhpmcounter23
    csr.mhpmcounter(21)  := mhpmcounter24
    csr.mhpmcounter(22)  := mhpmcounter25
    csr.mhpmcounter(23)  := mhpmcounter26
    csr.mhpmcounter(24)  := mhpmcounter27
    csr.mhpmcounter(25)  := mhpmcounter28
    csr.mhpmcounter(26)  := mhpmcounter29
    csr.mhpmcounter(27)  := mhpmcounter30
    csr.mhpmcounter(28)  := mhpmcounter31
    csr.mcycleh          := mcycleh.getOrElse(0.U)
    csr.minstreth        := minstreth.getOrElse(0.U)
    csr.mhpmcounterh(0)  := mhpmcounter3h.getOrElse(0.U)
    csr.mhpmcounterh(1)  := mhpmcounter4h.getOrElse(0.U)
    csr.mhpmcounterh(2)  := mhpmcounter5h.getOrElse(0.U)
    csr.mhpmcounterh(3)  := mhpmcounter6h.getOrElse(0.U)
    csr.mhpmcounterh(4)  := mhpmcounter7h.getOrElse(0.U)
    csr.mhpmcounterh(5)  := mhpmcounter8h.getOrElse(0.U)
    csr.mhpmcounterh(6)  := mhpmcounter9h.getOrElse(0.U)
    csr.mhpmcounterh(7)  := mhpmcounter10h.getOrElse(0.U)
    csr.mhpmcounterh(8)  := mhpmcounter11h.getOrElse(0.U)
    csr.mhpmcounterh(9)  := mhpmcounter12h.getOrElse(0.U)
    csr.mhpmcounterh(10) := mhpmcounter13h.getOrElse(0.U)
    csr.mhpmcounterh(11) := mhpmcounter14h.getOrElse(0.U)
    csr.mhpmcounterh(12) := mhpmcounter15h.getOrElse(0.U)
    csr.mhpmcounterh(13) := mhpmcounter16h.getOrElse(0.U)
    csr.mhpmcounterh(14) := mhpmcounter17h.getOrElse(0.U)
    csr.mhpmcounterh(15) := mhpmcounter18h.getOrElse(0.U)
    csr.mhpmcounterh(16) := mhpmcounter19h.getOrElse(0.U)
    csr.mhpmcounterh(17) := mhpmcounter20h.getOrElse(0.U)
    csr.mhpmcounterh(18) := mhpmcounter21h.getOrElse(0.U)
    csr.mhpmcounterh(19) := mhpmcounter22h.getOrElse(0.U)
    csr.mhpmcounterh(20) := mhpmcounter23h.getOrElse(0.U)
    csr.mhpmcounterh(21) := mhpmcounter24h.getOrElse(0.U)
    csr.mhpmcounterh(22) := mhpmcounter25h.getOrElse(0.U)
    csr.mhpmcounterh(23) := mhpmcounter26h.getOrElse(0.U)
    csr.mhpmcounterh(24) := mhpmcounter27h.getOrElse(0.U)
    csr.mhpmcounterh(25) := mhpmcounter28h.getOrElse(0.U)
    csr.mhpmcounterh(26) := mhpmcounter29h.getOrElse(0.U)
    csr.mhpmcounterh(27) := mhpmcounter30h.getOrElse(0.U)
    csr.mhpmcounterh(28) := mhpmcounter31h.getOrElse(0.U)

    csr.mcountinhibit  := mcountinhibit
    csr.mhpmevent(0)   := mhpmevent3
    csr.mhpmevent(1)   := mhpmevent4
    csr.mhpmevent(2)   := mhpmevent5
    csr.mhpmevent(3)   := mhpmevent6
    csr.mhpmevent(4)   := mhpmevent7
    csr.mhpmevent(5)   := mhpmevent8
    csr.mhpmevent(6)   := mhpmevent9
    csr.mhpmevent(7)   := mhpmevent10
    csr.mhpmevent(8)   := mhpmevent11
    csr.mhpmevent(9)   := mhpmevent12
    csr.mhpmevent(10)  := mhpmevent13
    csr.mhpmevent(11)  := mhpmevent14
    csr.mhpmevent(12)  := mhpmevent15
    csr.mhpmevent(13)  := mhpmevent16
    csr.mhpmevent(14)  := mhpmevent17
    csr.mhpmevent(15)  := mhpmevent18
    csr.mhpmevent(16)  := mhpmevent19
    csr.mhpmevent(17)  := mhpmevent20
    csr.mhpmevent(18)  := mhpmevent21
    csr.mhpmevent(19)  := mhpmevent22
    csr.mhpmevent(20)  := mhpmevent23
    csr.mhpmevent(21)  := mhpmevent24
    csr.mhpmevent(22)  := mhpmevent25
    csr.mhpmevent(23)  := mhpmevent26
    csr.mhpmevent(24)  := mhpmevent27
    csr.mhpmevent(25)  := mhpmevent28
    csr.mhpmevent(26)  := mhpmevent29
    csr.mhpmevent(27)  := mhpmevent30
    csr.mhpmevent(28)  := mhpmevent31
    csr.mhpmeventh(0)  := mhpmevent3h.getOrElse(0.U)
    csr.mhpmeventh(1)  := mhpmevent4h.getOrElse(0.U)
    csr.mhpmeventh(2)  := mhpmevent5h.getOrElse(0.U)
    csr.mhpmeventh(3)  := mhpmevent6h.getOrElse(0.U)
    csr.mhpmeventh(4)  := mhpmevent7h.getOrElse(0.U)
    csr.mhpmeventh(5)  := mhpmevent8h.getOrElse(0.U)
    csr.mhpmeventh(6)  := mhpmevent9h.getOrElse(0.U)
    csr.mhpmeventh(7)  := mhpmevent10h.getOrElse(0.U)
    csr.mhpmeventh(8)  := mhpmevent11h.getOrElse(0.U)
    csr.mhpmeventh(9)  := mhpmevent12h.getOrElse(0.U)
    csr.mhpmeventh(10) := mhpmevent13h.getOrElse(0.U)
    csr.mhpmeventh(11) := mhpmevent14h.getOrElse(0.U)
    csr.mhpmeventh(12) := mhpmevent15h.getOrElse(0.U)
    csr.mhpmeventh(13) := mhpmevent16h.getOrElse(0.U)
    csr.mhpmeventh(14) := mhpmevent17h.getOrElse(0.U)
    csr.mhpmeventh(15) := mhpmevent18h.getOrElse(0.U)
    csr.mhpmeventh(16) := mhpmevent19h.getOrElse(0.U)
    csr.mhpmeventh(17) := mhpmevent20h.getOrElse(0.U)
    csr.mhpmeventh(18) := mhpmevent21h.getOrElse(0.U)
    csr.mhpmeventh(19) := mhpmevent22h.getOrElse(0.U)
    csr.mhpmeventh(20) := mhpmevent23h.getOrElse(0.U)
    csr.mhpmeventh(21) := mhpmevent24h.getOrElse(0.U)
    csr.mhpmeventh(22) := mhpmevent25h.getOrElse(0.U)
    csr.mhpmeventh(23) := mhpmevent26h.getOrElse(0.U)
    csr.mhpmeventh(24) := mhpmevent27h.getOrElse(0.U)
    csr.mhpmeventh(25) := mhpmevent28h.getOrElse(0.U)
    csr.mhpmeventh(26) := mhpmevent29h.getOrElse(0.U)
    csr.mhpmeventh(27) := mhpmevent30h.getOrElse(0.U)
    csr.mhpmeventh(28) := mhpmevent31h.getOrElse(0.U)

    csr.stvec      := stvec.getOrElse(0.U)
    csr.scounteren := scounteren.getOrElse(0.U)

    csr.senvcfg := senvcfg.getOrElse(0.U)

    csr.scountinhibit := scountinhibit.getOrElse(0.U)

    csr.sscratch := sscratch.getOrElse(0.U)
    csr.sepc     := sepc.getOrElse(0.U)
    csr.scause   := scause.getOrElse(0.U)
    csr.stval    := stval.getOrElse(0.U)

    csr.satp := satp.getOrElse(0.U)

    csr.stimecmp  := stimecmp.getOrElse(0.U)
    csr.stimecmph := stimecmph.getOrElse(0.U)

    csr
  }
}

object CSRWrapperIO {
  def apply()(implicit config: RVConfig): CSRWrapperIO = new CSRWrapperIO
}

class ActionChecker(enableReg: Boolean = true, singleInstMode: Option[Inst] = None)(implicit config: RVConfig)
    extends Module {
  implicit val XLEN: Int = config.XLEN

  val commit    = IO(Input(InstCommit()))
  val writeback = IO(Input(WriteBack()))
  val mem       = if (config.formal.checkMem) Some(IO(Input(MemIO()))) else None
  val mode      = if (config.formal.checkCSRs) Some(IO(Input(UInt(2.W)))) else None
  val csr       = if (config.formal.checkCSRs) Some(IO(Input(CSRWrapperIO()))) else None

  val check = Module(new CheckerWithAction(enableReg, singleInstMode))

  check.io.instCommit := commit
  check.io.writeback  := writeback
  if (config.formal.checkMem) { check.io.mem.get := mem.get }
  if (config.formal.checkCSRs) {
    check.io.privilege.mode := mode.get
    check.io.privilege.csr  := csr.get.toCSRWire()
  } else {
    check.io.privilege.mode := PrivilegeLevel.Machine.asUInt
    check.io.privilege.csr  := CSR.wireInit()
  }

}

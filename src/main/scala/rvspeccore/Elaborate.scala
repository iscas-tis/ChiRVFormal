package rvspeccore

import rvspeccore.checker._
import rvspeccore.core._

object Elaborate extends App {
  val firtoolOptions = Array(
    "--lowering-options=" + List(
      "disallowLocalVariables",
      "disallowPackedArrays",
      "locationInfoStyle=wrapInAtSquareBracket"
    ).mkString(","),
    "-default-layer-specialization=enable"
  )

  implicit val config: RVConfig = RVConfig(
    XLEN = 64,
    extensions = "MCZifenceiZicsrZbaZbbZbcZbsZbkbZbkcZbkx",
    functions = Seq("Privileged", "TLB")
  )

  circt.stage.ChiselStage.emitSystemVerilogFile(
    new CheckerWithResult(checkMem = true, enableReg = true, singleInstMode = None),
    args,
    firtoolOptions
  )
}

package svcore

import scopt.OParser
import rvspeccore.checker._
import rvspeccore.core._
import chisel3.util.switch

case class Args(
    configFile: String = "config.json",
    model: String = "action",
    targetDir: String = "build",
    listModels: Boolean = false
)

object Args {
  val builder = OParser.builder[Args]
  val parser = {
    import builder._
    OParser.sequence(
      head("SystemVerilog Spec Core Generator", "1.3"),
      programName("sv-cores"),
      opt[String]('c', "config")
        .valueName("<file>")
        .action((x, c) => c.copy(configFile = x))
        .text("path to the configuration file (default: config.json)"),
      opt[String]('m', "model")
        .valueName("<model>")
        .action((x, c) => c.copy(model = x))
        .validate {
          case "action" | "state" | "assume" => success
          case _                                => failure("unsupported model (supported: action, state, assume)")
        }
        .text("check model to generate (default: action)"),
      opt[String]('t', "target-dir")
        .valueName("<directory>")
        .action((x, c) => c.copy(targetDir = x))
        .text("directory to output the generated SystemVerilog files (default: build)"),
      opt[Unit]('l', "list")
        .action((_, c) => c.copy(listModels = true))
        .text("show list of supported models"),
      help('h', "help").text("show list of command-line options")
    )
  }
}

object Main extends App {
  OParser.parse(Args.parser, args, Args()) match {
    case Some(args) if args.listModels =>
      println("Supported models:")
      println("  - action")
      println("  - state")
      println("  - assume")
      sys.exit(0)
    case Some(args) =>
      JsonTool.readConfigFromFile(args.configFile) match {
        case util.Success(config) =>
          val chiselStage = new chisel3.stage.ChiselStage
          args.model match {
            case "action" =>
              chiselStage.emitSystemVerilog(
                new ActionChecker(config.regDelay, config.getSingleInstMode)(config.toRVConfig),
                Array(
                  "--target-dir",
                  args.targetDir,
                  "--emission-options=disableMemRandomization,disableRegisterRandomization"
                )
              )
            case "state" => println("state model is not supported yet.")
            case "assume" =>
              chiselStage.emitSystemVerilog(
                new InstAssume()(config.toRVConfig),
                Array(
                  "--target-dir",
                  args.targetDir,
                  "--emission-options=disableMemRandomization,disableRegisterRandomization"
                )
              )
            case _ => println("unsupported model")
          }
        case util.Failure(err) =>
          throw new Exception(s"${args.configFile}: ${err.getMessage}")
      }
    case _ =>
      sys.exit(1)
  }
}

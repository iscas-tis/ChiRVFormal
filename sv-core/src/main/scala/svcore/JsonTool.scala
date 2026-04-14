package svcore

import scala.io.Source
import scala.util.Try
import upickle.default._
import upickle.core.Abort

import rvspeccore.checker._
import rvspeccore.core.RVConfig
import rvspeccore.core.spec.Inst

case class Extensions(value: Either[String, Seq[String]])

object Extensions {
  private def normalize(seq: Seq[String]): Seq[String] = seq.filter(_.nonEmpty).distinct

  implicit val rw: ReadWriter[Extensions] = {
    readwriter[ujson.Value].bimap[Extensions](
      {
        case Extensions(Left(s))    => ujson.Str(s)
        case Extensions(Right(seq)) => ujson.Arr.from(normalize(seq).map(ujson.Str(_)))
      },
      {
        case ujson.Str(s) => Extensions(Left(s))
        case ujson.Arr(arr) =>
          Extensions(Right(normalize(arr.map {
            case ujson.Str(s) => s
            case other =>
              throw Abort(s"expected array of strings, found element ${other.getClass().getSimpleName()}($other)")
          })))
        case other =>
          throw Abort(s"expected string | array[string] | null, got ${other.getClass.getSimpleName()}($other)")
      }
    )
  }
}

case class RefConfig(
    xlen: Int,
    extensions: Extensions = Extensions(Right(Seq.empty)),
    fakeExtensions: Extensions = Extensions(Right(Seq.empty)),
    initValue: Map[String, String] = Map.empty,
    functions: Seq[String] = Seq.empty,
    formal: Seq[String] = Seq.empty,
    regDelay: Boolean = true,
    singleInstMode: Option[String] = None
) {
  def toRVConfig: RVConfig = {
    RVConfig(
      XLEN = xlen,
      extensions = extensions.value.fold(identity, _.mkString("")),
      fakeExtensions = fakeExtensions.value.fold(identity, _.mkString("")),
      initValue = initValue,
      functions = functions,
      formal = formal
    )
  }

  def getSingleInstMode: Option[Inst] = {
    implicit val config = toRVConfig

    def getInsts(helper: AssumeHelper)(implicit config: RVConfig): Seq[Inst] =
      helper.list32 ++ (if (config.XLEN == 64) helper.append64 else Nil)

    val legalInsts: Seq[Inst] = (if (config.extensions.I) getInsts(RVI) else Nil) ++
      (if (config.extensions.C) getInsts(RVC) else Nil) ++
      (if (config.extensions.M) getInsts(RVM) else Nil) ++
      (if (config.extensions.Zba) getInsts(RVB.zba) else Nil) ++
      (if (config.extensions.Zbb) getInsts(RVB.zbb) else Nil) ++
      (if (config.extensions.Zbc) getInsts(RVB.zbc) else Nil) ++
      (if (config.extensions.Zbs) getInsts(RVB.zbs) else Nil) ++
      (if (config.extensions.Zbkb) getInsts(RVB.zbkb) else Nil) ++
      (if (config.extensions.Zbkc) getInsts(RVB.zbkc) else Nil) ++
      (if (config.extensions.Zbkx) getInsts(RVB.zbkx) else Nil) ++
      (if (config.extensions.Zicsr) getInsts(RVZicsr) else Nil) ++
      (if (config.extensions.Zifencei) getInsts(RVZifencei) else Nil) ++
      (if (config.functions.privileged) getInsts(RVPrivileged) else Nil)

    singleInstMode.map { mnemonic =>
      legalInsts.find(_.mnemonic == mnemonic.trim.toUpperCase.replace('_', '.')).getOrElse {
        throw Abort(s"invalid single instruction mode: invalid instruction '$mnemonic'")
      }
    }
  }
}

object RefConfig {
  private val baseRW: ReadWriter[RefConfig] = macroRW

  implicit val optionStringRW: ReadWriter[Option[String]] =
    readwriter[ujson.Value].bimap[Option[String]](
      {
        case Some(s) => ujson.Str(s)
        case None    => ujson.Null
      },
      {
        case ujson.Str(s) => Some(s)
        case ujson.Null   => None
        case other        => throw Abort(s"expected string or null, got ${other.getClass.getSimpleName}($other)")
      }
    )

  implicit val rw: ReadWriter[RefConfig] = {
    readwriter[ujson.Value].bimap[RefConfig](
      (rc: RefConfig) => writeJs(rc)(baseRW),
      {
        case obj: ujson.Obj =>
          obj.value.foreach {
            case ("singleInstMode", _) =>
            case (key, ujson.Null)     => throw Abort(s"field '$key' must not be null")
            case _                     =>
          }
          read[RefConfig](obj)(baseRW)
        case other =>
          throw Abort(s"expected JSON object, got ${other.getClass().getSimpleName()}($other)")
      }
    )
  }
}

object JsonTool {
  def readConfigFromFile(filePath: String): Try[RefConfig] = Try {
    val source = Source.fromFile(filePath)
    try source.mkString
    finally source.close()
  }.flatMap(json => Try(read[RefConfig](ujson.read(json))))
}

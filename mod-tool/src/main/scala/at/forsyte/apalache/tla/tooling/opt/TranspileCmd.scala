package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.bmcmt.config.{ReTLAToCHCModule, ReTLAToVMTModule}
import at.forsyte.apalache.tla.bmcmt.rules.vmt.TlaExToVMTWriter
import at.forsyte.apalache.tla.bmcmt.rules.chc.TlaExToCHCWriter
import at.forsyte.apalache.infra.passes.options.{EncodingType, OptionGroup}
import at.forsyte.apalache.infra.passes.PassChainExecutor
import org.backuity.clist.opt
import org.backuity.clist.util.Read

class TranspileCmd extends AbstractCheckerCmd(name = "transpile", description = "Transpile and quit") {

  implicit val encodingTypeRead: Read[EncodingType] =
    Read.reads[EncodingType]("an encoding type, either vmt or chc")(EncodingType.ofString)

  var encodingType: Option[EncodingType] = opt[Option[EncodingType]](name = "encoding-type", useEnv = true, default = None,
    description =
      s"the encoding types: ${EncodingType.VMT}, ${EncodingType.CHC} (experimental), default: ${EncodingType.VMT}")

  override def toConfig() =
    super.toConfig().map { cfg =>
    cfg.copy(
      transpiler = cfg.transpiler.copy(
        encodingType = encodingType
      ),
      typechecker = cfg.typechecker.copy(
        inferpoly = Some(true)
      ),
    )
  }

  def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithCheckerPreds(cfg).get

    val outFilePath = OutputManager.runDirPathOpt
      .map { p =>
        p.resolve(TlaExToCHCWriter.outFileName).toAbsolutePath
      }
      .getOrElse(TlaExToCHCWriter.outFileName)

    PassChainExecutor.run(new ReTLAToCHCModule(options)) match {
      case Right(_) => Right(s"CHC constraints successfully generated at\n$outFilePath")
      case Left(failure) => Left(failure.exitCode, "Failed to generate CHC constraints")
    }
  }
}

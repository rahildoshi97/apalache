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
    Read.reads[EncodingType]("the transpile target, either vmt or chc")(EncodingType.ofString)

  var encodingType: Option[EncodingType] = opt[Option[EncodingType]](name = "transpile-target", useEnv = true, default = None,
    description =
      s"the transpile targets: ${EncodingType.VMT}, ${EncodingType.CHC} (experimental), default: ${EncodingType.VMT}")

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
    val options = OptionGroup.WithTranspiler(cfg).get

    val encodingType = options.transpiler.encodingType

    encodingType match {
      case EncodingType.VMT =>
        val outFilePath = OutputManager.runDirPathOpt
          .map { p =>
            p.resolve(TlaExToVMTWriter.outFileName).toAbsolutePath
          }
          .getOrElse(TlaExToVMTWriter.outFileName)

        PassChainExecutor.run(new ReTLAToVMTModule(options)) match {
          case Right(_) => Right(s"VMT constraints successfully generated at\n$outFilePath")
          case Left(failure) => Left(failure.exitCode, "Failed to generate VMT constraints")
        }
      case EncodingType.CHC =>
        val outFilePath = OutputManager.runDirPathOpt
          .map { p =>
            p.resolve(TlaExToCHCWriter.outFileName).toAbsolutePath
          }
          .getOrElse(TlaExToCHCWriter.outFileName)

        PassChainExecutor.run(new ReTLAToCHCModule(options)) match {
          case Right(_) => Right(s"CHC constraints successfully generated at\n$outFilePath")
          case Left(failure) => Left(failure.exitCode, "Failed to generate CHC constraints")
        }
      case oddEncoding => throw new IllegalArgumentException(s"Unexpected transpiler.transpile-target=$oddEncoding")
    }
  }
}

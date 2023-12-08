package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.bmcmt.config.{ReTLAToCHCModule, ReTLAToVMTModule}
import at.forsyte.apalache.tla.bmcmt.rules.vmt.{TlaExToCHCWriter, TlaExToVMTWriter}
import at.forsyte.apalache.infra.passes.options.{OptionGroup, TranspilationTarget}
import at.forsyte.apalache.infra.passes.PassChainExecutor
import org.backuity.clist.opt
import org.backuity.clist.util.Read

class TranspileCmd extends AbstractCheckerCmd(name = "transpile", description = "Transpile and quit") {

  implicit val transpilationTargetRead: Read[TranspilationTarget] =
    Read.reads[TranspilationTarget]("the transpile target, either vmt or chc")(TranspilationTarget.ofString)

  var transpilationTarget: Option[TranspilationTarget] = opt[Option[TranspilationTarget]](name = "transpile-target",
      useEnv = true, default = None,
      description =
        s"the transpilation target: ${TranspilationTarget.VMT}, ${TranspilationTarget.CHC} (experimental), default: ${TranspilationTarget.VMT}")

  override def toConfig() =
    super.toConfig().map { cfg =>
      cfg.copy(
          transpiler = cfg.transpiler.copy(
              transpilationTarget = transpilationTarget
          ),
          typechecker = cfg.typechecker.copy(
              inferpoly = Some(true)
          ),
      )
    }

  def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithTranspiler(cfg).get

    val encodingType = options.transpiler.transpilationTarget

    encodingType match {
      case TranspilationTarget.VMT =>
        val outFilePath = OutputManager.runDirPathOpt
          .map { p =>
            p.resolve(TlaExToVMTWriter.outFileName).toAbsolutePath
          }
          .getOrElse(TlaExToVMTWriter.outFileName)

        PassChainExecutor.run(new ReTLAToVMTModule(options)) match {
          case Right(_)      => Right(s"VMT constraints successfully generated at\n$outFilePath")
          case Left(failure) => Left(failure.exitCode, "Failed to generate VMT constraints")
        }
      case TranspilationTarget.CHC =>
        val outFilePath = OutputManager.runDirPathOpt
          .map { p =>
            p.resolve(TlaExToCHCWriter.outFileName).toAbsolutePath
          }
          .getOrElse(TlaExToCHCWriter.outFileName)

        PassChainExecutor.run(new ReTLAToCHCModule(options)) match {
          case Right(_)      => Right(s"CHC constraints successfully generated at\n$outFilePath")
          case Left(failure) => Left(failure.exitCode, "Failed to generate CHC constraints")
        }
      case oddTranspilationTarget =>
        throw new IllegalArgumentException(s"Unexpected transpiler.transpile-target=$oddTranspilationTarget")
    }
  }
}

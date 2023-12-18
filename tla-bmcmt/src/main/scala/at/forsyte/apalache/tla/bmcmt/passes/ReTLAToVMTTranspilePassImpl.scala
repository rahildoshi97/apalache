package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.bmcmt.rules.transpilation.{TlaExToCHCWriter, TlaExToVMTWriter}
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import at.forsyte.apalache.tla.lir.{ModuleProperty, OperEx, TlaEx, TlaModule}
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, LanguageWatchdog, TransformationTracker}
import at.forsyte.apalache.tla.pp.{NormalizedNames, UniqueNameGenerator}
import com.google.inject.Inject
import com.typesafe.scalalogging.LazyLogging

/**
 * The reTLA to VMT transpilation pass
 *
 * @author
 *   Jure Kukovec
 */
class ReTLAToVMTTranspilePassImpl @Inject() (
    pred: LanguagePred,
    gen: UniqueNameGenerator,
    tracker: TransformationTracker)
    extends TranspilePass with LazyLogging {

  override def name: String = "Transpiler"

  private def getTransitionsWithNames(module: TlaModule, prefix: String): Seq[(String, TlaEx)] =
    module.operDeclarations
      .filter {
        _.name.startsWith(prefix) // transitions end in 0,1,...
      }
      .sortBy(_.name)
      .map { d =>
        (d.name, d.body)
      }

  val writer = new TlaExToVMTWriter(gen)

  override def execute(module: TlaModule): PassResult = {
    // Check if still ok fragment (sanity check, see postTypeChecker)
    LanguageWatchdog(pred).check(module)

    // Init has primes, for VMT we need to deprime it
    val deprime = ReplaceFixed(tracker).withFun { case OperEx(TlaActionOper.prime, arg) => arg }
    val initTrans = getTransitionsWithNames(module, NormalizedNames.INIT_PREFIX).map { case (a, b) =>
      (a, deprime(b))
    }
    val nextTrans = getTransitionsWithNames(module, NormalizedNames.NEXT_PREFIX)
    val cinitP = getTransitionsWithNames(module, NormalizedNames.CONST_INIT)
    val vcInvs = getTransitionsWithNames(module, NormalizedNames.VC_INV_PREFIX)
    val vcActionInvs = getTransitionsWithNames(module, NormalizedNames.VC_ACTION_INV_PREFIX)

    writer.annotateAndWrite(
        module.varDeclarations,
        module.constDeclarations,
        cinitP,
        initTrans,
        nextTrans,
        vcInvs ++ vcActionInvs,
    )

    Right(module)
  }

  override def dependencies: Set[ModuleProperty.Value] = Set()
  override def transformations: Set[ModuleProperty.Value] = Set()
}

class ReTLAToCHCTranspilePassImpl @Inject() (
    pred: LanguagePred,
    gen: UniqueNameGenerator,
    tracker: TransformationTracker)
    extends ReTLAToVMTTranspilePassImpl(pred, gen, tracker) {

  override val writer = new TlaExToCHCWriter(gen)
}

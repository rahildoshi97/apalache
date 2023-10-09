package at.forsyte.apalache.tla.bmcmt.config

import at.forsyte.apalache.tla.lir.transformations.standard.{MonotypeLanguagePred, ReTLALanguagePredForCHC}
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, PredResult}
import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule}

/**
 * A combined predicate to use in ReTLAToCHCModule.
 */
class ReTLACombinedPredicateForCHC extends LanguagePred {
  private val mono = new MonotypeLanguagePred()
  private val retla = new ReTLALanguagePredForCHC()

  override def isExprOk(ex: TlaEx): PredResult = {
    mono.isExprOk(ex).and(retla.isExprOk(ex))
  }

  override def isModuleOk(mod: TlaModule): PredResult = {
    mono.isModuleOk(mod).and(retla.isModuleOk(mod))
  }
}

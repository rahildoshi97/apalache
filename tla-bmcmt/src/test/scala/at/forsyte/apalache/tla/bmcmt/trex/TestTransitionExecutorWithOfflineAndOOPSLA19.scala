package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.{SymbStateRewriterImpl, oopsla19Encoding}
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatest.junit.JUnitRunner

/**
 * The tests for TransitionExecutorImpl that are using IncrementalSnapshot.
 *
 * @author Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorWithOfflineAndOOPSLA19 extends TestTransitionExecutorImpl[OfflineExecutionContextSnapshot] {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver = RecordingSolverContext.createZ3(None,
        SolverConfig(debug = false, profile = false, randomSeed = 0, smtEncoding = oopsla19Encoding))
    val rewriter = new SymbStateRewriterImpl(solver, new ExprGradeStoreImpl())
    val exeCtx = new OfflineExecutionContext(rewriter)
    try {
      test(exeCtx)
    } finally {
      rewriter.dispose()
    }
  }
}

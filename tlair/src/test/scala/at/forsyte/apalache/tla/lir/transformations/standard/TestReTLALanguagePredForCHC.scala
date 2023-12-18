package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestReTLALanguagePredForCHC extends TestReTLALanguagePred {
  private val pred = new ReTLALanguagePredForCHC

  test("reTLA with arithmetics: integer expressions") {
    expectOk(pred.isExprOk(lt(int(1), int(3))))
    expectOk(pred.isExprOk(le(int(1), int(3))))
    expectOk(pred.isExprOk(gt(int(1), int(3))))
    expectOk(pred.isExprOk(ge(int(1), int(3))))
    expectOk(pred.isExprOk(plus(int(1), int(3))))
    expectOk(pred.isExprOk(minus(int(1), int(3))))
    expectOk(pred.isExprOk(mult(int(1), int(3))))
    expectOk(pred.isExprOk(div(int(1), int(3))))
    expectOk(pred.isExprOk(mod(int(1), int(3))))
    expectOk(pred.isExprOk(exp(int(2), int(3))))
    expectOk(pred.isExprOk(uminus(int(2))))
  }

}

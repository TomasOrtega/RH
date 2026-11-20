import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullSecKAlg
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PolyExpBound

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

/- English proof (translation)
Introduce `m n c hc P Q r`. Establish `hP` using `NullS.integrable_pg c hc P`. Establish `hQ` using `NullS.integrable_pg c hc Q`. Prove the components needed by the constructor for the conclusion. Unfold `mom`.

Rewrite using `[← integral_add hP hQ]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [evX, map_add, add_mul]`. Unfold `mom`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [evX, MvPolynomial.smul_eval, mul_assoc]`.
-/
theorem momLin : MomLin := by
  intro m n c hc P Q r
  have hP := NullS.integrable_pg c hc P
  have hQ := NullS.integrable_pg c hc Q
  constructor
  · unfold mom
    rw [← integral_add hP hQ]
    congr 1
    funext x
    simp only [evX, map_add, add_mul]
  · unfold mom
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [evX, MvPolynomial.smul_eval, mul_assoc]

end PositivityTheory.Rg.Sw.LC

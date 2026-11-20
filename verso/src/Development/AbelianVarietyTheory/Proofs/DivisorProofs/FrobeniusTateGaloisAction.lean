import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusEndomorphismUniqueStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.frobenius_endomorphism_unique K A).1`. Use `LinearMap.ext fun t => Tate.ext fun n => ?_` and prove the remaining obligations. Conclude with `h (t.lev n)`.
-/
theorem frob_tend_galT (K : Type) [Field K] [Fintype K] (l : ℕ) [Fact l.Prime] (A : AbVar K) :
    tend l A (frob A) = galT l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  have h := (GlobalTheory.T.frobenius_endomorphism_unique K A).1
  refine LinearMap.ext fun t => Tate.ext fun n => ?_
  exact h (t.lev n)

/- English proof (translation)
Use `⟨frob_tend_galT K l A, ?_⟩` and prove the remaining obligations. Establish `hv : vend l A (toEnd0 A (frob A)) = (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)) (tend l A (frob A))`. Simplify using `[vend, toEnd0, Algebra.TensorProduct.lift_tmul]`. Rewrite using `[hv, frob_tend_galT K l A]`. Both sides reduce to the same expression.
-/
theorem frob_tate (K : Type) [Field K] [Fintype K] (l : ℕ) [Fact l.Prime] (A : AbVar K) :
    tend l A (frob A) = galT l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) ∧
    vend l A (toEnd0 A (frob A)) = galV l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  refine ⟨frob_tend_galT K l A, ?_⟩
  have hv : vend l A (toEnd0 A (frob A)) =
      (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)) (tend l A (frob A)) := by
    simp [vend, toEnd0, Algebra.TensorProduct.lift_tmul]
  rw [hv, frob_tend_galT K l A]
  rfl

end GlobalTheory.AV.AbVar

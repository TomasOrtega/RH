import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieExteriorSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodMetric.PolyRep.lie_wedge2` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolynomialMatrixFamilyRepLieExteriorSquare.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_exteriorSquare : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), ρ.wedge2.lie A = wedge2Lie (ρ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_wedge2 | exact GlobalTheory.GoodMetric.PolyRep.lie_wedge2 | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_wedge2 <;> assumption)

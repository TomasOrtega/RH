import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CCRFock.polEval_pderiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCommutingOperatorsPolynomialEvalPderiv.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.commutingOperatorsPolynomialEval_pderiv : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [DecidableEq ι] (m d : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V), (∀ i j, d i * m j - m j * d i = if i = j then 1 else 0) →
    (∀ i, d i f₀ = 0) → ∀ (i : ι) (p : MvPolynomial ι ℂ),
      GlobalTheory.CCRFock.polEval m hm f₀ (MvPolynomial.pderiv i p) = d i (GlobalTheory.CCRFock.polEval m hm f₀ p) := by
  first | exact @GlobalTheory.CCRFock.polEval_pderiv | exact GlobalTheory.CCRFock.polEval_pderiv | (intros; apply GlobalTheory.CCRFock.polEval_pderiv <;> assumption)

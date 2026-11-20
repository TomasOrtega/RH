import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicative
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Cyc.Decomp.lam_mul_of_isMat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FOcTensorCoeffActionMatrixMultiplicative.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.ocTensorCoeffActionMatrix_multiplicative : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), IsMat K LL T M A → (∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a) ∧ A 1 = 1 ∧ (∀ a b, A (a * b) = A a * A b) ∧ ∀ x y : OCO LL, lam o A (x * y) = lam o A x * lam o A y := by
  first | exact @GlobalTheory.Cyc.Decomp.lam_mul_of_isMat | exact GlobalTheory.Cyc.Decomp.lam_mul_of_isMat | (intros; apply GlobalTheory.Cyc.Decomp.lam_mul_of_isMat <;> assumption)

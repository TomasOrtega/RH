import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerreTateLinearIndependentOfWeightwise
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSerreTateLinearIndependentOfWeightwise.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.serreTate_linearIndependent_of_weightwise : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (G : Subgroup (GQ l)) (E : IntermediateField ℚ_[l] (Om l)), (∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E)) → ∀ (r n : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (e : Fin n → Fin r → PadicComplex l) (u : Fin n → ℤ), (∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k) → (∀ (a : ℤ) (c : Fin n → ↥E), (∀ k, u k ≠ a → c k = 0) → ∑ k, (((c k : ↥E) : Om l) : PadicComplex l) • e k = 0 → ∀ k, c k = 0) → LinearIndependent (PadicComplex l) e := by
  first | exact @GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise | exact GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise | (intros; apply GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise <;> assumption)

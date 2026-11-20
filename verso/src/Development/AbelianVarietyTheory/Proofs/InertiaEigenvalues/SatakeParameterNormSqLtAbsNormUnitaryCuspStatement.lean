import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNormSqLtAbsNormUnitaryCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.RSStrict.norm_sq_lt_absNorm`. Consider the case `exact GlobalTheory.RSStrict.norm_sq_lt_absNorm`. Consider the case `(intros; apply GlobalTheory.RSStrict.norm_sq_lt_absNorm <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (σ : CG E a), 1 ≤ a → σ.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → ∀ w ∉ T, ∀ α ∈ sat σ w, ‖(α : ℂ)‖ ^ 2 < (Ideal.absNorm w.asIdeal : ℝ) := by
  first
  | exact @GlobalTheory.RSStrict.norm_sq_lt_absNorm
  | exact GlobalTheory.RSStrict.norm_sq_lt_absNorm
  | (intros; apply GlobalTheory.RSStrict.norm_sq_lt_absNorm <;> assumption)

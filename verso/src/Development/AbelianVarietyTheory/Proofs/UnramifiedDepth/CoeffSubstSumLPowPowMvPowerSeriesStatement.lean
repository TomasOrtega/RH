import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffSubstSumLPowPowMvPowerSeries
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LogSubst.coeff_subst_sum_pow_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FCoeffSubstSumLPowPowMvPowerSeries.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries : ∀ (C : Type) [Field C] (σ τ I : Type) [Fintype σ] [Fintype τ] [Fintype I] (l : ℕ), 2 ≤ l → ∀ (co : I → ℕ → C) (t : I → MvPowerSeries σ C) (F : MvPowerSeries σ C) (f : σ → MvPowerSeries τ C), (∀ x, MvPowerSeries.constantCoeff (f x) = 0) → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ μ : σ →₀ ℕ, MvPowerSeries.coeff μ F = ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, co c s * MvPowerSeries.coeff μ (t c ^ (l ^ s))) → ∀ ν : τ →₀ ℕ, MvPowerSeries.coeff ν (MvPowerSeries.subst f F) = ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s * MvPowerSeries.coeff ν ((MvPowerSeries.subst f (t c) : MvPowerSeries τ C) ^ (l ^ s)) := by
  first | exact @GlobalTheory.LogSubst.coeff_subst_sum_pow_pow | exact GlobalTheory.LogSubst.coeff_subst_sum_pow_pow | (intros; apply GlobalTheory.LogSubst.coeff_subst_sum_pow_pow <;> assumption)

import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.BrExistsSqInv
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

/- English proof (translation)
Use `set a : ℂ := ρ ⟨g2 Λ, h2⟩ with ha`. Use `set b : ℂ := ρ ⟨g3 Λ, h3⟩ with hb`. Establish `hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1`. Apply `M.val.injective` to reduce the goal to its premises. Rewrite using `[map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]`.

Conclude with `h1`. Establish `hab1 : a ^ 3 - 27 * b ^ 2 = 1`. Rewrite using `[ha, hb, ← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]`. Establish `hjL : (⟨jL Λ, hjM⟩ : M) = 1728 * (⟨g2 Λ, h2⟩ : M) ^ 3`. Apply `M.val.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, map_pow, map_ofNat]`. Use `show jL Λ = 1728 * g2 Λ ^ 3`. Rewrite using `[br_jL_eq, h1, div_one]`. Establish `hj' : 1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2) = jL Λ₀`. Rewrite using `[hab1, div_one, ← hj, hjL, map_mul, map_pow, map_ofNat]`.

Take `⟨c, hc0, hc2, hc3⟩` from `br_exists_scale Λ₀ h0 a b (by rw [hab1]; exact one_ne_zero) hj'`. Establish `hd1 : discr (c • Λ₀) = 1` using `by show g2 (c • Λ₀) ^ 3 - 27 * g3 (c • Λ₀) ^ 2 = 1`. Rewrite using `[hc2, hc3, hab1]`. Establish `hl2 : Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g2 Λ) = ⟨g2 Λ, h2⟩` using `dif_pos h2`. Establish `hl3 : Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g3 Λ) = ⟨g3 Λ, h3⟩` using `dif_pos h3`.

Establish `hex : ∃ Λ' : AddSubgroup ℂ, Formalism.MainNotions.TaylorLogMetric.g2 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g2 Λ)) ∧ Formalism.MainNotions.TaylorLogMetric.g3 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.Mai …` using `⟨c • Λ₀, by rw [hl2]; exact hc2, by rw [hl3]; exact hc3⟩`. Establish `hspec` using `Classical.epsilon_spec hex`. Establish `hs2 : Formalism.MainNotions.TaylorLogMetric.g2 (lamConj M ρ Λ) = a`. Conclude with `hspec.1.trans (by rw [hl2])`. Establish `hs3 : Formalism.MainNotions.TaylorLogMetric.g3 (lamConj M ρ Λ) = b`.

Conclude with `hspec.2.trans (by rw [hl3])`. Use `⟨c, hc0, ?_, hd1⟩` and prove the remaining obligations. Use `symm`. Apply `hU` to reduce the goal to its premises. Use `show discr (c • Λ₀) ≠ 0`.

Rewrite using `[hd1]`. Conclude with `one_ne_zero`. Rewrite using `[hs2]`. Conclude with `hc2`. Rewrite using `[hs3]`.

Conclude with `hc3`.
-/
theorem br_lamConj_eq (hU : UniqInv) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (Λ Λ₀ : AddSubgroup ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (h1 : discr Λ = 1)
    (h0 : discr Λ₀ ≠ 0) (hjM : jL Λ ∈ M) (hj : ρ ⟨jL Λ, hjM⟩ = jL Λ₀) :
    ∃ c : ℂ, c ≠ 0 ∧ lamConj M ρ Λ = c • Λ₀ ∧ discr (c • Λ₀) = 1 := by
  set a : ℂ := ρ ⟨g2 Λ, h2⟩ with ha
  set b : ℂ := ρ ⟨g3 Λ, h3⟩ with hb
  have hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1 := by
    apply M.val.injective
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]
    exact h1
  have hab1 : a ^ 3 - 27 * b ^ 2 = 1 := by
    rw [ha, hb, ← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]
  have hjL : (⟨jL Λ, hjM⟩ : M) = 1728 * (⟨g2 Λ, h2⟩ : M) ^ 3 := by
    apply M.val.injective
    rw [map_mul, map_pow, map_ofNat]
    show jL Λ = 1728 * g2 Λ ^ 3
    rw [br_jL_eq, h1, div_one]
  have hj' : 1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2) = jL Λ₀ := by
    rw [hab1, div_one, ← hj, hjL, map_mul, map_pow, map_ofNat]
  obtain ⟨c, hc0, hc2, hc3⟩ := br_exists_scale Λ₀ h0 a b (by rw [hab1]; exact one_ne_zero) hj'
  have hd1 : discr (c • Λ₀) = 1 := by
    show g2 (c • Λ₀) ^ 3 - 27 * g3 (c • Λ₀) ^ 2 = 1
    rw [hc2, hc3, hab1]
  have hl2 : Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g2 Λ) = ⟨g2 Λ, h2⟩ := dif_pos h2
  have hl3 : Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g3 Λ) = ⟨g3 Λ, h3⟩ := dif_pos h3
  have hex : ∃ Λ' : AddSubgroup ℂ, Formalism.MainNotions.TaylorLogMetric.g2 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g2 Λ)) ∧
      Formalism.MainNotions.TaylorLogMetric.g3 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g3 Λ)) :=
    ⟨c • Λ₀, by rw [hl2]; exact hc2, by rw [hl3]; exact hc3⟩
  have hspec := Classical.epsilon_spec hex
  have hs2 : Formalism.MainNotions.TaylorLogMetric.g2 (lamConj M ρ Λ) = a := by
    exact hspec.1.trans (by rw [hl2])
  have hs3 : Formalism.MainNotions.TaylorLogMetric.g3 (lamConj M ρ Λ) = b := by
    exact hspec.2.trans (by rw [hl3])
  refine ⟨c, hc0, ?_, hd1⟩
  symm
  apply hU
  · show discr (c • Λ₀) ≠ 0
    rw [hd1]; exact one_ne_zero
  · rw [hs2]; exact hc2
  · rw [hs3]; exact hc3

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end

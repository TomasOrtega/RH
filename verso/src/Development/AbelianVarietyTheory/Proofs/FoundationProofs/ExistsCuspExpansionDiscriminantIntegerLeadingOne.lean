import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDeltaInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQStatement

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNExpD

/- English proof (translation)
Rewrite using `[hasQ_iff]`. Introduce `τ`. Use `ReciprocityTheory.ChartRestriction.L1.isMF_DD.hasSum τ` as an intermediate fact. Rewrite `this` using `[← ReciprocityTheory.ChartRestriction.L1.dC_eq]`. Simplify `this` using `[ReciprocityTheory.ChartRestriction.L1.qm, ReciprocityTheory.ChartRestriction.L1.dC, PowerSeries.coeff_map]`.
-/
theorem hasQ_DD_int : HasQ 1 DD fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : ℂ) := by
  rw [hasQ_iff]
  intro τ
  have := ReciprocityTheory.ChartRestriction.L1.isMF_DD.hasSum τ
  rw [← ReciprocityTheory.ChartRestriction.L1.dC_eq] at this
  simpa [ReciprocityTheory.ChartRestriction.L1.qm, ReciprocityTheory.ChartRestriction.L1.dC, PowerSeries.coeff_map] using this

/- English proof (translation)
Introduce `Ω _ ε`. Establish `hD : HasQ 1 DD fun n => ε ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω)`. Simplify `hasQ_DD_int` using `only [map_intCast]`. Take `⟨h, hexp, hk, hz⟩` from `GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε 1 DD (fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω)) one_pos hD`. Establish `h1 : h.coeff 1 = 1`.

Use `hk 1` as an intermediate fact. Simplify `this` using `[ReciprocityTheory.ChartRestriction.L1.dZ_coeff_one]`. Establish `hlow : ∀ r : ℚ, r < 1 → h.coeff r = 0`. Introduce `r hr`. Distinguish the cases in `hr' : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)`.

Take `⟨k, rfl⟩` from `hr'`. Establish `hk1 : (k : ℚ) < 1` using `by simpa using hr`. Establish `hk0 : k = 0`. Establish `: k < 1` using `by exact_mod_cast hk1`. Use linear arithmetic over natural numbers and integers.

Substitute `hk0` using the available equality. Rewrite using `[hk 0]`. Simplify using `[ReciprocityTheory.ChartRestriction.L1.dZ_coeff_zero]`. Use `push_neg at hr'`. Conclude with `hz r hr'`.

Establish `hne : h ≠ 0` using `HahnSeries.ne_zero_of_coeff_ne_zero (h1 ▸ one_ne_zero)`. Establish `hord : h.order = 1`. Use `le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (h1 ▸ one_ne_zero)) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Conclude with `(HahnSeries.coeff_order_eq_zero.not.mpr hne) (hlow _ hlt)`. Use `⟨h, hexp, hne, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[HahnSeries.leadingCoeff_eq, hord, h1]`. Introduce `r`. Distinguish the cases in `hr : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)`.

Take `⟨k, rfl⟩` from `hr`. Conclude with `⟨_, hk k⟩`. Use `push_neg at hr`. Conclude with `⟨0, by simpa using hz r hr⟩`.
-/
theorem expD : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε DD h ∧ h ≠ 0 ∧
    h.leadingCoeff = 1 ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  intro Ω _ ε
  have hD : HasQ 1 DD fun n => ε ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω) := by
    simpa only [map_intCast] using hasQ_DD_int
  obtain ⟨h, hexp, hk, hz⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε 1 DD
    (fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω)) one_pos hD
  have h1 : h.coeff 1 = 1 := by
    have := hk 1
    simpa [ReciprocityTheory.ChartRestriction.L1.dZ_coeff_one] using this
  have hlow : ∀ r : ℚ, r < 1 → h.coeff r = 0 := by
    intro r hr
    by_cases hr' : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)
    · obtain ⟨k, rfl⟩ := hr'
      have hk1 : (k : ℚ) < 1 := by simpa using hr
      have hk0 : k = 0 := by
        have : k < 1 := by exact_mod_cast hk1
        omega
      subst hk0
      rw [hk 0]
      simp [ReciprocityTheory.ChartRestriction.L1.dZ_coeff_zero]
    · push_neg at hr'
      exact hz r hr'
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero (h1 ▸ one_ne_zero)
  have hord : h.order = 1 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (h1 ▸ one_ne_zero)) ?_
    by_contra hlt
    push_neg at hlt
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hne) (hlow _ hlt)
  refine ⟨h, hexp, hne, ?_, ?_⟩
  · rw [HahnSeries.leadingCoeff_eq, hord, h1]
  · intro r
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)
    · obtain ⟨k, rfl⟩ := hr
      exact ⟨_, hk k⟩
    · push_neg at hr
      exact ⟨0, by simpa using hz r hr⟩

end GlobalTheory.FNExpD

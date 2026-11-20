import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory

/- English proof (translation)
Introduce `g Λ hΛ d hd`. Establish `hc1 : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹) Filter.atTop (nhds 0)`. Simplify `tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)` using `only [one_div, Nat.cast_add, Nat.cast_one]`. Establish `hlim : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹ • d) Filter.atTop (nhds 0)`. Simplify using `using hc1.smul_const d`.

Set `f : ℕ → Λ` to `fun k => ⟨(((k + 1 : ℕ) : ℂ))⁻¹ • d, hd (k + 1) k.succ_pos⟩`. Establish `hf : Filter.Tendsto f Filter.atTop (nhds 0)`. Rewrite using `[tendsto_subtype_rng]`. Simplify `hlim` using `[f]`. Rewrite `hf` using `[nhds_discrete, Filter.tendsto_pure]`.

Take `⟨k, hk⟩` from `hf.exists`. Establish `h0 : (((k + 1 : ℕ) : ℂ))⁻¹ • d = 0` using `congrArg Subtype.val hk`. Rewrite `h0` using `[smul_eq_zero]`. Break down `h0 with h0 | h0` into its components or cases. It suffices to derive a contradiction.

Rewrite `h0` using `[inv_eq_zero]`. Conclude with `(Nat.cast_ne_zero.mpr k.succ_ne_zero) h0`. Conclude with `h0`.
-/
theorem discrete_submodule_inv_smul_eq_zero : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → ∀ d : Fin g → ℂ, (∀ k : ℕ, 0 < k → (k : ℂ)⁻¹ • d ∈ Λ) → d = 0 := by
  intro g Λ hΛ d hd
  have hc1 : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹) Filter.atTop (nhds 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
  have hlim : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹ • d) Filter.atTop (nhds 0) := by
    simpa using hc1.smul_const d
  let f : ℕ → Λ := fun k => ⟨(((k + 1 : ℕ) : ℂ))⁻¹ • d, hd (k + 1) k.succ_pos⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds 0) := by
    rw [tendsto_subtype_rng]
    simpa [f] using hlim
  rw [nhds_discrete, Filter.tendsto_pure] at hf
  obtain ⟨k, hk⟩ := hf.exists
  have h0 : (((k + 1 : ℕ) : ℂ))⁻¹ • d = 0 := congrArg Subtype.val hk
  rw [smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exfalso
    rw [inv_eq_zero] at h0
    exact (Nat.cast_ne_zero.mpr k.succ_ne_zero) h0
  · exact h0

end GlobalTheory

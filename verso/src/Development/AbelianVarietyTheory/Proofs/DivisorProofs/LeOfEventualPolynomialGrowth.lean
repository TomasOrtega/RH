import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteMonotoneGrowth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `d D a f h`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hq : Filter.Tendsto (fun s : ℕ => ((s:ℝ) + a) / s) Filter.atTop (nhds 1)`. Establish `h2 : Filter.Tendsto (fun s : ℕ => 1 + (a:ℝ) / s) Filter.atTop (nhds (1 + 0))` using `tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (a:ℝ))`.

Rewrite `h2` using `[add_zero]`. Apply `h2.congr'` to reduce the goal to its premises. Use `filter_upwards [Filter.eventually_gt_atTop 0] with s hs`. Establish `hs' : (s:ℝ) ≠ 0` using `by positivity`. Rewrite using `[add_div, div_self hs']`.

Establish `h1 : Filter.Tendsto (fun s : ℕ => (D:ℝ) * (((s:ℝ) + a) / s) ^ f) Filter.atTop (nhds ((D:ℝ) * 1 ^ f))` using `tendsto_const_nhds.mul (hq.pow f)`. Rewrite `h1` using `[one_pow, _root_.mul_one]`. Establish `hd : (D:ℝ) < d` using `by exact_mod_cast hlt`. Establish `hev : ∀ᶠ s : ℕ in Filter.atTop, (D:ℝ) * (((s:ℝ) + a) / s) ^ f < d` using `h1.eventually (gt_mem_nhds hd)`. Take `⟨N, hN⟩` from `Filter.eventually_atTop.1 hev`.

Take `⟨s, hs, hle⟩` from `h (N + 1)`. Establish `hlt2` using `hN s (by omega)`. Establish `hspos : (0:ℝ) < s`. Establish `: 0 < s` using `by omega`. Conclude with `this` after adjusting the coercions.

Rewrite `hlt2` using `[div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)]`. Establish `hc : ((d * s ^ f : ℕ) : ℝ) ≤ ((D * (s + a) ^ f : ℕ) : ℝ)` using `by exact_mod_cast hle`. Move the coercions through the operations in `at hc`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_of_frequently_mul_pow_le_mul_add_pow :
    ∀ (d D a f : ℕ), (∀ N : ℕ, ∃ s, N ≤ s ∧ d * s ^ f ≤ D * (s + a) ^ f) → d ≤ D := by
  intro d D a f h
  by_contra hlt
  push_neg at hlt
  have hq : Filter.Tendsto (fun s : ℕ => ((s:ℝ) + a) / s) Filter.atTop (nhds 1) := by
    have h2 : Filter.Tendsto (fun s : ℕ => 1 + (a:ℝ) / s) Filter.atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (a:ℝ))
    rw [add_zero] at h2
    apply h2.congr'
    filter_upwards [Filter.eventually_gt_atTop 0] with s hs
    have hs' : (s:ℝ) ≠ 0 := by positivity
    rw [add_div, div_self hs']
  have h1 : Filter.Tendsto (fun s : ℕ => (D:ℝ) * (((s:ℝ) + a) / s) ^ f) Filter.atTop
      (nhds ((D:ℝ) * 1 ^ f)) := tendsto_const_nhds.mul (hq.pow f)
  rw [one_pow, _root_.mul_one] at h1
  have hd : (D:ℝ) < d := by exact_mod_cast hlt
  have hev : ∀ᶠ s : ℕ in Filter.atTop, (D:ℝ) * (((s:ℝ) + a) / s) ^ f < d :=
    h1.eventually (gt_mem_nhds hd)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨s, hs, hle⟩ := h (N + 1)
  have hlt2 := hN s (by omega)
  have hspos : (0:ℝ) < s := by
    have : 0 < s := by omega
    exact_mod_cast this
  rw [div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)] at hlt2
  have hc : ((d * s ^ f : ℕ) : ℝ) ≤ ((D * (s + a) ^ f : ℕ) : ℝ) := by exact_mod_cast hle
  push_cast at hc
  linarith

/- English proof (translation)
The claim follows from `le_of_frequently_mul_pow_le_mul_add_pow`.
-/
example : ∀ (d D a f : ℕ), (∀ N : ℕ, ∃ s, N ≤ s ∧ d * s ^ f ≤ D * (s + a) ^ f) → d ≤ D := le_of_frequently_mul_pow_le_mul_add_pow

end GlobalTheory

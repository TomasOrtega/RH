import Formalism.GrowthSums.StatementA

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

/- English proof (translation)
Introduce `p hp`. Establish `hp0 : p ≠ 0` using `by positivity`. Establish `hp2 : 1 < p ^ 2` using `by nlinarith`. Establish `hq : p ^ 2 - 1 ≠ 0` using `by linarith`. Establish `hq' : p - 1 ≠ 0` using `by linarith`.

Establish `hr0 : (0 : ℝ) ≤ (p ^ 2)⁻¹` using `by positivity`. Establish `hr1 : (p ^ 2)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hp2`. Establish `hs` using `(hasSum_geometric_of_lt_one hr0 hr1).mul_left p⁻¹`. Establish `hf : (fun n : ℕ => (p ^ (2 * n + 1))⁻¹) = fun i : ℕ => p⁻¹ * (p ^ 2)⁻¹ ^ i`. Use function extensionality and compare the values at `n`.

Rewrite using `[inv_pow, ← mul_inv]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : gamP p = p⁻¹ * (1 - (p ^ 2)⁻¹)⁻¹`. Unfold `gamP rhoP`.

Establish `e : 1 - (p ^ 2)⁻¹ = (p ^ 2 - 1) / p ^ 2` using `by field_simp`. Rewrite using `[e, inv_div]`. Clear the denominators using the available nonvanishing facts. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, hv]`.

Conclude with `hs`. Unfold `gamP rhoP`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem oddPowerInvSumIdentity : GammaIdentity := by
  intro p hp
  have hp0 : p ≠ 0 := by positivity
  have hp2 : 1 < p ^ 2 := by nlinarith
  have hq : p ^ 2 - 1 ≠ 0 := by linarith
  have hq' : p - 1 ≠ 0 := by linarith
  have hr0 : (0 : ℝ) ≤ (p ^ 2)⁻¹ := by positivity
  have hr1 : (p ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp2
  have hs := (hasSum_geometric_of_lt_one hr0 hr1).mul_left p⁻¹
  have hf : (fun n : ℕ => (p ^ (2 * n + 1))⁻¹) = fun i : ℕ => p⁻¹ * (p ^ 2)⁻¹ ^ i := by
    funext n
    rw [inv_pow, ← mul_inv]
    congr 1
    ring
  have hv : gamP p = p⁻¹ * (1 - (p ^ 2)⁻¹)⁻¹ := by
    unfold gamP rhoP
    have e : 1 - (p ^ 2)⁻¹ = (p ^ 2 - 1) / p ^ 2 := by field_simp
    rw [e, inv_div]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hf, hv]
    exact hs
  · unfold gamP rhoP
    field_simp
    ring

end Formalism.GrowthSums

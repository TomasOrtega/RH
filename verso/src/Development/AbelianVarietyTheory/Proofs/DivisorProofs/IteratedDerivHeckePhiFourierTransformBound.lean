import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.TermBoundDeriv

/- English proof (translation)
Establish `hti : 0 < t⁻¹` using `inv_pos.mpr ht`. Establish `hM1 : 1 ≤ t + t⁻¹`. Break down `le_total 1 t with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: 1 ≤ t⁻¹` using `one_le_inv_iff₀.mpr ⟨ht, h⟩`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsr : (t + t⁻¹) ^ (s : ℝ) = (t + t⁻¹) ^ s` using `Real.rpow_natCast _ _`. Rewrite using `[← hsr]`. Break down `le_total 0 r with h0 | h0` into its components or cases. Combine the equalities or inequalities in the displayed calculation.

Establish `e : t ^ r = t⁻¹ ^ (-r)`. Rewrite using `[Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv]`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rpow_le_add_inv_pow {t r : ℝ} {s : ℕ} (ht : 0 < t) (hr : |r| ≤ s) :
    t ^ r ≤ (t + t⁻¹) ^ s := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have hM1 : 1 ≤ t + t⁻¹ := by
    rcases le_total 1 t with h | h
    · linarith
    · have : 1 ≤ t⁻¹ := one_le_inv_iff₀.mpr ⟨ht, h⟩
      linarith
  have hsr : (t + t⁻¹) ^ (s : ℝ) = (t + t⁻¹) ^ s := Real.rpow_natCast _ _
  rw [← hsr]
  rcases le_total 0 r with h0 | h0
  · calc t ^ r ≤ (t + t⁻¹) ^ r := Real.rpow_le_rpow ht.le (by linarith) h0
      _ ≤ (t + t⁻¹) ^ (s : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 (le_trans (le_abs_self r) hr)
  · have e : t ^ r = t⁻¹ ^ (-r) := by
      rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv]
    rw [e]
    calc t⁻¹ ^ (-r) ≤ (t + t⁻¹) ^ (-r) := Real.rpow_le_rpow hti.le (by linarith) (by linarith)
      _ ≤ (t + t⁻¹) ^ (s : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 (le_trans (neg_le_abs r) hr)

end GlobalTheory.HeckeTwo.TermBoundDeriv

namespace GlobalTheory.HeckeTwo.TermBoundDeriv

/- English proof (translation)
Introduce `hder hint K hK hKH j`. Take `⟨S, P, hS, hEq⟩` from `hder j`. Take `⟨R, hR⟩ : ∃ R, ∀ σ ∈ K, ‖σ‖ ≤ R` from `hK.isBounded.exists_norm_le`. Use `⟨⌈1 + (j : ℝ) + 2 * R⌉₊, fun N => ?_⟩` and prove the remaining obligations. Establish `hCex : ∀ p : ℕ × ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ (p ∈ S → ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 → ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖ ≤ C * |y| ^ ((p.2.2 : ℝ) + 1 - p.1 - 2 * p.2.1 - 2 * σ.re) / (1 + |ν * y|) ^ N)`.

Introduce `p`. Distinguish the cases in `hp : p ∈ S`. Take `⟨C, hC⟩` from `hint K hK hKH p.1 p.2.1 p.2.2 (hS p hp).1 N`. Use `⟨max C 0, le_max_right _ _, fun _ σ hσ ν y hν hy => (hC σ hσ ν y hν hy).trans ?_⟩` and prove the remaining obligations. Conclude with `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)`.

Conclude with `⟨0, le_rfl, fun h => absurd h hp⟩`. Use `choose Cp hCp0 hCp using hCex`. Establish `hBex : ∀ p : ℕ × ℕ × ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ K, ‖(P p).eval σ‖ ≤ B`. Introduce `p`. Take `⟨B, hB⟩` from `hK.exists_bound_of_continuousOn (P p).continuous.continuousOn`.

Conclude with `⟨max B 0, le_max_right _ _, fun σ hσ => (hB σ hσ).trans (le_max_left _ _)⟩`. Use `choose B hB0 hB using hBex`. Use `⟨∑ p ∈ S, B p * Cp p, fun σ hσ ν y hν hy => ?_⟩` and prove the remaining obligations. Establish `hy' : 0 < |y|` using `abs_pos.mpr hy`. Establish `hD : 0 < (1 + |ν * y|) ^ N` using `by positivity`.

Establish `hre : |σ.re| ≤ R` using `(Complex.abs_re_le_norm σ).trans (hR σ hσ)`. Rewrite using `[hEq σ (hKH hσ) ν y hy]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`.

Rewrite using `[norm_mul]`. Apply `mul_le_mul (hB p σ hσ) _ (norm_nonneg _) (hB0 p)` to reduce the goal to its premises. Use `(hCp p hp σ hσ ν y hν hy).trans ?_` and prove the remaining obligations. Apply `div_le_div_of_nonneg_right _ hD.le` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_left _ (hCp0 p)` to reduce the goal to its premises.

Apply `rpow_le_add_inv_pow hy'` to reduce the goal to its premises. Establish `hc : (p.1 : ℝ) + 2 * p.2.1 = p.2.2 + 2 + j` using `by exact_mod_cast (hS p hp).2`. Establish `he : (p.2.2 : ℝ) + 1 - p.1 - 2 * p.2.1 - 2 * σ.re = -(1 + j + 2 * σ.re)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[he, abs_neg]`.

Use `le_trans ?_ (Nat.le_ceil _)` and prove the remaining obligations. Establish `hj : (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_of_nonneg (by linarith), abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]`. Use `_ ≤ 1 + j + 2 * R := by linarith`.

Use `_ = (∑ p ∈ S, B p * Cp p) * (|y| + |y|⁻¹) ^ ⌈1 + (j : ℝ) + 2 * R⌉₊ / (1 + |ν * y|) ^ N := by`. Rewrite using `[Finset.sum_mul, Finset.sum_div]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iteratedDeriv_hTrans_bound :
    (∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y) → (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N := by
  intro hder hint K hK hKH j
  obtain ⟨S, P, hS, hEq⟩ := hder j
  obtain ⟨R, hR⟩ : ∃ R, ∀ σ ∈ K, ‖σ‖ ≤ R := hK.isBounded.exists_norm_le
  refine ⟨⌈1 + (j : ℝ) + 2 * R⌉₊, fun N => ?_⟩
  have hCex : ∀ p : ℕ × ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ (p ∈ S → ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖ ≤
        C * |y| ^ ((p.2.2 : ℝ) + 1 - p.1 - 2 * p.2.1 - 2 * σ.re) / (1 + |ν * y|) ^ N) := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨C, hC⟩ := hint K hK hKH p.1 p.2.1 p.2.2 (hS p hp).1 N
      refine ⟨max C 0, le_max_right _ _, fun _ σ hσ ν y hν hy => (hC σ hσ ν y hν hy).trans ?_⟩
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
    · exact ⟨0, le_rfl, fun h => absurd h hp⟩
  choose Cp hCp0 hCp using hCex
  have hBex : ∀ p : ℕ × ℕ × ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ K, ‖(P p).eval σ‖ ≤ B := by
    intro p
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (P p).continuous.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun σ hσ => (hB σ hσ).trans (le_max_left _ _)⟩
  choose B hB0 hB using hBex
  refine ⟨∑ p ∈ S, B p * Cp p, fun σ hσ ν y hν hy => ?_⟩
  have hy' : 0 < |y| := abs_pos.mpr hy
  have hD : 0 < (1 + |ν * y|) ^ N := by positivity
  have hre : |σ.re| ≤ R := (Complex.abs_re_le_norm σ).trans (hR σ hσ)
  rw [hEq σ (hKH hσ) ν y hy]
  calc ‖∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖
      ≤ ∑ p ∈ S, ‖(P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ S, B p * (Cp p * (|y| + |y|⁻¹) ^ ⌈1 + (j : ℝ) + 2 * R⌉₊ / (1 + |ν * y|) ^ N) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_mul]
        apply mul_le_mul (hB p σ hσ) _ (norm_nonneg _) (hB0 p)
        refine (hCp p hp σ hσ ν y hν hy).trans ?_
        apply div_le_div_of_nonneg_right _ hD.le
        apply mul_le_mul_of_nonneg_left _ (hCp0 p)
        apply rpow_le_add_inv_pow hy'
        have hc : (p.1 : ℝ) + 2 * p.2.1 = p.2.2 + 2 + j := by exact_mod_cast (hS p hp).2
        have he : (p.2.2 : ℝ) + 1 - p.1 - 2 * p.2.1 - 2 * σ.re = -(1 + j + 2 * σ.re) := by
          linarith
        rw [he, abs_neg]
        refine le_trans ?_ (Nat.le_ceil _)
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        calc |1 + (j : ℝ) + 2 * σ.re| ≤ |1 + (j : ℝ)| + |2 * σ.re| := abs_add_le _ _
          _ = 1 + j + 2 * |σ.re| := by
              rw [abs_of_nonneg (by linarith), abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          _ ≤ 1 + j + 2 * R := by linarith
    _ = (∑ p ∈ S, B p * Cp p) * (|y| + |y|⁻¹) ^ ⌈1 + (j : ℝ) + 2 * R⌉₊ / (1 + |ν * y|) ^ N := by
        rw [Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

end GlobalTheory.HeckeTwo.TermBoundDeriv

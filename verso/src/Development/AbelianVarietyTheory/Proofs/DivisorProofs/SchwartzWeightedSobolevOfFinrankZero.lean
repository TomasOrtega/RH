import Mathlib

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ _ _ μ _ hE k n`. Use `haveI : Subsingleton E := Module.finrank_zero_iff.mp hE`. Establish `hcpt : IsCompact (univ : Set E)` using `(Set.subsingleton_univ).isCompact`. Establish `hfin : μ univ ≠ ∞` using `hcpt.measure_lt_top.ne`. Establish `hne : μ univ ≠ 0` using `isOpen_univ.measure_ne_zero μ univ_nonempty`.

Use `set m : ℝ := μ.real univ with hm`. Establish `hmpos : 0 < m` using `ENNReal.toReal_pos hne hfin`. Use `⟨n, Real.sqrt m⁻¹, Real.sqrt_nonneg _, fun f x => ?_⟩` and prove the remaining obligations. Establish `hx : x = 0` using `Subsingleton.elim _ _`. Substitute `hx` using the available equality.

Use `set a : ℝ := ‖iteratedFDeriv ℝ n f (0 : E)‖ with ha`. Establish `ha0 : 0 ≤ a` using `norm_nonneg _`. Establish `h1 : ‖(0 : E)‖ ^ k * a ≤ a`. Apply `mul_le_of_le_one_left ha0` to reduce the goal to its premises. Rewrite using `[norm_zero]`.

Conclude with `pow_le_one₀ le_rfl zero_le_one`. Use `h1.trans ?_` and prove the remaining obligations. Establish `hterm : ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2 ∂μ = m * a ^ 2`. Establish `: (fun z : E => (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2) = fun _ => a ^ 2`. Use function extensionality and compare the values at `z`.

Rewrite using `[Subsingleton.elim z 0, pow_zero, one_mul]`. Rewrite using `[this, integral_const, smul_eq_mul]`. Establish `hnn : ∀ i j : ℕ, 0 ≤ ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ` using `fun i j => integral_nonneg fun z => sq_nonneg _`. Establish `hle : m * a ^ 2 ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ`. Rewrite using `[← hterm]`.

Use `le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (n + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) (Finset.mem_range.mpr (Nat.succ_pos n)))` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun j => ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) (fun j _ => hnn 0 j) (Finset.mem_range.mpr (Nat.lt_succ_self n))`. Rewrite using `[← Real.sqrt_mul (inv_nonneg.mpr hmpos.le)]`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem schwartz_weighted_sobolev_of_finrank_zero :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], finrank ℝ E = 0 → ∀ (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  intro E _ _ _ _ _ μ _ hE k n
  haveI : Subsingleton E := Module.finrank_zero_iff.mp hE
  have hcpt : IsCompact (univ : Set E) := (Set.subsingleton_univ).isCompact
  have hfin : μ univ ≠ ∞ := hcpt.measure_lt_top.ne
  have hne : μ univ ≠ 0 := isOpen_univ.measure_ne_zero μ univ_nonempty
  set m : ℝ := μ.real univ with hm
  have hmpos : 0 < m := ENNReal.toReal_pos hne hfin
  refine ⟨n, Real.sqrt m⁻¹, Real.sqrt_nonneg _, fun f x => ?_⟩
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  set a : ℝ := ‖iteratedFDeriv ℝ n f (0 : E)‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have h1 : ‖(0 : E)‖ ^ k * a ≤ a := by
    apply mul_le_of_le_one_left ha0
    rw [norm_zero]
    exact pow_le_one₀ le_rfl zero_le_one
  refine h1.trans ?_
  have hterm : ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2 ∂μ = m * a ^ 2 := by
    have : (fun z : E => (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2) = fun _ => a ^ 2 := by
      funext z
      rw [Subsingleton.elim z 0, pow_zero, one_mul]
    rw [this, integral_const, smul_eq_mul]
  have hnn : ∀ i j : ℕ, 0 ≤ ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ :=
    fun i j => integral_nonneg fun z => sq_nonneg _
  have hle : m * a ^ 2 ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ := by
    rw [← hterm]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ∑ j ∈ Finset.range (n + 1),
        ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ)
      (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
      (Finset.mem_range.mpr (Nat.succ_pos n)))
    exact Finset.single_le_sum
      (f := fun j => ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ)
      (fun j _ => hnn 0 j) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  rw [← Real.sqrt_mul (inv_nonneg.mpr hmpos.le)]
  apply Real.le_sqrt_of_sq_le
  calc a ^ 2 = m⁻¹ * (m * a ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hmpos.le)

end GlobalTheory

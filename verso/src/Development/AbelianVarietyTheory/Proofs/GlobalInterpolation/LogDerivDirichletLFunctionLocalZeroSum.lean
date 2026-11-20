import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableAtMellinSummatory
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TsumOneDivRpowLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LLocal

/- English proof (translation)
Unfold `analyticOrderNatAt`. Use `congr 1`. Establish `h` using `analyticOrderAt_comp_of_deriv_ne_zero (f := g) (g := fun z : ℂ => c + z) (z₀ := w) (by fun_prop) (by simp)`. Conclude with `h`.
-/
theorem analyticOrderNatAt_comp_const_add (g : ℂ → ℂ) (c w : ℂ) :
    analyticOrderNatAt (fun z => g (c + z)) w = analyticOrderNatAt g (c + w) := by
  unfold analyticOrderNatAt
  congr 1
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := g) (g := fun z : ℂ => c + z) (z₀ := w)
    (by fun_prop) (by simp)
  exact h

/- English proof (translation)
Take `⟨C, hC, H⟩` from `GlobalTheory.LogDerivZeros.main (2/3) (5/6) (by norm_num) (by norm_num) (by norm_num)`. Use `⟨6 * C, by positivity, ?_⟩` and prove the remaining obligations. Introduce `q _ χ hχ t s hs hLs`. Use `set c : ℂ := 3/2 + t * I with hc`. Establish `hcre : c.re = 3/2` using `by simp [hc]`.

Establish `hcn : ‖c‖ ≤ 3/2 + |t|`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)`. Establish `ht : 0 ≤ |t|` using `abs_nonneg t`.

Establish `hd : Differentiable ℂ (LFunction χ)` using `differentiable_LFunction hχ`. Establish `hf : AnalyticOnNhd ℂ (fun z => LFunction χ (c + z)) (Metric.closedBall 0 1)`. Introduce `z _`. Establish `: Differentiable ℂ (fun z => LFunction χ (c + z))` using `hd.comp (by fun_prop)`. Conclude with `this.analyticAt z`.

Establish `hlow : 1/3 ≤ ‖LFunction χ (c + 0)‖`. Use `GlobalTheory.LLower.norm_LFunction_ge q χ c (by rw [hcre]; norm_num)` as an intermediate fact. Rewrite `this` using `[hcre]`. Rewrite using `[add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hf0 : LFunction χ (c + 0) ≠ 0`. Introduce `h`. Rewrite `hlow` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖LFunction χ (c + z)‖ ≤ q * (2 * |t| + 5)`.

Introduce `z hz`. Establish `hz1 : ‖z‖ ≤ 1` using `by simpa using hz`. Establish `hre : 1/2 ≤ (c + z).re`. Use `(abs_le.1 ((Complex.abs_re_le_norm z).trans hz1)).1` as an intermediate fact. Rewrite using `[add_re, hcre]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn : ‖c + z‖ ≤ |t| + 5/2`. Use `norm_add_le c z` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `(GlobalTheory.LGrowth.norm_LFunction_le q χ hχ (c + z) (by linarith)).trans ?_` and prove the remaining obligations.

Rewrite using `[div_le_iff₀ (by linarith)]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨⟨hfin, -⟩, hb⟩` from `H _ _ hf hf0 hM`. Establish `hb'` using `hb (s - c) hs (by simpa using hLs)`. Establish `hset : {w : ℂ | ‖w - c‖ ≤ 5/6 ∧ LFunction χ w = 0} = (fun z => c + z) '' {w : ℂ | ‖w‖ ≤ 5/6 ∧ LFunction χ (c + w) = 0}`.

Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨w - c, ⟨h1, by simpa using h2⟩, by simp⟩`. Introduce and unpack `⟨z, ⟨h1, h2⟩, rfl⟩`.

Conclude with `⟨by simpa using h1, h2⟩`. Rewrite using `[hset]`. Use `⟨hfin.image _, ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_mem_image (fun a _ b _ h => add_left_cancel h)]`. Rewrite `hb'` using `[deriv_comp_const_add]`.

Simplify using `only [analyticOrderNatAt_comp_const_add, add_sub_cancel, sub_sub] at hb'`. Use `hb'.trans ?_` and prove the remaining obligations. Use `set X : ℝ := q * (|t| + 2) with hX`. Establish `hX2 : 2 ≤ X` using `by nlinarith`. Establish `hl2 : Real.log 2 ≤ Real.log X` using `Real.log_le_log (by norm_num) hX2`.

Establish `hl : (1 : ℝ) / 2 ≤ Real.log 2` using `by linarith [Real.log_two_gt_d9]`. Establish `hp : 0 < ‖LFunction χ (c + 0)‖` using `by linarith`. Establish `h8 : q * (2 * |t| + 5) / ‖LFunction χ (c + 0)‖ ≤ 2 ^ 3 * X`. Rewrite using `[div_le_iff₀ hp]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h9` using `Real.log_le_log (by positivity) h8`. Rewrite `h9` using `[Real.log_mul (by norm_num) (by linarith), Real.log_pow]`. Move the coercions through the operations in `at h9`. Establish `: 1 + Real.log (q * (2 * |t| + 5) / ‖LFunction χ (c + 0)‖) ≤ 6 * Real.log X`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem logDeriv_LFunction_local : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}.Finite ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (2/3) (5/6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨6 * C, by positivity, ?_⟩
  intro q _ χ hχ t s hs hLs
  set c : ℂ := 3/2 + t * I with hc
  have hcre : c.re = 3/2 := by simp [hc]
  have hcn : ‖c‖ ≤ 3/2 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have ht : 0 ≤ |t| := abs_nonneg t
  have hd : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ
  have hf : AnalyticOnNhd ℂ (fun z => LFunction χ (c + z)) (Metric.closedBall 0 1) := by
    intro z _
    have : Differentiable ℂ (fun z => LFunction χ (c + z)) := hd.comp (by fun_prop)
    exact this.analyticAt z
  have hlow : 1/3 ≤ ‖LFunction χ (c + 0)‖ := by
    have := GlobalTheory.LLower.norm_LFunction_ge q χ c (by rw [hcre]; norm_num)
    rw [hcre] at this
    rw [add_zero]
    linarith
  have hf0 : LFunction χ (c + 0) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have hM : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖LFunction χ (c + z)‖ ≤ q * (2 * |t| + 5) := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    have hre : 1/2 ≤ (c + z).re := by
      have := (abs_le.1 ((Complex.abs_re_le_norm z).trans hz1)).1
      rw [add_re, hcre]; linarith
    have hn : ‖c + z‖ ≤ |t| + 5/2 := by
      have := norm_add_le c z
      linarith
    refine (GlobalTheory.LGrowth.norm_LFunction_le q χ hχ (c + z) (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    calc (q : ℝ) * ‖c + z‖ ≤ q * (|t| + 5/2) := by gcongr
      _ = q * (2 * |t| + 5) * (1/2) := by ring
      _ ≤ _ := by gcongr
  obtain ⟨⟨hfin, -⟩, hb⟩ := H _ _ hf hf0 hM
  have hb' := hb (s - c) hs (by simpa using hLs)
  have hset : {w : ℂ | ‖w - c‖ ≤ 5/6 ∧ LFunction χ w = 0} =
      (fun z => c + z) '' {w : ℂ | ‖w‖ ≤ 5/6 ∧ LFunction χ (c + w) = 0} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w - c, ⟨h1, by simpa using h2⟩, by simp⟩
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using h1, h2⟩
  rw [hset]
  refine ⟨hfin.image _, ?_⟩
  rw [finsum_mem_image (fun a _ b _ h => add_left_cancel h)]
  rw [deriv_comp_const_add] at hb'
  simp only [analyticOrderNatAt_comp_const_add, add_sub_cancel, sub_sub] at hb'
  refine hb'.trans ?_
  set X : ℝ := q * (|t| + 2) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hl2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
  have hl : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hp : 0 < ‖LFunction χ (c + 0)‖ := by linarith
  have h8 : q * (2 * |t| + 5) / ‖LFunction χ (c + 0)‖ ≤ 2 ^ 3 * X := by
    rw [div_le_iff₀ hp]
    calc (q : ℝ) * (2 * |t| + 5) ≤ 2 ^ 3 * X * (1/3) := by rw [hX]; nlinarith
      _ ≤ _ := by gcongr
  have h9 := Real.log_le_log (by positivity) h8
  rw [Real.log_mul (by norm_num) (by linarith), Real.log_pow] at h9
  push_cast at h9
  have : 1 + Real.log (q * (2 * |t| + 5) / ‖LFunction χ (c + 0)‖) ≤ 6 * Real.log X := by
    linarith
  calc _ ≤ C * (6 * Real.log X) := by gcongr
    _ = _ := by ring

end GlobalTheory.LLocal

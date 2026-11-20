import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LocSer

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero => rw [h1, h0]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ n ih => rw [hr n, ih]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem step (x y : ℂ) (c : ℕ → ℂ) (h1 : c 1 = x + y) (h0 : c 0 = 1)
    (hr : ∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) :
    ∀ r, c (r + 1) = y * c r + x ^ (r + 1) := by
  intro r
  induction r with
  | zero => rw [h1, h0]; ring
  | succ n ih => rw [hr n, ih]; ring

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero => simp [h0]`. Consider the case `succ n ih`. Establish `e : c (n + 1) * z ^ (n + 1) = (y * z) * (c n * z ^ n) + (x * z) ^ (n + 1)`.

Rewrite using `[hs n]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `set ρ := max ‖x * z‖ ‖y * z‖`. Establish `hx : ‖x * z‖ ≤ ρ` using `le_max_left _ _`.

Establish `hy : ‖y * z‖ ≤ ρ` using `le_max_right _ _`. Establish `hρ : 0 ≤ ρ` using `le_trans (norm_nonneg _) hx`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`.

Use `_ ≤ ρ * (((n : ℝ) + 1) * ρ ^ n) + ρ ^ (n + 1) := by gcongr`. Use `_ = (((n + 1 : ℕ) : ℝ) + 1) * ρ ^ (n + 1) := by push_cast; ring`.
-/
theorem bound (x y z : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1)) :
    ∀ r : ℕ, ‖c r * z ^ r‖ ≤ ((r : ℝ) + 1) * (max ‖x * z‖ ‖y * z‖) ^ r := by
  intro r
  induction r with
  | zero => simp [h0]
  | succ n ih =>
    have e : c (n + 1) * z ^ (n + 1) = (y * z) * (c n * z ^ n) + (x * z) ^ (n + 1) := by
      rw [hs n]; ring
    rw [e]
    set ρ := max ‖x * z‖ ‖y * z‖
    have hx : ‖x * z‖ ≤ ρ := le_max_left _ _
    have hy : ‖y * z‖ ≤ ρ := le_max_right _ _
    have hρ : 0 ≤ ρ := le_trans (norm_nonneg _) hx
    calc ‖(y * z) * (c n * z ^ n) + (x * z) ^ (n + 1)‖
        ≤ ‖y * z‖ * ‖c n * z ^ n‖ + ‖x * z‖ ^ (n + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_pow]
      _ ≤ ρ * (((n : ℝ) + 1) * ρ ^ n) + ρ ^ (n + 1) := by
          gcongr
      _ = (((n + 1 : ℕ) : ℝ) + 1) * ρ ^ (n + 1) := by push_cast; ring

/- English proof (translation)
Establish `hn : ‖ρ‖ < 1` using `by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1`. Establish `a` using `summable_pow_mul_geometric_of_norm_lt_one 1 hn`. Establish `b` using `summable_geometric_of_lt_one h0 h1`. Conclude with `(a.add b).congr (fun r => by ring)`.
-/
theorem summ1 (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) * ρ ^ r) := by
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have a := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have b := summable_geometric_of_lt_one h0 h1
  exact (a.add b).congr (fun r => by ring)

/- English proof (translation)
Establish `hn : ‖ρ‖ < 1` using `by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1`. Establish `a` using `summable_pow_mul_geometric_of_norm_lt_one 2 hn`. Establish `a1` using `summable_pow_mul_geometric_of_norm_lt_one 1 hn`. Establish `b` using `summable_geometric_of_lt_one h0 h1`. Conclude with `((a.add (a1.mul_left 2)).add b).congr (fun r => by ring)`.
-/
theorem summ2 (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) ^ 2 * ρ ^ r) := by
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have a := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have a1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have b := summable_geometric_of_lt_one h0 h1
  exact ((a.add (a1.mul_left 2)).add b).congr (fun r => by ring)

/- English proof (translation)
Use `set ρ := max ‖x * z‖ ‖y * z‖`. Establish `hρ1 : ρ < 1` using `max_lt hx hy`. Establish `hρ0 : 0 ≤ ρ` using `le_trans (norm_nonneg _) (le_max_left _ _)`. Establish `hS : Summable (fun r => c r * z ^ r)` using `Summable.of_norm_bounded (summ1 ρ hρ0 hρ1) (bound x y z c h0 hs)`. Use `⟨hS, ?_⟩` and prove the remaining obligations.

Establish `hG` using `tsum_geometric_of_norm_lt_one hx`. Establish `hGs` using `summable_geometric_of_norm_lt_one hx`. Establish `hne : (1 : ℂ) - x * z ≠ 0`. Introduce `h`. Establish `: x * z = 1` using `by linear_combination -h`.

Rewrite `hx` using `[this, norm_one]`. Conclude with `lt_irrefl _ hx`. Establish `hG' : (∑' n : ℕ, (x * z) ^ n) * (1 - x * z) = 1`. Rewrite using `[hG]`. Conclude with `inv_mul_cancel₀ hne`.

Establish `e1` using `hS.tsum_eq_zero_add`. Establish `e2 : ∀ r : ℕ, c (r + 1) * z ^ (r + 1) = (y * z) * (c r * z ^ r) + (x * z) * (x * z) ^ r`. Introduce `r`. Rewrite using `[hs r]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `e1` using `[e2]`. Rewrite `e1` using `[Summable.tsum_add (hS.mul_left _) (hGs.mul_left _), tsum_mul_left, tsum_mul_left, h0]`. Simplify using `only [pow_zero, mul_one] at e1`. Take the linear combination `(1 - x * z) * e1 + (x * z) * hG'`.
-/
theorem part1 (x y z : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1))
    (hx : ‖x * z‖ < 1) (hy : ‖y * z‖ < 1) :
    Summable (fun r => c r * z ^ r) ∧ (∑' r, c r * z ^ r) * ((1 - x * z) * (1 - y * z)) = 1 := by
  set ρ := max ‖x * z‖ ‖y * z‖
  have hρ1 : ρ < 1 := max_lt hx hy
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hS : Summable (fun r => c r * z ^ r) :=
    Summable.of_norm_bounded (summ1 ρ hρ0 hρ1) (bound x y z c h0 hs)
  refine ⟨hS, ?_⟩
  have hG := tsum_geometric_of_norm_lt_one hx
  have hGs := summable_geometric_of_norm_lt_one hx
  have hne : (1 : ℂ) - x * z ≠ 0 := by
    intro h
    have : x * z = 1 := by linear_combination -h
    rw [this, norm_one] at hx; exact lt_irrefl _ hx
  have hG' : (∑' n : ℕ, (x * z) ^ n) * (1 - x * z) = 1 := by
    rw [hG]; exact inv_mul_cancel₀ hne
  have e1 := hS.tsum_eq_zero_add
  have e2 : ∀ r : ℕ, c (r + 1) * z ^ (r + 1) = (y * z) * (c r * z ^ r) + (x * z) * (x * z) ^ r := by
    intro r; rw [hs r]; ring
  simp_rw [e2] at e1
  rw [Summable.tsum_add (hS.mul_left _) (hGs.mul_left _), tsum_mul_left, tsum_mul_left, h0] at e1
  simp only [pow_zero, mul_one] at e1
  linear_combination (1 - x * z) * e1 + (x * z) * hG'

/- English proof (translation)
Establish `hnx : 0 ≤ ‖x‖` using `norm_nonneg _`. Establish `hny : 0 ≤ ‖y‖` using `norm_nonneg _`. Establish `hnT : ‖(T : ℂ)‖ = T` using `by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]`. Establish `hxy : ‖y‖ * (‖x‖ * T) < 1`. Establish `hp` using `mul_lt_mul'' hx hy (by positivity) (by positivity)`.

Establish `e : (‖y‖ * (‖x‖ * T)) ^ 2 = (‖x‖ ^ 2 * T) * (‖y‖ ^ 2 * T)` using `by ring`. Establish `: (‖y‖ * (‖x‖ * T)) ^ 2 < 1` using `by rw [e]; linarith`. Use polynomial arithmetic with `[mul_nonneg hny (mul_nonneg hnx hT0)]`. Use `set m := max ‖x‖ ‖y‖ with hm`. Establish `hσ : m ^ 2 * T < 1`.

Apply the tactic sequence `rcases max_choice ‖x‖ ‖y‖ with h | h <;> rw [hm, h] <;> assumption`. Establish `hb : ∀ r : ℕ, ‖c r‖ ≤ ((r : ℝ) + 1) * m ^ r`. Introduce `r`. Use `bound x y 1 c h0 hs r` as an intermediate fact. Simplify using `using this`.

Establish `hU : Summable (fun r : ℕ => ‖c r‖ ^ 2 * T ^ r)`. Use `Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_) (summ2 (m ^ 2 * T) (by positivity) hσ)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hf : ∀ r : ℕ, c r * conj (c r) * (T : ℂ) ^ r = ((‖c r‖ ^ 2 * T ^ r : ℝ) : ℂ)`. Introduce `r`.

Use `push_cast`. Rewrite using `[Complex.mul_conj']`. Establish `hVs : Summable (fun r : ℕ => c r * conj (c r) * (T : ℂ) ^ r)`. Use `(Complex.summable_ofReal).mpr hU` as an intermediate fact. Conclude with `this.congr (fun r => (hf r).symm)`.

Establish `hVdef : ((∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r : ℝ) : ℂ) = ∑' r : ℕ, c r * conj (c r) * (T : ℂ) ^ r`. Rewrite using `[Complex.ofReal_tsum]`. Use `congr 1`. Use function extensionality and compare the values at `r`. Conclude with `(hf r).symm`.

Establish `hW : Summable (fun r => c r * (conj x * T) ^ r) ∧ (∑' r, c r * (conj x * T) ^ r) * ((1 - x * (conj x * T)) * (1 - y * (conj x * T))) = 1`. Use `part1 x y (conj x * T) c h0 hs ?_ ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj, hnT]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj, hnT]`.

Conclude with `hxy`. Establish `hW' : Summable (fun r => conj (c r) * (x * T) ^ r) ∧ (∑' r, conj (c r) * (x * T) ^ r) * ((1 - conj x * (x * T)) * (1 - conj y * (x * T))) = 1`. Use `part1 (conj x) (conj y) (x * T) (fun r => conj (c r)) (by simp [h0]) ?_ ?_ ?_` and prove the remaining obligations. Introduce `r show conj (c (r + 1)) = conj y * conj (c r) + conj x ^ (r + 1)`. Rewrite using `[hs r]`.

Simplify using `only [map_add, map_mul, map_pow]`. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj, hnT]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj, hnT]`. Combine the linear relations using `[hxy]`.

Establish `hGn : ‖x * conj x * (T : ℂ)‖ < 1`. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj, hnT]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hGs` using `summable_geometric_of_norm_lt_one hGn`. Establish `hG : (∑' n : ℕ, (x * conj x * (T : ℂ)) ^ n) * (1 - x * conj x * T) = 1`.

Rewrite using `[tsum_geometric_of_norm_lt_one hGn]`. Use `inv_mul_cancel₀ ?_` and prove the remaining obligations. Introduce `h`. Establish `: x * conj x * (T : ℂ) = 1` using `by linear_combination -h`. Rewrite `hGn` using `[this, norm_one]`.

Conclude with `lt_irrefl _ hGn`. Establish `e1` using `hVs.tsum_eq_zero_add`. Establish `e2 : ∀ r : ℕ, c (r + 1) * conj (c (r + 1)) * (T : ℂ) ^ (r + 1) = (T : ℂ) * (y * conj y * (c r * conj (c r) * (T : ℂ) ^ r) + y * conj x * (c r * (conj x * T) ^ r) + x * conj y * (conj (c r) * (x * T) ^ r) + x * conj x * (x * conj x * T) ^ r)`. Introduce `r`. Rewrite using `[hs r]`.

Simplify using `only [map_add, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e1` using `[e2]`. Rewrite `e1` using `[tsum_mul_left, Summable.tsum_add (((hVs.mul_left _).add (hW.1.mul_left _)).add (hW'.1.mul_left _)) (hGs.mul_left _), Summable.tsum_add ((hVs.mul_left _).add (hW.1.mul_left _)) (hW'.1.mul_left _), Summable.tsum_add (hVs.mul_left _) (hW.1.mul_left _)]`. Simplify using `only [tsum_mul_left, h0, map_one, pow_zero, mul_one] at e1`.

Establish `hW2` using `hW.2`. Establish `hW'2` using `hW'.2`. Use `set V := ∑' r : ℕ, c r * conj (c r) * (T : ℂ) ^ r`. Use `set W := ∑' r, c r * (conj x * T) ^ r`. Use `set W' := ∑' r, conj (c r) * (x * T) ^ r`.

Use `set G := ∑' n : ℕ, (x * conj x * (T : ℂ)) ^ n`. Establish `key : V * ((1 - x * conj x * T) * (1 - y * conj y * T) * ((1 - x * conj y * T) * (1 - conj x * y * T))) = 1 - x * conj x * (y * conj y) * T ^ 2`. Take the linear combination `((1 - x * conj x * T) * (1 - x * conj y * T) * (1 - conj x * y * T)) * e1 + (T * y * conj x * (1 - x * conj y * T)) * hW2 + (T * x * conj y * (1 - conj x * y * T)) * hW'2 + (x * conj x * T * (1 - x * conj y * T) * (1 - conj x * y * T)) * hG`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_mul, hVdef]`.

Use `push_cast`. Establish `hx2 : ((‖x‖ : ℂ)) ^ 2 = x * conj x` using `(Complex.mul_conj' x).symm`. Establish `hy2 : ((‖y‖ : ℂ)) ^ 2 = y * conj y` using `(Complex.mul_conj' y).symm`. Establish `hxy2 : ((‖x * y‖ : ℂ)) ^ 2 = x * y * conj (x * y)` using `(Complex.mul_conj' _).symm`. Establish `hn2 : ((‖1 - x * conj y * T‖ : ℂ)) ^ 2 = (1 - x * conj y * T) * conj (1 - x * conj y * T)` using `(Complex.mul_conj' _).symm`.

Rewrite using `[hx2, hy2, hxy2, hn2]`. Simplify using `only [map_mul, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]`. Take the linear combination `key`.
-/
theorem part2 (x y : ℂ) (c : ℕ → ℂ) (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T < 1) (hx : ‖x‖ ^ 2 * T < 1)
    (hy : ‖y‖ ^ 2 * T < 1) (h0 : c 0 = 1) (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1)) :
    (∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r) * ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2)
      = 1 - ‖x * y‖ ^ 2 * T ^ 2 := by
  have hnx : 0 ≤ ‖x‖ := norm_nonneg _
  have hny : 0 ≤ ‖y‖ := norm_nonneg _
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
  have hxy : ‖y‖ * (‖x‖ * T) < 1 := by
    have hp := mul_lt_mul'' hx hy (by positivity) (by positivity)
    have e : (‖y‖ * (‖x‖ * T)) ^ 2 = (‖x‖ ^ 2 * T) * (‖y‖ ^ 2 * T) := by ring
    have : (‖y‖ * (‖x‖ * T)) ^ 2 < 1 := by rw [e]; linarith
    nlinarith [mul_nonneg hny (mul_nonneg hnx hT0)]

  set m := max ‖x‖ ‖y‖ with hm
  have hσ : m ^ 2 * T < 1 := by
    rcases max_choice ‖x‖ ‖y‖ with h | h <;> rw [hm, h] <;> assumption
  have hb : ∀ r : ℕ, ‖c r‖ ≤ ((r : ℝ) + 1) * m ^ r := by
    intro r; have := bound x y 1 c h0 hs r; simpa using this
  have hU : Summable (fun r : ℕ => ‖c r‖ ^ 2 * T ^ r) := by
    refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_)
      (summ2 (m ^ 2 * T) (by positivity) hσ)
    calc ‖c r‖ ^ 2 * T ^ r ≤ (((r : ℝ) + 1) * m ^ r) ^ 2 * T ^ r := by
          gcongr; exact hb r
      _ = ((r : ℝ) + 1) ^ 2 * (m ^ 2 * T) ^ r := by ring
  have hf : ∀ r : ℕ, c r * conj (c r) * (T : ℂ) ^ r = ((‖c r‖ ^ 2 * T ^ r : ℝ) : ℂ) := by
    intro r; push_cast; rw [Complex.mul_conj']
  have hVs : Summable (fun r : ℕ => c r * conj (c r) * (T : ℂ) ^ r) := by
    have := (Complex.summable_ofReal).mpr hU
    exact this.congr (fun r => (hf r).symm)
  have hVdef : ((∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r : ℝ) : ℂ) = ∑' r : ℕ, c r * conj (c r) * (T : ℂ) ^ r := by
    rw [Complex.ofReal_tsum]; congr 1; funext r; exact (hf r).symm

  have hW : Summable (fun r => c r * (conj x * T) ^ r) ∧
      (∑' r, c r * (conj x * T) ^ r) * ((1 - x * (conj x * T)) * (1 - y * (conj x * T))) = 1 := by
    refine part1 x y (conj x * T) c h0 hs ?_ ?_
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; exact hxy
  have hW' : Summable (fun r => conj (c r) * (x * T) ^ r) ∧
      (∑' r, conj (c r) * (x * T) ^ r) * ((1 - conj x * (x * T)) * (1 - conj y * (x * T))) = 1 := by
    refine part1 (conj x) (conj y) (x * T) (fun r => conj (c r)) (by simp [h0]) ?_ ?_ ?_
    · intro r
      show conj (c (r + 1)) = conj y * conj (c r) + conj x ^ (r + 1)
      rw [hs r]; simp only [map_add, map_mul, map_pow]
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; linarith [hxy]
  have hGn : ‖x * conj x * (T : ℂ)‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
  have hGs := summable_geometric_of_norm_lt_one hGn
  have hG : (∑' n : ℕ, (x * conj x * (T : ℂ)) ^ n) * (1 - x * conj x * T) = 1 := by
    rw [tsum_geometric_of_norm_lt_one hGn]
    refine inv_mul_cancel₀ ?_
    intro h
    have : x * conj x * (T : ℂ) = 1 := by linear_combination -h
    rw [this, norm_one] at hGn; exact lt_irrefl _ hGn
  have e1 := hVs.tsum_eq_zero_add
  have e2 : ∀ r : ℕ, c (r + 1) * conj (c (r + 1)) * (T : ℂ) ^ (r + 1) =
      (T : ℂ) * (y * conj y * (c r * conj (c r) * (T : ℂ) ^ r) + y * conj x * (c r * (conj x * T) ^ r)
        + x * conj y * (conj (c r) * (x * T) ^ r) + x * conj x * (x * conj x * T) ^ r) := by
    intro r; rw [hs r]; simp only [map_add, map_mul, map_pow]; ring
  simp_rw [e2] at e1
  rw [tsum_mul_left, Summable.tsum_add (((hVs.mul_left _).add (hW.1.mul_left _)).add (hW'.1.mul_left _))
    (hGs.mul_left _), Summable.tsum_add ((hVs.mul_left _).add (hW.1.mul_left _)) (hW'.1.mul_left _),
    Summable.tsum_add (hVs.mul_left _) (hW.1.mul_left _)] at e1
  simp only [tsum_mul_left, h0, map_one, pow_zero, mul_one] at e1
  have hW2 := hW.2
  have hW'2 := hW'.2
  set V := ∑' r : ℕ, c r * conj (c r) * (T : ℂ) ^ r
  set W := ∑' r, c r * (conj x * T) ^ r
  set W' := ∑' r, conj (c r) * (x * T) ^ r
  set G := ∑' n : ℕ, (x * conj x * (T : ℂ)) ^ n
  have key : V * ((1 - x * conj x * T) * (1 - y * conj y * T) * ((1 - x * conj y * T) * (1 - conj x * y * T)))
      = 1 - x * conj x * (y * conj y) * T ^ 2 := by
    linear_combination ((1 - x * conj x * T) * (1 - x * conj y * T) * (1 - conj x * y * T)) * e1
      + (T * y * conj x * (1 - x * conj y * T)) * hW2 + (T * x * conj y * (1 - conj x * y * T)) * hW'2
      + (x * conj x * T * (1 - x * conj y * T) * (1 - conj x * y * T)) * hG
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, hVdef]
  push_cast
  have hx2 : ((‖x‖ : ℂ)) ^ 2 = x * conj x := (Complex.mul_conj' x).symm
  have hy2 : ((‖y‖ : ℂ)) ^ 2 = y * conj y := (Complex.mul_conj' y).symm
  have hxy2 : ((‖x * y‖ : ℂ)) ^ 2 = x * y * conj (x * y) := (Complex.mul_conj' _).symm
  have hn2 : ((‖1 - x * conj y * T‖ : ℂ)) ^ 2 = (1 - x * conj y * T) * conj (1 - x * conj y * T) :=
    (Complex.mul_conj' _).symm
  rw [hx2, hy2, hxy2, hn2]
  simp only [map_mul, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
  linear_combination key

/- English proof (translation)
Introduce `x y c T hT0 hT1 hx hy h0 h1 hr`. Establish `hs` using `step x y c h1 h0 hr`. Establish `hnT : ‖(T : ℂ)‖ = T` using `by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]`. Establish `hsq : ∀ u : ℂ, ‖u‖ ^ 2 * T < 1 → ‖u * (T : ℂ)‖ < 1`. Introduce `u hu`.

Rewrite using `[norm_mul, hnT]`. Establish `hn : 0 ≤ ‖u‖ * T` using `mul_nonneg (norm_nonneg _) hT0`. Establish `: (‖u‖ * T) ^ 2 ≤ ‖u‖ ^ 2 * T`. Establish `: (‖u‖ * T) ^ 2 = (‖u‖ ^ 2 * T) * T` using `by ring`. Rewrite using `[this]`.

Conclude with `mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) hT0) hT1.le`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `⟨(part1 x y T c h0 hs (hsq x hx) (hsq y hy)).2, part2 x y c T hT0 hT1 hx hy h0 hs⟩`.
-/
theorem twoStep_eulerFactors : ∀ (x y : ℂ) (c : ℕ → ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 → c 0 = 1 → c 1 = x + y → (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∑' r : ℕ, c r * (T : ℂ) ^ r) * ((1 - x * T) * (1 - y * T)) = 1 ∧ (∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r) * ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2) = 1 - ‖x * y‖ ^ 2 * T ^ 2 := by
  intro x y c T hT0 hT1 hx hy h0 h1 hr
  have hs := step x y c h1 h0 hr
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
  have hsq : ∀ u : ℂ, ‖u‖ ^ 2 * T < 1 → ‖u * (T : ℂ)‖ < 1 := by
    intro u hu
    rw [norm_mul, hnT]
    have hn : 0 ≤ ‖u‖ * T := mul_nonneg (norm_nonneg _) hT0
    have : (‖u‖ * T) ^ 2 ≤ ‖u‖ ^ 2 * T := by
      have : (‖u‖ * T) ^ 2 = (‖u‖ ^ 2 * T) * T := by ring
      rw [this]
      exact mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) hT0) hT1.le
    nlinarith
  exact ⟨(part1 x y T c h0 hs (hsq x hx) (hsq y hy)).2, part2 x y c T hT0 hT1 hx hy h0 hs⟩

end GlobalTheory.LocSer

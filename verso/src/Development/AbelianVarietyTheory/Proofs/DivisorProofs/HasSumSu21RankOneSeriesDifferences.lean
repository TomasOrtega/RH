import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.SURankOneSeries

/- English proof (translation)
Establish `h : 2 * i / 2 = i` using `by omega`. Rewrite using `[h, div_pow, ← pow_mul, show 2 * i + 2 * i = 2 * (2 * i) by ring, ← pow_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem term_even (q z : ℂ) (hq : q ≠ 0) (i : ℕ) :
    (z / q ^ 2) ^ (2 * i) * q ^ (2 * i + 2 * (2 * i / 2)) = (z ^ 2) ^ i := by
  have h : 2 * i / 2 = i := by omega
  rw [h, div_pow, ← pow_mul, show 2 * i + 2 * i = 2 * (2 * i) by ring, ← pow_mul]
  field_simp

/- English proof (translation)
Establish `h : (2 * i + 1) / 2 = i` using `by omega`. Rewrite using `[h]`. Establish `h4 : 2 * i + 1 + 2 * i = 2 * (2 * i) + 1` using `by ring`. Rewrite using `[h4]`. Simplify using `only [div_pow, ← pow_mul]`.

Rewrite using `[show 2 * (2 * i + 1) = (2 * (2 * i) + 1) + 1 by ring, pow_succ q (2 * (2 * i) + 1)]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem term_odd (q z : ℂ) (hq : q ≠ 0) (i : ℕ) :
    (z / q ^ 2) ^ (2 * i + 1) * q ^ (2 * i + 1 + 2 * ((2 * i + 1) / 2)) = z / q * (z ^ 2) ^ i := by
  have h : (2 * i + 1) / 2 = i := by omega
  rw [h]
  have h4 : 2 * i + 1 + 2 * i = 2 * (2 * i) + 1 := by ring
  rw [h4]
  simp only [div_pow, ← pow_mul]
  rw [show 2 * (2 * i + 1) = (2 * (2 * i) + 1) + 1 by ring, pow_succ q (2 * (2 * i) + 1)]
  field_simp
  ring

/- English proof (translation)
Establish `hz2 : ‖z ^ 2‖ < 1`. Rewrite using `[norm_pow]`. Use polynomial arithmetic with `[norm_nonneg z]`. Establish `hg` using `hasSum_geometric_of_norm_lt_one hz2`. Establish `he : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) (1 - z ^ 2)⁻¹`.

Establish `: (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) = fun k => (z ^ 2) ^ k`. Use function extensionality and compare the values at `fun k => term_even q z hq k`. Rewrite using `[this]`. Conclude with `hg`. Establish `ho : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2))) (z / q * (1 - z ^ 2)⁻¹)`.

Establish `: (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2))) = fun k => z / q * (z ^ 2) ^ k` using `funext fun k => term_odd q z hq k`. Rewrite using `[this]`. Conclude with `hg.mul_left _`. Establish `h1 : (1 : ℂ) - z ^ 2 ≠ 0`. Introduce `h`.

Establish `: z ^ 2 = 1` using `by linear_combination -h`. Establish `: ‖z ^ 2‖ = 1` using `by rw [this, norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : (1 - z ^ 2)⁻¹ + z / q * (1 - z ^ 2)⁻¹ = (1 + q⁻¹ * z) / (1 - z ^ 2)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[← e]`. Conclude with `HasSum.even_add_odd (f := fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) he ho`.
-/
theorem hasSum_weighted (q z : ℂ) (hq : q ≠ 0) (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) ((1 + q⁻¹ * z) / (1 - z ^ 2)) := by
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg z]
  have hg := hasSum_geometric_of_norm_lt_one hz2
  have he : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) (1 - z ^ 2)⁻¹ := by
    have : (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) = fun k => (z ^ 2) ^ k :=
      funext fun k => term_even q z hq k
    rw [this]; exact hg
  have ho : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2)))
      (z / q * (1 - z ^ 2)⁻¹) := by
    have : (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2))) =
        fun k => z / q * (z ^ 2) ^ k := funext fun k => term_odd q z hq k
    rw [this]; exact hg.mul_left _
  have h1 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = 1 := by linear_combination -h
    have : ‖z ^ 2‖ = 1 := by rw [this, norm_one]
    linarith
  have e : (1 - z ^ 2)⁻¹ + z / q * (1 - z ^ 2)⁻¹ = (1 + q⁻¹ * z) / (1 - z ^ 2) := by
    field_simp
  rw [← e]
  exact HasSum.even_add_odd (f := fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) he ho

/- English proof (translation)
Introduce `q hq z hz`. Establish `hq0 : (q : ℂ) ≠ 0` using `by exact_mod_cast (by omega : q ≠ 0)`. Establish `hA` using `hasSum_weighted (q : ℂ) z hq0 hz`. Use `set w : ℂ := z / (q : ℂ) ^ 2 with hw`. Use `set S : ℂ := (1 + (q : ℂ)⁻¹ * z) / (1 - z ^ 2) with hS`.

Use `set a : ℕ → ℂ := fun j => w ^ j * (q : ℂ) ^ (j + 2 * (j / 2)) with ha`. Use `set b : ℕ → ℂ := fun j => if j = 0 then 0 else w * a (j - 1) with hb`. Establish `hB : HasSum b (w * S)`. Use `(hasSum_nat_add_iff' 1).mp ?_` and prove the remaining obligations. Establish `e : (fun n => b (n + 1)) = fun n => w * a n`.

Use function extensionality and compare the values at `n`. Simplify using `[hb]`. Rewrite using `[e]`. Simplify `hA.mul_left w` using `[hb]`. Establish `hfun : (fun j : ℕ => w ^ j * ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) = fun j => a j - b j`.

Use function extensionality and compare the values at `j`. Break down `j with _ | n` into its components or cases. Simplify using `[ha, hb]`. Simplify using `only [ha, hb, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]`. Rewrite using `[pow_succ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`. Establish `h1 : (1 : ℂ) - z ^ 2 ≠ 0`. Introduce `h`. Establish `: z ^ 2 = 1` using `by linear_combination -h`.

Establish `: ‖z ^ 2‖ = 1` using `by rw [this, norm_one]`. Rewrite `this` using `[norm_pow]`. Use polynomial arithmetic with `[norm_nonneg z]`. Establish `e : cSU (q : ℂ) z = S - w * S`. Rewrite using `[cSU, hS, hw]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `hA.sub hB`.
-/
theorem hasSum_series : ∀ (q : ℕ), 2 ≤ q → ∀ z : ℂ, ‖z‖ < 1 →
    HasSum (fun j : ℕ => (z / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) (cSU q z) := by
  intro q hq z hz
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hA := hasSum_weighted (q : ℂ) z hq0 hz
  set w : ℂ := z / (q : ℂ) ^ 2 with hw
  set S : ℂ := (1 + (q : ℂ)⁻¹ * z) / (1 - z ^ 2) with hS
  set a : ℕ → ℂ := fun j => w ^ j * (q : ℂ) ^ (j + 2 * (j / 2)) with ha
  set b : ℕ → ℂ := fun j => if j = 0 then 0 else w * a (j - 1) with hb
  have hB : HasSum b (w * S) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    have e : (fun n => b (n + 1)) = fun n => w * a n := by
      funext n; simp [hb]
    rw [e]
    simpa [hb] using hA.mul_left w
  have hfun : (fun j : ℕ => w ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) =
      fun j => a j - b j := by
    funext j
    rcases j with _ | n
    · simp [ha, hb]
    · simp only [ha, hb, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [pow_succ]; ring
  rw [hfun]
  have h1 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = 1 := by linear_combination -h
    have : ‖z ^ 2‖ = 1 := by rw [this, norm_one]
    rw [norm_pow] at this
    nlinarith [norm_nonneg z]
  have e : cSU (q : ℂ) z = S - w * S := by
    rw [cSU, hS, hw]
    field_simp
  rw [e]
  exact hA.sub hB

end GlobalTheory.SURankOneSeries

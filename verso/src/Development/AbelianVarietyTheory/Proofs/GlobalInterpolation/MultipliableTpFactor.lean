import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta

open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

def qPoch (t : ℂ) (m : ℕ) : ℂ := ∏ i ∈ Finset.range m, (1 - t ^ (i + 1))

def qPochInf (t : ℂ) : ℂ := ∏' i : ℕ, (1 - t ^ (i + 1))

def qBinom (t : ℂ) (m k : ℕ) : ℂ := qPoch t m / (qPoch t k * qPoch t (m - k))

def finCoeff (t : ℂ) (n : ℕ) (j : ℤ) : ℂ :=
  if j.natAbs ≤ n then qBinom t (2 * n) ((n : ℤ) + j).toNat else 0

/- English proof (translation)
Establish `hg : Summable (fun i : ℕ => ‖t‖ * ‖t‖ ^ i)` using `(summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left ‖t‖`. Establish `hsum : Summable (fun i : ℕ => ‖-(t ^ (i + 1))‖)` using `hg.congr (fun i => by rw [norm_neg, norm_pow, pow_succ, mul_comm])`. Establish `hne : ∀ i : ℕ, 1 + -(t ^ (i + 1)) ≠ 0`. Introduce `i h`. Establish `h1 : t ^ (i + 1) = 1` using `by linear_combination -h`.

Establish `h2 : ‖t‖ ^ (i + 1) < 1` using `pow_lt_one₀ (norm_nonneg t) ht (by omega)`. Rewrite `h2` using `[← norm_pow, h1, norm_one]`. Conclude with `lt_irrefl _ h2`. Establish `hm` using `multipliable_one_add_of_summable hsum`. Establish `h0` using `tprod_one_add_ne_zero_of_summable hne hsum`.

Simplify using `only [← sub_eq_add_neg] at hm h0 hne`. Use `⟨hm.hasProd.tendsto_prod_nat, h0, fun m => Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)⟩` and prove the remaining obligations.
-/
theorem qPoch_tendsto (t : ℂ) (ht : ‖t‖ < 1) :
    Filter.Tendsto (qPoch t) Filter.atTop (nhds (qPochInf t)) ∧ qPochInf t ≠ 0 ∧
      ∀ m, qPoch t m ≠ 0 := by
  have hg : Summable (fun i : ℕ => ‖t‖ * ‖t‖ ^ i) :=
    (summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left ‖t‖
  have hsum : Summable (fun i : ℕ => ‖-(t ^ (i + 1))‖) :=
    hg.congr (fun i => by rw [norm_neg, norm_pow, pow_succ, mul_comm])
  have hne : ∀ i : ℕ, 1 + -(t ^ (i + 1)) ≠ 0 := by
    intro i h
    have h1 : t ^ (i + 1) = 1 := by linear_combination -h
    have h2 : ‖t‖ ^ (i + 1) < 1 := pow_lt_one₀ (norm_nonneg t) ht (by omega)
    rw [← norm_pow, h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hm := multipliable_one_add_of_summable hsum
  have h0 := tprod_one_add_ne_zero_of_summable hne hsum
  simp only [← sub_eq_add_neg] at hm h0 hne
  refine ⟨hm.hasProd.tendsto_prod_nat, h0, fun m => Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)⟩

/- English proof (translation)
Unfold `GlobalTheory.ThetaWeberRoad.tpFactor`. Rewrite using `[← pow_mul, ← exp_nat_mul, ← exp_nat_mul, ← exp_neg, ← exp_add, ← exp_add]`. Rewrite using `[mul_assoc]`. Apply the tactic sequence `congr 3 <;> push_cast <;> ring_nf`.
-/
theorem tpFactor_eq (τ : ℍ) (z : ℂ) (k : ℕ) :
    GlobalTheory.ThetaWeberRoad.tpFactor τ z k = (1 - (cexp (π * I * (τ : ℂ)) ^ 2) ^ (k + 1)) *
      ((1 + cexp (2 * π * I * z) * cexp (π * I * (τ : ℂ)) ^ (2 * k + 1)) *
        (1 + (cexp (2 * π * I * z))⁻¹ * cexp (π * I * (τ : ℂ)) ^ (2 * k + 1))) := by
  unfold GlobalTheory.ThetaWeberRoad.tpFactor
  rw [← pow_mul, ← exp_nat_mul, ← exp_nat_mul, ← exp_neg, ← exp_add, ← exp_add]
  rw [mul_assoc]
  congr 3 <;> push_cast <;> ring_nf

/- English proof (translation)
Unfold `jacobiTheta₂_term`. Rewrite using `[← exp_int_mul, ← exp_int_mul, ← exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jacobiTheta₂_term_eq_zpow (τ z : ℂ) (j : ℤ) :
    jacobiTheta₂_term j z τ = cexp (2 * π * I * z) ^ j * cexp (π * I * τ) ^ (j ^ 2) := by
  unfold jacobiTheta₂_term
  rw [← exp_int_mul, ← exp_int_mul, ← exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[norm_exp, ← Real.exp_zero, Real.exp_lt_exp]`. Establish `: (π * I * τ).re = -(π * τ.im)` using `by simp`. Rewrite using `[this]`. Use `Real.pi_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_exp_pi_I_lt_one (τ : ℂ) (hτ : 0 < τ.im) : ‖cexp (π * I * τ)‖ < 1 := by
  rw [norm_exp, ← Real.exp_zero, Real.exp_lt_exp]
  have : (π * I * τ).re = -(π * τ.im) := by simp
  rw [this]
  have := Real.pi_pos
  nlinarith

/- English proof (translation)
Use `set s := cexp (π * I * (τ : ℂ)) with hs`. Use `set x := cexp (2 * π * I * z) with hx`. Establish `hs1 : ‖s‖ < 1` using `norm_exp_pi_I_lt_one (τ : ℂ) τ.2`. Establish `g : Summable (fun k : ℕ => (‖s‖ ^ 2) ^ k)` using `summable_geometric_of_lt_one (by positivity) (by nlinarith [norm_nonneg s])`. Establish `h1 : Multipliable (fun k : ℕ => 1 + -((s ^ 2) ^ (k + 1)))` using `multipliable_one_add_of_summable ((g.mul_left (‖s‖ ^ 2)).congr (fun k => by`.

Rewrite using `[norm_neg, norm_pow, norm_pow, pow_succ]`. Use the proof step `ring))`. Establish `h2 : Multipliable (fun k : ℕ => 1 + x * s ^ (2 * k + 1))` using `multipliable_one_add_of_summable ((g.mul_left (‖x‖ * ‖s‖)).congr (fun k => by`. Rewrite using `[norm_mul, norm_pow]`. Use the proof step `ring))`.

Establish `h3 : Multipliable (fun k : ℕ => 1 + x⁻¹ * s ^ (2 * k + 1))` using `multipliable_one_add_of_summable ((g.mul_left (‖x⁻¹‖ * ‖s‖)).congr (fun k => by`. Rewrite using `[norm_mul, norm_pow]`. Use the proof step `ring))`. Use `h1.mul (h2.mul h3) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Rewrite using `[tpFactor_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem multipliable_tpFactor (τ : ℍ) (z : ℂ) :
    Multipliable (GlobalTheory.ThetaWeberRoad.tpFactor τ z) := by
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) τ.2
  have g : Summable (fun k : ℕ => (‖s‖ ^ 2) ^ k) :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith [norm_nonneg s])
  have h1 : Multipliable (fun k : ℕ => 1 + -((s ^ 2) ^ (k + 1))) :=
    multipliable_one_add_of_summable ((g.mul_left (‖s‖ ^ 2)).congr (fun k => by
      rw [norm_neg, norm_pow, norm_pow, pow_succ]; ring))
  have h2 : Multipliable (fun k : ℕ => 1 + x * s ^ (2 * k + 1)) :=
    multipliable_one_add_of_summable ((g.mul_left (‖x‖ * ‖s‖)).congr (fun k => by
      rw [norm_mul, norm_pow]; ring))
  have h3 : Multipliable (fun k : ℕ => 1 + x⁻¹ * s ^ (2 * k + 1)) :=
    multipliable_one_add_of_summable ((g.mul_left (‖x⁻¹‖ * ‖s‖)).congr (fun k => by
      rw [norm_mul, norm_pow]; ring))
  convert h1.mul (h2.mul h3) using 1
  funext k
  rw [tpFactor_eq]
  ring

end GlobalTheory.JacobiTriple

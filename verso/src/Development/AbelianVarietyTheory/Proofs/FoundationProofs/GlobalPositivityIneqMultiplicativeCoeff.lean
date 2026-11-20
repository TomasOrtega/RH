import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPositivityEulerFactorPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowInvOneSubOneDivRpowLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowZetaTwoAddLeTwoStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `b s hs hb1 hmul hsum`. Establish `hn : Summable (fun n : ℕ => ‖LSeries.term b ((1 + s : ℝ) : ℂ) n‖)`. Establish `h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + s))` using `Real.summable_one_div_nat_rpow.2 (by linarith)`. Use `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hsum.add h1)` and prove the remaining obligations. Rewrite using `[LSeries.norm_term_eq]`.

Use `split_ifs with h0`. Check the signs of the components of the expression. Rewrite using `[Complex.ofReal_re, ← add_div]`. Apply `div_le_div_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Use polynomial arithmetic with `[sq_nonneg (‖b n‖ - 1), norm_nonneg (b n)]`.

Use `EulerProduct.eulerProduct (f := LSeries.term b ((1 + s : ℝ) : ℂ)) ?_ ?_ hn ?_` and prove the remaining obligations. Simplify using `[LSeries.term, hb1]`. Introduce `m n hmn`. Break down `eq_or_ne m 0 with rfl | hm` into its components or cases. Simplify using the standard rewrite rules.

Break down `eq_or_ne n 0 with rfl | hn0` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero (mul_ne_zero hm hn0), hmul m n hmn, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, div_mul_div_comm]`. Simplify using the standard rewrite rules.
-/
theorem tendsto_eulerProduct_LSeries_of_sq : ∀ (b : ℕ → ℂ) (s : ℝ), 0 < s → b 1 = 1 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)) atTop (𝓝 (LSeries b ((1 + s : ℝ) : ℂ))) := by
  intro b s hs hb1 hmul hsum
  have hn : Summable (fun n : ℕ => ‖LSeries.term b ((1 + s : ℝ) : ℂ) n‖) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + s)) :=
      Real.summable_one_div_nat_rpow.2 (by linarith)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hsum.add h1)
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · positivity
    · rw [Complex.ofReal_re, ← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (‖b n‖ - 1), norm_nonneg (b n)]
  refine EulerProduct.eulerProduct (f := LSeries.term b ((1 + s : ℝ) : ℂ)) ?_ ?_ hn ?_
  · simp [LSeries.term, hb1]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn0,
      LSeries.term_of_ne_zero (mul_ne_zero hm hn0), hmul m n hmn, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, div_mul_div_comm]
  · simp

/- English proof (translation)
Introduce `b s hb1 hmul hsum N`. Establish `h0 : ∀ n : ℕ, 0 ≤ ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)` using `fun n => by positivity`. Establish `key` using `EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers (f := fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) (by simp [hb1]) (fun {m n} hmn => by`. Simplify using `only [hmul m n hmn, norm_mul, mul_pow, Nat.cast_mul]`. Rewrite using `[Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm])`.

Use the proof step `(by simpa only [Real.norm_of_nonneg (h0 _)] using hsum) N`. Rewrite using `[key]`. Conclude with `hsum.tsum_subtype_le _ _ h0`.
-/
theorem prod_primesBelow_sq_le_tsum : ∀ (b : ℕ → ℂ) (s : ℝ), b 1 = 1 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) ≤ ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro b s hb1 hmul hsum N
  have h0 : ∀ n : ℕ, 0 ≤ ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := fun n => by positivity
  have key := EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers
    (f := fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) (by simp [hb1])
    (fun {m n} hmn => by
      simp only [hmul m n hmn, norm_mul, mul_pow, Nat.cast_mul]
      rw [Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm])
    (by simpa only [Real.norm_of_nonneg (h0 _)] using hsum) N
  rw [key]
  exact hsum.tsum_subtype_le _ _ h0

/- English proof (translation)
Introduce `M b ω s C hs hb1 hb0 hmul hbM hrec hC hsum X`. Use `set f : ℕ → ℝ := fun n => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hf`. Use `set Ssum := ∑' n : ℕ, f n`. Use `set Lp : ℕ → ℂ := fun p => ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) with hLp`. Use `set Rp : ℕ → ℝ := fun p => ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) with hRp`.

Use `set α : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ with hα`. Use `set β : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ with hβ`. Use `set A : ℕ → ℝ := fun p => if ¬ p ∣ M then ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) else 0 with hA`. Establish `hA0 : ∀ p, 0 ≤ A p` using `fun p => by`. Apply the tactic sequence `simp only [hA]; split_ifs <;> positivity`.

Establish `hα1 : ∀ p : ℕ, p.Prime → 1 ≤ α p`. Introduce `p hp`. Establish `h1 : (1 : ℝ) < (p : ℝ) ^ (1 + s)` using `Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)`. Establish `h2 : 0 < 1 / (p : ℝ) ^ (1 + s)` using `by positivity`. Establish `h3 : 1 / (p : ℝ) ^ (1 + s) < 1` using `by rw [div_lt_one (by linarith)]; exact h1`.

Simplify using `only [hα]`. Rewrite using `[one_le_inv₀ (by linarith)]; linarith`. Establish `hβ1 : ∀ p : ℕ, p.Prime → 1 ≤ β p`. Introduce `p hp`. Establish `h1 : (1 : ℝ) < (p : ℝ) ^ (2 * (1 + s))` using `Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)`.

Establish `h2 : 0 < 1 / (p : ℝ) ^ (2 * (1 + s))` using `by positivity`. Establish `h3 : 1 / (p : ℝ) ^ (2 * (1 + s)) < 1` using `by rw [div_lt_one (by linarith)]; exact h1`. Simplify using `only [hβ]`. Rewrite using `[one_le_inv₀ (by linarith)]; linarith`. Establish `hdiv : ∀ p : ℕ, p.Prime → p ∣ M → Lp p = 1 ∧ Rp p = 1`.

Introduce `p hp hpM`. Establish `hz : ∀ e : ℕ, e ≠ 0 → b (p ^ e) = 0`. Introduce `e he`. Apply `hbM` to reduce the goal to its premises. Introduce `hc`.

Establish `: p ∣ Nat.gcd (p ^ e) M` using `Nat.dvd_gcd (dvd_pow_self p he) hpM`. Rewrite `this` using `[hc]`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.mp this)`. Prove the components needed by the constructor for the conclusion. Simplify using `only [hLp]`.

Rewrite using `[tsum_eq_single 0]`. Simplify using `[LSeries.term, hb1]`. Introduce `e he`. Simplify using `[LSeries.term, hz e he]`. Simplify using `only [hRp]`.

Rewrite using `[tsum_eq_single 0]`. Simplify using `[hb1]`. Introduce `e he`. Simplify using `[hz e he]`. Establish `hRp0 : ∀ p, 0 ≤ Rp p` using `fun p => tsum_nonneg (fun e => by positivity)`.

Establish `hα0 : ∀ p : ℕ, p.Prime → 0 ≤ α p` using `fun p hp => le_trans zero_le_one (hα1 p hp)`. Establish `hβ0 : ∀ p : ℕ, p.Prime → 0 ≤ β p` using `fun p hp => le_trans zero_le_one (hβ1 p hp)`. Establish `hloc : ∀ p : ℕ, p.Prime → Real.exp (A p) ≤ α p * ‖Lp p‖ ^ 2 * Rp p * β p`. Introduce `p hp`. Distinguish the cases in `hpM : p ∣ M`.

Take `⟨h1, h2⟩` from `hdiv p hp hpM`. Simplify using `only [hA, hpM, not_true_eq_false, if_false, Real.exp_zero, h1, h2, norm_one, one_pow, mul_one]`. Use polynomial arithmetic with `[hα1 p hp, hβ1 p hp]`. Use `GlobalTheory.T.local_positivity_eulerFactor_prime b ω s C p hs hp hb1 (hrec p 1 hp hpM).1 (fun r => (hrec p r hp hpM).2) hC` as an intermediate fact. Simplify `this` using `only [hA, hpM, not_false_eq_true, if_true]`.

Establish `hfin : ∀ N : ℕ, X ≤ N → Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum`. Introduce `N hN`. Establish `e1 : ∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) = ∑ p ∈ X.primesBelow, A p`. Rewrite using `[Nat.primesBelow, Finset.sum_filter, Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations.

Apply the tactic sequence `by_cases h1 : p.Prime <;> by_cases h2 : p ∣ M <;> simp [hA, h1, h2]`. Establish `e2 : ∑ p ∈ X.primesBelow, A p ≤ ∑ p ∈ N.primesBelow, A p` using `Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesBelow_mono hN) (fun p _ _ => hA0 p)`. Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, norm_prod, Finset.prod_pow]`.

Use `_ ≤ (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum * 2 := by`. Establish `a1` using `GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_le s hs N`. Establish `a2` using `GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_two_mul_le s hs.le N`. Establish `a3` using `prod_primesBelow_sq_le_tsum b s hb1 hmul hsum N`. Establish `p1 : 0 ≤ ∏ p ∈ N.primesBelow, α p` using `Finset.prod_nonneg (fun p hp => hα0 p (Nat.prime_of_mem_primesBelow hp))`.

Establish `p2 : 0 ≤ ∏ p ∈ N.primesBelow, Rp p` using `Finset.prod_nonneg (fun p _ => hRp0 p)`. Establish `p3 : 0 ≤ ∏ p ∈ N.primesBelow, β p` using `Finset.prod_nonneg (fun p hp => hβ0 p (Nat.prime_of_mem_primesBelow hp))`. Use `gcongr`. Use `_ = 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by ring`. Establish `hlim` using `tendsto_eulerProduct_LSeries_of_sq b s hs hb1 hmul hsum`.

Establish `hcont : Tendsto (fun N : ℕ => 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum) atTop (𝓝 (2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * Ssum))` using `((hlim.norm.pow 2).const_mul _).mul_const _`. Conclude with `ge_of_tendsto hcont (Filter.eventually_atTop.mpr ⟨X, hfin⟩)`.
-/
theorem global_positivity_ineq : ∀ (M : ℕ) (b ω : ℕ → ℂ) (s C : ℝ), 0 < s → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ X : ℕ, Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro M b ω s C hs hb1 hb0 hmul hbM hrec hC hsum X
  set f : ℕ → ℝ := fun n => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hf
  set Ssum := ∑' n : ℕ, f n
  set Lp : ℕ → ℂ := fun p => ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) with hLp
  set Rp : ℕ → ℝ := fun p => ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) with hRp
  set α : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ with hα
  set β : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ with hβ
  set A : ℕ → ℝ := fun p => if ¬ p ∣ M then ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) else 0 with hA
  have hA0 : ∀ p, 0 ≤ A p := fun p => by
    simp only [hA]; split_ifs <;> positivity

  have hα1 : ∀ p : ℕ, p.Prime → 1 ≤ α p := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ (1 + s) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    have h2 : 0 < 1 / (p : ℝ) ^ (1 + s) := by positivity
    have h3 : 1 / (p : ℝ) ^ (1 + s) < 1 := by rw [div_lt_one (by linarith)]; exact h1
    simp only [hα]
    rw [one_le_inv₀ (by linarith)]; linarith
  have hβ1 : ∀ p : ℕ, p.Prime → 1 ≤ β p := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ (2 * (1 + s)) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    have h2 : 0 < 1 / (p : ℝ) ^ (2 * (1 + s)) := by positivity
    have h3 : 1 / (p : ℝ) ^ (2 * (1 + s)) < 1 := by rw [div_lt_one (by linarith)]; exact h1
    simp only [hβ]
    rw [one_le_inv₀ (by linarith)]; linarith

  have hdiv : ∀ p : ℕ, p.Prime → p ∣ M → Lp p = 1 ∧ Rp p = 1 := by
    intro p hp hpM
    have hz : ∀ e : ℕ, e ≠ 0 → b (p ^ e) = 0 := by
      intro e he
      apply hbM
      intro hc
      have : p ∣ Nat.gcd (p ^ e) M := Nat.dvd_gcd (dvd_pow_self p he) hpM
      rw [hc] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    constructor
    · simp only [hLp]
      rw [tsum_eq_single 0]
      · simp [LSeries.term, hb1]
      · intro e he; simp [LSeries.term, hz e he]
    · simp only [hRp]
      rw [tsum_eq_single 0]
      · simp [hb1]
      · intro e he; simp [hz e he]
  have hRp0 : ∀ p, 0 ≤ Rp p := fun p => tsum_nonneg (fun e => by positivity)
  have hα0 : ∀ p : ℕ, p.Prime → 0 ≤ α p := fun p hp => le_trans zero_le_one (hα1 p hp)
  have hβ0 : ∀ p : ℕ, p.Prime → 0 ≤ β p := fun p hp => le_trans zero_le_one (hβ1 p hp)

  have hloc : ∀ p : ℕ, p.Prime → Real.exp (A p) ≤ α p * ‖Lp p‖ ^ 2 * Rp p * β p := by
    intro p hp
    by_cases hpM : p ∣ M
    · obtain ⟨h1, h2⟩ := hdiv p hp hpM
      simp only [hA, hpM, not_true_eq_false, if_false, Real.exp_zero, h1, h2, norm_one, one_pow, mul_one]
      nlinarith [hα1 p hp, hβ1 p hp]
    · have := GlobalTheory.T.local_positivity_eulerFactor_prime b ω s C p hs hp hb1 (hrec p 1 hp hpM).1 (fun r => (hrec p r hp hpM).2) hC
      simpa only [hA, hpM, not_false_eq_true, if_true] using this

  have hfin : ∀ N : ℕ, X ≤ N → Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by
    intro N hN
    have e1 : ∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) = ∑ p ∈ X.primesBelow, A p := by
      rw [Nat.primesBelow, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h1 : p.Prime <;> by_cases h2 : p ∣ M <;> simp [hA, h1, h2]
    have e2 : ∑ p ∈ X.primesBelow, A p ≤ ∑ p ∈ N.primesBelow, A p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesBelow_mono hN) (fun p _ _ => hA0 p)
    rw [e1]
    calc Real.exp (∑ p ∈ X.primesBelow, A p) ≤ Real.exp (∑ p ∈ N.primesBelow, A p) := Real.exp_le_exp.mpr e2
      _ = ∏ p ∈ N.primesBelow, Real.exp (A p) := Real.exp_sum _ _
      _ ≤ ∏ p ∈ N.primesBelow, (α p * ‖Lp p‖ ^ 2 * Rp p * β p) :=
          Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) (fun p hp => hloc p (Nat.prime_of_mem_primesBelow hp))
      _ = (∏ p ∈ N.primesBelow, α p) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * (∏ p ∈ N.primesBelow, Rp p) * (∏ p ∈ N.primesBelow, β p) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, norm_prod, Finset.prod_pow]
      _ ≤ (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum * 2 := by
          have a1 := GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_le s hs N
          have a2 := GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_two_mul_le s hs.le N
          have a3 := prod_primesBelow_sq_le_tsum b s hb1 hmul hsum N
          have p1 : 0 ≤ ∏ p ∈ N.primesBelow, α p := Finset.prod_nonneg (fun p hp => hα0 p (Nat.prime_of_mem_primesBelow hp))
          have p2 : 0 ≤ ∏ p ∈ N.primesBelow, Rp p := Finset.prod_nonneg (fun p _ => hRp0 p)
          have p3 : 0 ≤ ∏ p ∈ N.primesBelow, β p := Finset.prod_nonneg (fun p hp => hβ0 p (Nat.prime_of_mem_primesBelow hp))
          gcongr
      _ = 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by ring
  have hlim := tendsto_eulerProduct_LSeries_of_sq b s hs hb1 hmul hsum
  have hcont : Tendsto (fun N : ℕ => 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum) atTop (𝓝 (2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * Ssum)) :=
    ((hlim.norm.pow 2).const_mul _).mul_const _
  exact ge_of_tendsto hcont (Filter.eventually_atTop.mpr ⟨X, hfin⟩)

end GlobalTheory.EisM

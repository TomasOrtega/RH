import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Formalism.REAL Finset

namespace GlobalTheory

/- English proof (translation)
Establish `hc : ∀ (f : N →ₗ[ℂ] ℂ) (k : ℕ), (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i))).coeff k = f (a k)`. Introduce `f k`. Rewrite using `[Polynomial.finsetSum_coeff]`. Simplify using `only [Polynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`.

Use `split_ifs with hk`. Both sides reduce to the same expression. Rewrite using `[ha k (by simpa using hk), map_zero]`. Establish `key : ∀ f : N →ₗ[ℂ] ℂ, Polynomial.X * (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i))) + (∑ i ∈ Finset.range M, Polynomial.monomial i ((f ∘ₗ Ω) (a i))) = p * Polynomial.C (f w)`. Introduce `f`.

Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `u`. Establish `h1` using `congrArg f (h u)`. Simplify using `only [map_add, map_smul, map_sum, smul_eq_mul] at h1`. Simplify using `only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_C, LinearMap.comp_apply]`.

Rewrite using `[← h1]`. Simplify using `only [mul_comm]`. Use `⟨?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `f`.

Establish `h1` using `congrArg (fun P => Polynomial.coeff P 0) (key f)`. Simplify using `only [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, hc, Polynomial.coeff_mul_C, zero_add] at h1`. Rewrite `h1` using `[LinearMap.comp_apply]`. Rewrite using `[map_sub, map_smul, smul_eq_mul, h1, sub_self]`. Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`.

Introduce `f`. Establish `h1` using `congrArg (fun P => Polynomial.coeff P (k + 1)) (key f)`. Simplify using `only [Polynomial.coeff_add, Polynomial.coeff_X_mul, hc, Polynomial.coeff_mul_C] at h1`. Rewrite `h1` using `[LinearMap.comp_apply]`. Rewrite using `[map_sub, map_add, map_smul, smul_eq_mul, h1, sub_self]`.
-/
theorem shift_coeff_of_eval_identity {N : Type} [AddCommGroup N] [Module ℂ N]
    (Ω : Module.End ℂ N) (M : ℕ) (a : ℕ → N) (ha : ∀ i, M ≤ i → a i = 0) (p : Polynomial ℂ)
    (w : N) (h : ∀ u : ℂ, u • (∑ i ∈ Finset.range M, u ^ i • a i)
      + Ω (∑ i ∈ Finset.range M, u ^ i • a i) = p.eval u • w) :
    Ω (a 0) = p.coeff 0 • w ∧ ∀ k, a k + Ω (a (k + 1)) = p.coeff (k + 1) • w := by
  have hc : ∀ (f : N →ₗ[ℂ] ℂ) (k : ℕ),
      (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i))).coeff k = f (a k) := by
    intro f k
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hk
    · rfl
    · rw [ha k (by simpa using hk), map_zero]
  have key : ∀ f : N →ₗ[ℂ] ℂ,
      Polynomial.X * (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i)))
        + (∑ i ∈ Finset.range M, Polynomial.monomial i ((f ∘ₗ Ω) (a i)))
        = p * Polynomial.C (f w) := by
    intro f
    apply Polynomial.funext
    intro u
    have h1 := congrArg f (h u)
    simp only [map_add, map_smul, map_sum, smul_eq_mul] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_C,
      LinearMap.comp_apply]
    rw [← h1]
    simp only [mul_comm]
  refine ⟨?_, fun k => ?_⟩
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h1 := congrArg (fun P => Polynomial.coeff P 0) (key f)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, hc, Polynomial.coeff_mul_C,
      zero_add] at h1
    rw [LinearMap.comp_apply] at h1
    rw [map_sub, map_smul, smul_eq_mul, h1, sub_self]
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h1 := congrArg (fun P => Polynomial.coeff P (k + 1)) (key f)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul, hc, Polynomial.coeff_mul_C] at h1
    rw [LinearMap.comp_apply] at h1
    rw [map_sub, map_add, map_smul, smul_eq_mul, h1, sub_self]

/- English proof (translation)
Introduce `N _ _ Ω X d c p hX h`. Set `a : N → ℕ → N` to `fun w i => if i < d then c i w else 0`. Establish `ha : ∀ w i, d ≤ i → a w i = 0` using `fun w i hi => if_neg (by omega)`. Establish `hXa : ∀ (M : ℕ), d ≤ M → ∀ (u : ℂ) (w : N), X u w = ∑ i ∈ Finset.range M, u ^ i • a w i`. Introduce `M hM u w`.

Rewrite using `[hX u, LinearMap.sum_apply]`. Rewrite using `[← Finset.sum_subset (Finset.range_subset_range.2 hM)]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `only [a, if_pos (Finset.mem_range.1 hi), LinearMap.smul_apply]`. Introduce `i _ hi`.

Rewrite using `[ha w i (by simpa using hi), smul_zero]`. Establish `hco : ∀ w, Ω (a w 0) = p.coeff 0 • w ∧ ∀ k, a w k + Ω (a w (k + 1)) = p.coeff (k + 1) • w`. Introduce `w`. Use `shift_coeff_of_eval_identity Ω d (a w) (ha w) p w fun u => ?_` and prove the remaining obligations. Rewrite using `[← hXa d le_rfl u w]`.

Conclude with `h u w`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Establish `tel : ∀ n, ∑ i ∈ Finset.range (n + 1), p.coeff i • ((-Ω) ^ i) w = ((-Ω) ^ n) (Ω (a w n))`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp [(hco w).1]`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ, ih, ← map_smul, ← (hco w).2 n, map_add, ← add_assoc]`. Establish `: ((-Ω) ^ (n + 1)) (a w n) = - ((-Ω) ^ n) (Ω (a w n))`.

Rewrite using `[pow_succ, Module.End.mul_apply, LinearMap.neg_apply, map_neg]`. Rewrite using `[this, add_neg_cancel, zero_add]`. Rewrite using `[Polynomial.aeval_eq_sum_range' (n := d + p.natDegree + 1) (by omega), LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply]`. Rewrite using `[tel, ha w _ (by omega), map_zero, map_zero, LinearMap.zero_apply]`.

Introduce `α w hw q hq u`. Establish `step : ∀ k, a w (k + 1) = q.coeff (k + 1) • w → a w k = q.coeff k • w`. Introduce `k hk`. Establish `h1` using `(hco w).2 k`. Rewrite `h1` using `[hk, map_smul, hw, hq, add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, add_smul, smul_smul, mul_comm]`.

Conclude with `add_right_cancel h1`. Establish `all : ∀ k, a w k = q.coeff k • w`. Introduce `k`. Establish `hk : k ≤ k + d + q.natDegree + 1` using `by omega`. Use `Nat.decreasingInduction (motive := fun k _ => a w k = q.coeff k • w) (fun j _ hj => step j hj) ?_ hk` and prove the remaining obligations.

Rewrite using `[ha w _ (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]`. Rewrite using `[hXa (d + q.natDegree + 1) (by omega), Polynomial.eval_eq_sum_range' (n := d + q.natDegree + 1) (by omega), Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[all, smul_smul, mul_comm]`.
-/
theorem aeval_neg_eq_zero_and_eigen_of_resolvent_identity :
    ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (p : Polynomial ℂ), (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = p.eval u • w) → Polynomial.aeval (-Ω) p = 0 ∧ ∀ (α : ℂ) (w : N), Ω w = α • w → ∀ (q : Polynomial ℂ), p = (Polynomial.X + Polynomial.C α) * q → ∀ u : ℂ, X u w = q.eval u • w := by
  intro N _ _ Ω X d c p hX h
  let a : N → ℕ → N := fun w i => if i < d then c i w else 0
  have ha : ∀ w i, d ≤ i → a w i = 0 := fun w i hi => if_neg (by omega)
  have hXa : ∀ (M : ℕ), d ≤ M → ∀ (u : ℂ) (w : N),
      X u w = ∑ i ∈ Finset.range M, u ^ i • a w i := by
    intro M hM u w
    rw [hX u, LinearMap.sum_apply]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 hM)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp only [a, if_pos (Finset.mem_range.1 hi), LinearMap.smul_apply]
    · intro i _ hi
      rw [ha w i (by simpa using hi), smul_zero]
  have hco : ∀ w, Ω (a w 0) = p.coeff 0 • w ∧
      ∀ k, a w k + Ω (a w (k + 1)) = p.coeff (k + 1) • w := by
    intro w
    refine shift_coeff_of_eval_identity Ω d (a w) (ha w) p w fun u => ?_
    rw [← hXa d le_rfl u w]
    exact h u w
  refine ⟨?_, ?_⟩
  · ext w
    have tel : ∀ n, ∑ i ∈ Finset.range (n + 1), p.coeff i • ((-Ω) ^ i) w
        = ((-Ω) ^ n) (Ω (a w n)) := by
      intro n
      induction n with
      | zero => simp [(hco w).1]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, ← map_smul, ← (hco w).2 n, map_add, ← add_assoc]
        have : ((-Ω) ^ (n + 1)) (a w n) = - ((-Ω) ^ n) (Ω (a w n)) := by
          rw [pow_succ, Module.End.mul_apply, LinearMap.neg_apply, map_neg]
        rw [this, add_neg_cancel, zero_add]
    rw [Polynomial.aeval_eq_sum_range' (n := d + p.natDegree + 1) (by omega), LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [tel, ha w _ (by omega), map_zero, map_zero, LinearMap.zero_apply]
  · intro α w hw q hq u
    have step : ∀ k, a w (k + 1) = q.coeff (k + 1) • w → a w k = q.coeff k • w := by
      intro k hk
      have h1 := (hco w).2 k
      rw [hk, map_smul, hw, hq, add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_mul, add_smul, smul_smul, mul_comm] at h1
      exact add_right_cancel h1
    have all : ∀ k, a w k = q.coeff k • w := by
      intro k
      have hk : k ≤ k + d + q.natDegree + 1 := by omega
      refine Nat.decreasingInduction (motive := fun k _ => a w k = q.coeff k • w)
        (fun j _ hj => step j hj) ?_ hk
      rw [ha w _ (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]
    rw [hXa (d + q.natDegree + 1) (by omega), Polynomial.eval_eq_sum_range' (n := d + q.natDegree + 1) (by omega), Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [all, smul_smul, mul_comm]

end GlobalTheory

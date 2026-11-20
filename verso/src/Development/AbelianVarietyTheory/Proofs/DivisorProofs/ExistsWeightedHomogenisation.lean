import Mathlib

open MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Set `d : (Fin r →₀ ℕ) → ℕ` to `fun α => ∑ i, α i * wt i.succ`. Set `N : ℕ` to `P.support.sup d`. Set `e : (Fin r →₀ ℕ) → (Fin (r + 1) →₀ ℕ)` to `fun α => Finsupp.cons (N - d α) α`. Establish `he : Function.Injective e` using `fun a b h => by`. Use `congrArg Finsupp.tail h` as an intermediate fact.

Simplify `this` using `[e]`. Establish `hd : ∀ α ∈ P.support, d α ≤ N` using `fun α h => Finset.le_sup (f := d) h`. Use `⟨N, ∑ α ∈ P.support, monomial (e α) (P.coeff α), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `IsWeightedHomogeneous.sum _ _ _ fun α hα => ?_` and prove the remaining obligations. Use `isWeightedHomogeneous_monomial _ _ _ ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_succ]`. Use `hd α hα` as an intermediate fact. Simplify using `only [e, Finsupp.cons_zero, Finsupp.cons_succ, hwt, smul_eq_mul, mul_one]`. Express the relevant statement in the definitionally equal form `N - d α + d α = N`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[eval₂_eq', Finset.mul_sum, map_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Rewrite using `[eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]`. Establish `h1 : (z 0 : L) ^ N = (z 0 : L) ^ (N - d α) * (z 0 : L) ^ d α`.

Rewrite using `[← pow_add, Nat.sub_add_cancel (hd α hα)]`. Establish `h2 : (z 0 : L) ^ d α * ∏ i, ((z i.succ : L) / (z 0 : L) ^ wt i.succ) ^ α i = ∏ i, (z i.succ : L) ^ α i`. Simplify using `only [d]`. Rewrite using `[← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm (α i), pow_mul, ← mul_pow, mul_div_cancel₀ _ (pow_ne_zero _ hz)]`. Simplify using `only [e, Finsupp.cons_zero, Finsupp.cons_succ]`. Use `push_cast`. Rewrite using `[h1, ← h2, Subring.coe_subtype]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `α`. Use `⟨e α, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_monomial, he.eq_iff]`. Rewrite using `[Finset.sum_ite_eq']`.

Use `split_ifs with h`. Both sides reduce to the same expression. Conclude with `(notMem_support_iff.mp h).symm`.
-/
theorem exists_weightedHomogenisation {L : Type} [Field L] (Q : Subring L) (r : ℕ)
    (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ) (hwt : wt 0 = 1) (hz : (z 0 : L) ≠ 0)
    (P : MvPolynomial (Fin r) Q) :
    ∃ (N : ℕ) (F : MvPolynomial (Fin (r + 1)) Q), F.IsWeightedHomogeneous wt N ∧
      ((MvPolynomial.eval z F : Q) : L) = (z 0 : L) ^ N *
        MvPolynomial.eval₂ Q.subtype (fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ) P ∧
      ∀ α, ∃ β, F.coeff β = P.coeff α := by
  classical
  let d : (Fin r →₀ ℕ) → ℕ := fun α => ∑ i, α i * wt i.succ
  let N : ℕ := P.support.sup d
  let e : (Fin r →₀ ℕ) → (Fin (r + 1) →₀ ℕ) := fun α => Finsupp.cons (N - d α) α
  have he : Function.Injective e := fun a b h => by
    have := congrArg Finsupp.tail h
    simpa [e] using this
  have hd : ∀ α ∈ P.support, d α ≤ N := fun α h => Finset.le_sup (f := d) h
  refine ⟨N, ∑ α ∈ P.support, monomial (e α) (P.coeff α), ?_, ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun α hα => ?_
    refine isWeightedHomogeneous_monomial _ _ _ ?_
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_succ]
    have := hd α hα
    simp only [e, Finsupp.cons_zero, Finsupp.cons_succ, hwt, smul_eq_mul, mul_one]
    change N - d α + d α = N
    omega
  · rw [eval₂_eq', Finset.mul_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
    have h1 : (z 0 : L) ^ N = (z 0 : L) ^ (N - d α) * (z 0 : L) ^ d α := by
      rw [← pow_add, Nat.sub_add_cancel (hd α hα)]
    have h2 : (z 0 : L) ^ d α * ∏ i, ((z i.succ : L) / (z 0 : L) ^ wt i.succ) ^ α i
        = ∏ i, (z i.succ : L) ^ α i := by
      simp only [d]
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_comm (α i), pow_mul, ← mul_pow, mul_div_cancel₀ _ (pow_ne_zero _ hz)]
    simp only [e, Finsupp.cons_zero, Finsupp.cons_succ]
    push_cast
    rw [h1, ← h2, Subring.coe_subtype]
    ring
  · intro α
    refine ⟨e α, ?_⟩
    rw [coeff_sum]
    simp only [coeff_monomial, he.eq_iff]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (notMem_support_iff.mp h).symm

end GlobalTheory

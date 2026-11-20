import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Introduce `x hx`. Establish `hmem : ∀ q : G ⧸ N, q.out ∈ N ↔ q = ((1 : G) : G ⧸ N)`. Introduce `q`. Use `conv_rhs => rw [← QuotientGroup.out_eq' q]`. Rewrite using `[QuotientGroup.eq, mul_one, inv_mem_iff]`.

Establish `key : ∀ q : G ⧸ N, (∑ i, a i * q.out • b i) * q.out • x = if ((1 : G) : G ⧸ N) = q then c * x else 0`. Introduce `q`. Distinguish the cases in `hq : q.out ∈ N`. Rewrite using `[if_pos ((hmem q).mp hq).symm, h.sum_in _ hq]`. Use `congr 1`.

Conclude with `hx ⟨_, hq⟩`. Rewrite using `[if_neg (fun h1 => hq ((hmem q).mpr h1.symm)), h.sum_out _ hq, zero_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [cosetTrace, smul_mul', Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = c * x := by rw [Finset.sum_congr rfl fun q _ => key q]; simp`.
-/
theorem sum_mul_cosetTrace_eq (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] (N : Subgroup G) [Fintype (G ⧸ N)] (n : ℕ) (a b : Fin n → L) (c : L)
    (h : IsSep v N a b c) : ∀ x ∈ Fix L N, ∑ i, a i * cosetTrace N (b i * x) = c * x := by
  classical
  intro x hx
  have hmem : ∀ q : G ⧸ N, q.out ∈ N ↔ q = ((1 : G) : G ⧸ N) := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq, mul_one, inv_mem_iff]
  have key : ∀ q : G ⧸ N, (∑ i, a i * q.out • b i) * q.out • x
      = if ((1 : G) : G ⧸ N) = q then c * x else 0 := by
    intro q
    by_cases hq : q.out ∈ N
    · rw [if_pos ((hmem q).mp hq).symm, h.sum_in _ hq]
      congr 1
      exact hx ⟨_, hq⟩
    · rw [if_neg (fun h1 => hq ((hmem q).mpr h1.symm)), h.sum_out _ hq, zero_mul]
  calc ∑ i, a i * cosetTrace N (b i * x)
      = ∑ q : G ⧸ N, (∑ i, a i * q.out • b i) * q.out • x := by
        simp only [cosetTrace, smul_mul', Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = c * x := by rw [Finset.sum_congr rfl fun q _ => key q]; simp

end GlobalTheory.AlmostEt

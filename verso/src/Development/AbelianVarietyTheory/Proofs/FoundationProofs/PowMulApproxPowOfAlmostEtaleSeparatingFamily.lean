import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationFrobeniusSumSubLeNatCastPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedPropertiesStatement

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Introduce `L _ v p hp G _ _ hv N _ θ hθ hroot n a b c hs x hx hx1`. Establish `frob` using `GlobalTheory.T.valuation_frobenius_sum_sub_le_natCast_prime L v p hp`. Establish `trfix` using `GlobalTheory.T.cosetRepresentativeTrace_fixed_properties L v G hv N`. Establish `memN : ∀ y : L, y ∈ Fix L N ↔ ∀ g ∈ N, g • y = y`. Introduce `y`.

Prove the components needed by the constructor for the conclusion. Introduce `h g hg`. Conclude with `h ⟨g, hg⟩`. Introduce `h g`. Conclude with `h g g.2`.

Establish `memTop : ∀ y : L, y ∈ Fix L (⊤ : Subgroup G) ↔ ∀ g : G, g • y = y`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `h g`. Conclude with `h ⟨g, Subgroup.mem_top g⟩`.

Introduce `h g`. Conclude with `h g`. Use `set q₀ : G ⧸ N := ((1 : G) : G ⧸ N) with hq₀`. Establish `hout : ∀ q : G ⧸ N, q.out ∈ N ↔ q = q₀` using `fun q => by conv_rhs => rw [← QuotientGroup.out_eq' q]`. Rewrite using `[hq₀, QuotientGroup.eq, mul_one, inv_mem_iff]`.

Use `set T : Fin n → L := fun i => cosetTrace N (b i ^ p * x) with hTdef`. Establish `hbx : ∀ i, b i ^ p * x ∈ Fix L N` using `fun i => Subfield.mul_mem _ (Subfield.pow_mem _ (hs.b_mem i) p) hx`. Establish `hT : ∀ i, (∀ g : G, g • T i = T i) ∧ v (T i) ≤ 1` using `fun i => by`. Take `⟨h1, h2, -⟩` from `trfix _ (hbx i)`. Use `⟨h1, h2 ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow]`. Conclude with `mul_le_one' (pow_le_one' (hs.b_le i) p) hx1`. Use `choose w hwmem hwle using fun i => hroot (T i) ((memTop _).2 (hT i).1)`. Establish `hwθ : ∀ i, v (T i - w i ^ p) ≤ θ` using `fun i => le_trans (hwle i) (mul_le_of_le_one_right zero_le' (hT i).2)`. Establish `hw1 : ∀ i, v (w i) ≤ 1` using `fun i => by`.

Establish `: v (w i ^ p) ≤ 1`. Establish `e : w i ^ p = T i - (T i - w i ^ p)` using `by ring`. Rewrite using `[e]`. Conclude with `Valuation.map_sub_le v (hT i).2 (le_trans (hwθ i) hθ)`. Rewrite `this` using `[map_pow]`.

Conclude with `(pow_le_one_iff_of_nonneg zero_le' hp.ne_zero).1 this`. Use `set W : L := ∑ i, a i * w i with hWdef`. Establish `hWmem : W ∈ Fix L N`. Use `Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hs.a_mem i) ?_` and prove the remaining obligations. Conclude with `(memN _).2 fun g _ => (memTop _).1 (hwmem i) g`.

Use `⟨W, hWmem, ?_⟩` and prove the remaining obligations. Establish `key1 : ∑ i, a i ^ p * T i = ∑ q : G ⧸ N, (∑ i, (a i * q.out • b i) ^ p) * q.out • x`. Simplify using `only [hTdef, cosetTrace, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_mul', smul_pow', mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `key2 : c ^ p * x = ∑ q : G ⧸ N, (∑ i, a i * q.out • b i) ^ p * q.out • x`. Rewrite using `[Finset.sum_eq_single q₀]`. Rewrite using `[hs.sum_in _ ((hout q₀).2 rfl), (memN x).1 hx _ ((hout q₀).2 rfl)]`.

Introduce `q _ hq`. Rewrite using `[hs.sum_out _ (fun h => hq ((hout q).1 h)), zero_pow hp.ne_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `bound1 : v (c ^ p * x - ∑ i, a i ^ p * T i) ≤ v (p : L)`.

Rewrite using `[key1, key2, ← Finset.sum_sub_distrib]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `q _`. Rewrite using `[← sub_mul, map_mul]`. Establish `h1 : v (q.out • x) ≤ 1` using `by rw [hv]; exact hx1`.

Establish `h2` using `frob (Fin n) Finset.univ (fun i => a i * q.out • b i) (fun i _ => by rw [map_mul, hv]; exact mul_le_one' (hs.a_le i) (hs.b_le i))`. Combine the equalities or inequalities in the displayed calculation. Establish `bound2 : v (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) ≤ θ`. Rewrite using `[← Finset.sum_sub_distrib]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[← mul_sub, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `bound3 : v (∑ i, a i ^ p * w i ^ p - W ^ p) ≤ v (p : L)`. Establish `h` using `frob (Fin n) Finset.univ (fun i => a i * w i) (fun i _ => by rw [map_mul]; exact mul_le_one' (hs.a_le i) (hw1 i))`.

Simplify using `only [mul_pow] at h`. Rewrite using `[Valuation.map_sub_swap]`. Conclude with `h`. Establish `e : c ^ p * x - W ^ p = (c ^ p * x - ∑ i, a i ^ p * T i) + (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) + (∑ i, a i ^ p * w i ^ p - W ^ p)` using `by ring`. Rewrite using `[e]`.

Use `Valuation.map_add_le v (Valuation.map_add_le v ?_ ?_) ?_` and prove the remaining obligations. Conclude with `le_trans bound1 (le_max_right _ _)`. Conclude with `le_trans bound2 (le_max_left _ _)`. Conclude with `le_trans bound3 (le_max_right _ _)`.
-/
theorem cpow_mul_approx_pow_of_isSep :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)] (θ : ℝ≥0), θ ≤ 1 → (∀ u ∈ Fix L (⊤ : Subgroup G), ∃ w ∈ Fix L (⊤ : Subgroup G), v (u - w ^ p) ≤ θ * v u) → ∀ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, v x ≤ 1 → ∃ w ∈ Fix L N, v (c ^ p * x - w ^ p) ≤ max θ (v (p : L)) := by
  intro L _ v p hp G _ _ hv N _ θ hθ hroot n a b c hs x hx hx1
  have frob := GlobalTheory.T.valuation_frobenius_sum_sub_le_natCast_prime L v p hp
  have trfix := GlobalTheory.T.cosetRepresentativeTrace_fixed_properties L v G hv N
  have memN : ∀ y : L, y ∈ Fix L N ↔ ∀ g ∈ N, g • y = y := by
    intro y
    constructor
    · intro h g hg; exact h ⟨g, hg⟩
    · intro h g; exact h g g.2
  have memTop : ∀ y : L, y ∈ Fix L (⊤ : Subgroup G) ↔ ∀ g : G, g • y = y := by
    intro y
    constructor
    · intro h g; exact h ⟨g, Subgroup.mem_top g⟩
    · intro h g; exact h g
  set q₀ : G ⧸ N := ((1 : G) : G ⧸ N) with hq₀
  have hout : ∀ q : G ⧸ N, q.out ∈ N ↔ q = q₀ := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [hq₀, QuotientGroup.eq, mul_one, inv_mem_iff]
  set T : Fin n → L := fun i => cosetTrace N (b i ^ p * x) with hTdef
  have hbx : ∀ i, b i ^ p * x ∈ Fix L N := fun i =>
    Subfield.mul_mem _ (Subfield.pow_mem _ (hs.b_mem i) p) hx
  have hT : ∀ i, (∀ g : G, g • T i = T i) ∧ v (T i) ≤ 1 := fun i => by
    obtain ⟨h1, h2, -⟩ := trfix _ (hbx i)
    refine ⟨h1, h2 ?_⟩
    rw [map_mul, map_pow]
    exact mul_le_one' (pow_le_one' (hs.b_le i) p) hx1
  choose w hwmem hwle using fun i => hroot (T i) ((memTop _).2 (hT i).1)
  have hwθ : ∀ i, v (T i - w i ^ p) ≤ θ := fun i =>
    le_trans (hwle i) (mul_le_of_le_one_right zero_le' (hT i).2)
  have hw1 : ∀ i, v (w i) ≤ 1 := fun i => by
    have : v (w i ^ p) ≤ 1 := by
      have e : w i ^ p = T i - (T i - w i ^ p) := by ring
      rw [e]
      exact Valuation.map_sub_le v (hT i).2 (le_trans (hwθ i) hθ)
    rw [map_pow] at this
    exact (pow_le_one_iff_of_nonneg zero_le' hp.ne_zero).1 this
  set W : L := ∑ i, a i * w i with hWdef
  have hWmem : W ∈ Fix L N := by
    refine Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hs.a_mem i) ?_
    exact (memN _).2 fun g _ => (memTop _).1 (hwmem i) g
  refine ⟨W, hWmem, ?_⟩

  have key1 : ∑ i, a i ^ p * T i = ∑ q : G ⧸ N, (∑ i, (a i * q.out • b i) ^ p) * q.out • x := by
    simp only [hTdef, cosetTrace, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul', smul_pow', mul_pow]
    ring
  have key2 : c ^ p * x = ∑ q : G ⧸ N, (∑ i, a i * q.out • b i) ^ p * q.out • x := by
    rw [Finset.sum_eq_single q₀]
    · rw [hs.sum_in _ ((hout q₀).2 rfl), (memN x).1 hx _ ((hout q₀).2 rfl)]
    · intro q _ hq
      rw [hs.sum_out _ (fun h => hq ((hout q).1 h)), zero_pow hp.ne_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have bound1 : v (c ^ p * x - ∑ i, a i ^ p * T i) ≤ v (p : L) := by
    rw [key1, key2, ← Finset.sum_sub_distrib]
    apply Valuation.map_sum_le
    intro q _
    rw [← sub_mul, map_mul]
    have h1 : v (q.out • x) ≤ 1 := by rw [hv]; exact hx1
    have h2 := frob (Fin n) Finset.univ (fun i => a i * q.out • b i)
      (fun i _ => by rw [map_mul, hv]; exact mul_le_one' (hs.a_le i) (hs.b_le i))
    calc _ ≤ v (p : L) * 1 := mul_le_mul' h2 h1
      _ = _ := mul_one _
  have bound2 : v (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) ≤ θ := by
    rw [← Finset.sum_sub_distrib]
    apply Valuation.map_sum_le
    intro i _
    rw [← mul_sub, map_mul]
    calc _ ≤ 1 * θ := mul_le_mul' (by rw [map_pow]; exact pow_le_one' (hs.a_le i) p) (hwθ i)
      _ = θ := one_mul θ
  have bound3 : v (∑ i, a i ^ p * w i ^ p - W ^ p) ≤ v (p : L) := by
    have h := frob (Fin n) Finset.univ (fun i => a i * w i)
      (fun i _ => by rw [map_mul]; exact mul_le_one' (hs.a_le i) (hw1 i))
    simp only [mul_pow] at h
    rw [Valuation.map_sub_swap]
    exact h
  have e : c ^ p * x - W ^ p = (c ^ p * x - ∑ i, a i ^ p * T i)
      + (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) + (∑ i, a i ^ p * w i ^ p - W ^ p) := by ring
  rw [e]
  refine Valuation.map_add_le v (Valuation.map_add_le v ?_ ?_) ?_
  · exact le_trans bound1 (le_max_right _ _)
  · exact le_trans bound2 (le_max_left _ _)
  · exact le_trans bound3 (le_max_right _ _)

end GlobalTheory.AlmostEt

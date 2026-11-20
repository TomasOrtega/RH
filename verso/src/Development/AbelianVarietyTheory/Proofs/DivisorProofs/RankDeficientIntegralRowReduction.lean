import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

/- English proof (translation)
Establish `hdep : ¬ LinearIndependent k X.row`. Introduce `h`. Rewrite `h` using `[linearIndependent_iff_card_eq_finrank_span]`. Rewrite `hX` using `[rank_eq_finrank_span_row]`. Conclude with `(lt_irrefl _) (h ▸ hX)`.

Take `⟨c, hc, i₁, hi₁⟩` from `Fintype.not_linearIndependent_iff.1 hdep`. Establish `hcj : ∀ j, ∑ i, c i * X i j = 0`. Introduce `j`. Use `congrFun hc j` as an intermediate fact. Simplify `this` using `[Finset.sum_apply, Matrix.row]`.

Take `⟨i₀, -, hmax⟩` from `Finset.exists_max_image Finset.univ (fun i => valuation k (c i)) ⟨i₁, Finset.mem_univ _⟩`. Establish `hc0 : c i₀ ≠ 0`. Introduce `h0`. Use `hmax i₁ (Finset.mem_univ _)` as an intermediate fact. Rewrite `this` using `[h0, map_zero, le_zero_iff, Valuation.zero_iff]`.

Conclude with `hi₁ this`. Use `set c' : A → k := fun i => c i / c i₀ with hc'`. Establish `hc'int : ∀ i, c' i ∈ 𝒪[k]`. Introduce `i`. Rewrite using `[Valuation.mem_integer_iff, hc', map_div₀]`.

Establish `hpos : 0 < valuation k (c i₀)`. Rewrite using `[zero_lt_iff]`. Conclude with `(Valuation.ne_zero_iff _).2 hc0`. Conclude with `(div_le_one₀ hpos).2 (hmax i (Finset.mem_univ _))`. Establish `hc'0 : c' i₀ = 1` using `div_self hc0`.

Set `E : Matrix A A k` to `Matrix.of fun i j => if i = i₀ ∧ j ≠ i₀ then c' j else 0`. Establish `hEE : E * E = 0`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, E, Matrix.of_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hl : l = i₀`. Simplify using `[hl]`. Simplify using `[hl]`. Establish `hEint : ∀ i j, E i j ∈ 𝒪[k]`. Introduce `i j`.

Simplify using `only [E, Matrix.of_apply]`. Use `split_ifs`. Conclude with `hc'int j`. Conclude with `zero_mem _`. Establish `h1int : ∀ i j, (1 : Matrix A A k) i j ∈ 𝒪[k]`.

Introduce `i j`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Set `g : GL A k` to `⟨1 + E, 1 - E, by rw [add_mul, one_mul, mul_sub, mul_one, hEE]; abel, by rw [sub_mul, one_mul, mul_add, mul_one, hEE]; abel⟩`. Use `⟨g, ?_, i₀, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.SplitFlip.mem_KO_iff]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Use `show (1 + E) i j ∈ 𝒪[k]`.

Conclude with `add_mem (h1int i j) (hEint i j)`. Use `show (1 - E) i j ∈ 𝒪[k]`. Conclude with `sub_mem (h1int i j) (hEint i j)`. Use `show (((1 : Matrix A A k) + E) * X) i₀ j = 0`. Establish `hrow : ∀ l, (1 + E) i₀ l = c' l`.

Introduce `l`. Distinguish the cases in `hl : l = i₀`. Substitute `hl` using the available equality. Simplify using `[E, hc'0]`. Simplify using `[E, hl, Matrix.one_apply, Ne.symm hl]`.

Rewrite using `[Matrix.mul_apply]`. Repeatedly rewrite using `[hrow, hc', div_mul_eq_mul_div, ← Finset.sum_div, hcj j, zero_div]`.
-/
theorem exists_KO_row_zero_of_rank_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (X : Matrix A D k) (hX : X.rank < Fintype.card A) :
    ∃ g ∈ GlobalTheory.SplitWeil.KO k A, ∃ i₀ : A, ∀ j, (g.val * X) i₀ j = 0 := by

  have hdep : ¬ LinearIndependent k X.row := by
    intro h
    rw [linearIndependent_iff_card_eq_finrank_span] at h
    rw [rank_eq_finrank_span_row] at hX
    exact (lt_irrefl _) (h ▸ hX)
  obtain ⟨c, hc, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hcj : ∀ j, ∑ i, c i * X i j = 0 := by
    intro j
    have := congrFun hc j
    simpa [Finset.sum_apply, Matrix.row] using this

  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (c i))
    ⟨i₁, Finset.mem_univ _⟩
  have hc0 : c i₀ ≠ 0 := by
    intro h0
    have := hmax i₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hi₁ this
  set c' : A → k := fun i => c i / c i₀ with hc'
  have hc'int : ∀ i, c' i ∈ 𝒪[k] := by
    intro i
    rw [Valuation.mem_integer_iff, hc', map_div₀]
    have hpos : 0 < valuation k (c i₀) := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hc0
    exact (div_le_one₀ hpos).2 (hmax i (Finset.mem_univ _))
  have hc'0 : c' i₀ = 1 := div_self hc0

  let E : Matrix A A k := Matrix.of fun i j => if i = i₀ ∧ j ≠ i₀ then c' j else 0
  have hEE : E * E = 0 := by
    ext i j
    simp only [Matrix.mul_apply, E, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = i₀
    · simp [hl]
    · simp [hl]
  have hEint : ∀ i j, E i j ∈ 𝒪[k] := by
    intro i j
    simp only [E, Matrix.of_apply]
    split_ifs
    · exact hc'int j
    · exact zero_mem _
  have h1int : ∀ i j, (1 : Matrix A A k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  let g : GL A k := ⟨1 + E, 1 - E, by rw [add_mul, one_mul, mul_sub, mul_one, hEE]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, hEE]; abel⟩
  refine ⟨g, ?_, i₀, fun j => ?_⟩
  · rw [GlobalTheory.SplitFlip.mem_KO_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      exact add_mem (h1int i j) (hEint i j)
    · show (1 - E) i j ∈ 𝒪[k]
      exact sub_mem (h1int i j) (hEint i j)
  · show (((1 : Matrix A A k) + E) * X) i₀ j = 0
    have hrow : ∀ l, (1 + E) i₀ l = c' l := by
      intro l
      by_cases hl : l = i₀
      · subst hl; simp [E, hc'0]
      · simp [E, hl, Matrix.one_apply, Ne.symm hl]
    rw [Matrix.mul_apply]
    simp_rw [hrow, hc', div_mul_eq_mul_div, ← Finset.sum_div, hcj j, zero_div]

end GlobalTheory.RankCoinv

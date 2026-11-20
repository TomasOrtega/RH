import Mathlib

namespace GroundTheory.Variant₂.N1

/- English proof (translation)
Use `set S : Submodule ℚ_[p] (PadicAlgCl p) := Subalgebra.toSubmodule (Algebra.adjoin ℚ_[p] {c}) with hS`. Establish `hint : IsIntegral ℚ_[p] c` using `Algebra.IsIntegral.isIntegral c`. Establish `: FiniteDimensional ℚ_[p] S` using `Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton`. Establish `: ProperSpace S` using `FiniteDimensional.proper ℚ_[p] S`. Establish `hmem : ∀ n : ℕ, c ^ n ∈ S` using `fun n => Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℚ_[p] c) n`.

Set `x : ℕ → S` to `fun k => ⟨c ^ f k, hmem _⟩`. Establish `hx : ∀ k, x k ∈ Metric.closedBall (0 : S) 1`. Introduce `k`. Rewrite using `[mem_closedBall_zero_iff]`. Express the relevant statement in the definitionally equal form `‖c ^ f k‖ ≤ 1`.

Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) hc`. Take `⟨a, -, φ, hφ, hlim⟩` from `(isCompact_closedBall (0 : S) 1).tendsto_subseq hx`. Take `⟨N, hN⟩` from `Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)`. Use `⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩` and prove the remaining obligations.

Establish `h1 : dist (x (φ (N + 1))) a < ε / 2` using `hN (N + 1) (Nat.le_succ N)`. Establish `h2 : dist (x (φ N)) a < ε / 2` using `hN N le_rfl`. Establish `h3 : dist (x (φ (N + 1))) (x (φ N)) < ε`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h3` using `[dist_eq_norm]`.

Conclude with `h3`.
-/
theorem exists_lt_norm_pow_sub_pow_lt {p : ℕ} [hp : Fact (Nat.Prime p)] {c : PadicAlgCl p}
    (hc : ‖c‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) (f : ℕ → ℕ) :
    ∃ (k₀ : ℕ) (k₁ : ℕ), k₀ < k₁ ∧ ‖c ^ f k₁ - c ^ f k₀‖ < ε := by
  set S : Submodule ℚ_[p] (PadicAlgCl p) :=
    Subalgebra.toSubmodule (Algebra.adjoin ℚ_[p] {c}) with hS
  have hint : IsIntegral ℚ_[p] c := Algebra.IsIntegral.isIntegral c
  have : FiniteDimensional ℚ_[p] S := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  have : ProperSpace S := FiniteDimensional.proper ℚ_[p] S
  have hmem : ∀ n : ℕ, c ^ n ∈ S := fun n =>
    Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℚ_[p] c) n
  let x : ℕ → S := fun k => ⟨c ^ f k, hmem _⟩
  have hx : ∀ k, x k ∈ Metric.closedBall (0 : S) 1 := by
    intro k
    rw [mem_closedBall_zero_iff]
    change ‖c ^ f k‖ ≤ 1
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hc
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : S) 1).tendsto_subseq hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  have h1 : dist (x (φ (N + 1))) a < ε / 2 := hN (N + 1) (Nat.le_succ N)
  have h2 : dist (x (φ N)) a < ε / 2 := hN N le_rfl
  have h3 : dist (x (φ (N + 1))) (x (φ N)) < ε :=
    calc dist (x (φ (N + 1))) (x (φ N)) ≤ dist (x (φ (N + 1))) a + dist (x (φ N)) a :=
          dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := add_halves ε
  rw [dist_eq_norm] at h3
  exact h3

end GroundTheory.Variant₂.N1

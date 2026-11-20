import Mathlib

open Matrix Polynomial

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Establish `ha` using `hs a (Multiset.mem_cons_self a s)`. Take `⟨h1, h2⟩` from `ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))`.

Establish `hlo : (1 / 2 : ℝ) ≤ ‖a‖`. Use `norm_sub_norm_le (1 : ℂ) (1 - a)` as an intermediate fact. Rewrite `this` using `[norm_one, sub_sub_cancel, norm_sub_rev]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hhi : ‖a‖ ≤ 3 / 2`.

Use `norm_add_le (a - 1) 1` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ, pow_succ]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[mul_comm ((1 / 2 : ℝ) ^ _)]`. Conclude with `mul_le_mul hlo h1 (by positivity) (norm_nonneg _)`. Rewrite using `[mul_comm ((3 / 2 : ℝ) ^ _)]`. Conclude with `mul_le_mul hhi h2 (norm_nonneg _) (by norm_num)`.
-/
theorem norm_multiset_prod_near_one (s : Multiset ℂ) (hs : ∀ μ ∈ s, ‖μ - 1‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ Multiset.card s ≤ ‖s.prod‖ ∧ ‖s.prod‖ ≤ (3 / 2 : ℝ) ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    obtain ⟨h1, h2⟩ := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
    have hlo : (1 / 2 : ℝ) ≤ ‖a‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - a)
      rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
      linarith
    have hhi : ‖a‖ ≤ 3 / 2 := by
      have := norm_add_le (a - 1) 1
      rw [sub_add_cancel, norm_one] at this
      linarith
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ, pow_succ]
    constructor
    · rw [mul_comm ((1 / 2 : ℝ) ^ _)]
      exact mul_le_mul hlo h1 (by positivity) (norm_nonneg _)
    · rw [mul_comm ((3 / 2 : ℝ) ^ _)]
      exact mul_le_mul hhi h2 (norm_nonneg _) (by norm_num)

/- English proof (translation)
Establish `hroot : ∀ μ ∈ A.charpoly.roots, ‖μ - 1‖ ≤ 1 / 2`. Introduce `μ hμ`. Establish `hr : A.charpoly.IsRoot μ` using `isRoot_of_mem_roots hμ`. Establish `hev : Module.End.HasEigenvalue (Matrix.toLin' A) μ`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']`.

Conclude with `hr`. Take `⟨k, hk⟩` from `eigenvalue_mem_ball hev`. Rewrite `hk` using `[Metric.mem_closedBall, dist_eq_norm]`. Establish `hdiag : ‖A k k - 1‖ ≤ ε` using `by simpa using hA k k`. Establish `h1n : 1 ≤ n` using `Fin.pos k`.

Establish `hoff : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ((n : ℝ) - 1) * ε`. Establish `hle : ∀ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ε`. Introduce `j hj`. Establish `hjk : k ≠ j` using `(Finset.ne_of_mem_erase hj).symm`. Simplify `hA k j` using `[Matrix.one_apply_ne hjk]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub h1n, Nat.cast_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcard : Multiset.card A.charpoly.roots = n`. Rewrite using `[(splits_iff_card_roots).mp (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`.

Take `⟨h1, h2⟩` from `norm_multiset_prod_near_one _ hroot`. Rewrite `h1`, `h2` using `[hcard, ← Matrix.det_eq_prod_roots_charpoly]`. Use `⟨h1, h2.trans ?_⟩` and prove the remaining obligations. Conclude with `pow_le_pow_left₀ (by norm_num) (by norm_num) n`.
-/
theorem det_near_one_bounds (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ε) (hn : (n : ℝ) * ε ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ n ≤ ‖A.det‖ ∧ ‖A.det‖ ≤ 2 ^ n := by
  have hroot : ∀ μ ∈ A.charpoly.roots, ‖μ - 1‖ ≤ 1 / 2 := by
    intro μ hμ
    have hr : A.charpoly.IsRoot μ := isRoot_of_mem_roots hμ
    have hev : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']; exact hr
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
    rw [Metric.mem_closedBall, dist_eq_norm] at hk
    have hdiag : ‖A k k - 1‖ ≤ ε := by simpa using hA k k
    have h1n : 1 ≤ n := Fin.pos k
    have hoff : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ((n : ℝ) - 1) * ε := by
      have hle : ∀ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ε := by
        intro j hj
        have hjk : k ≠ j := (Finset.ne_of_mem_erase hj).symm
        simpa [Matrix.one_apply_ne hjk] using hA k j
      calc _ ≤ ∑ _j ∈ Finset.univ.erase k, ε := Finset.sum_le_sum hle
        _ = ((n : ℝ) - 1) * ε := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub h1n, Nat.cast_one]
    calc ‖μ - 1‖ = ‖(μ - A k k) + (A k k - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖μ - A k k‖ + ‖A k k - 1‖ := norm_add_le _ _
      _ ≤ ((n : ℝ) - 1) * ε + ε := add_le_add (hk.trans hoff) hdiag
      _ = n * ε := by ring
      _ ≤ 1 / 2 := hn
  have hcard : Multiset.card A.charpoly.roots = n := by
    rw [(splits_iff_card_roots).mp (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  obtain ⟨h1, h2⟩ := norm_multiset_prod_near_one _ hroot
  rw [hcard, ← Matrix.det_eq_prod_roots_charpoly] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

end GlobalTheory

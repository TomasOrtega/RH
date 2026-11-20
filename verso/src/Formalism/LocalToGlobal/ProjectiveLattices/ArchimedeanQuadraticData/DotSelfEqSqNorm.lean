import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open Matrix

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem dot_self_eq_sq_norm {N : ℕ} (v : Fin N → ℝ) :
    v ⬝ᵥ v = ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [dotProduct, sq]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cover_round {N : ℕ} (b : Fin N → Fin N → ℝ) (hb : LinearIndependent ℝ b) (ℓ : ℝ)
    (hℓ : ∀ j, b j ⬝ᵥ b j ≤ ℓ ^ 2) (w : Fin N → ℝ) :
    ∃ n : Fin N → ℤ, (w - ∑ j, (n j : ℝ) • b j) ⬝ᵥ (w - ∑ j, (n j : ℝ) • b j) ≤ ((N : ℝ) * ℓ / 2) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, by simp [dotProduct]⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hcard : Fintype.card (Fin N) = Module.finrank ℝ (Fin N → ℝ) := by simp
  let B := basisOfLinearIndependentOfCardEqFinrank hb hcard
  have hB : ∀ j, B j = b j := fun j => by simp [B]
  set c := B.repr w with hcdef
  refine ⟨fun j => round (c j), ?_⟩
  have hw : w = ∑ j, c j • b j := by
    conv_lhs => rw [← B.sum_repr w]
    simp only [hB, hcdef]

  have hdiff : w - ∑ j, ((round (c j) : ℤ) : ℝ) • b j = ∑ j, (c j - round (c j)) • b j := by
    conv_lhs => rw [hw]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sub_smul]
  have hbj : ∀ j, ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (b j)‖ ≤ |ℓ| := by
    intro j
    have h := hℓ j
    rw [dot_self_eq_sq_norm, ← sq_abs ℓ] at h
    by_contra hc
    push_neg at hc
    nlinarith [abs_nonneg ℓ]
  have hnorm : ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (∑ j, (c j - round (c j)) • b j)‖ ≤
      (N : ℝ) * |ℓ| / 2 := by
    rw [map_sum]
    calc ‖∑ j, (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm ((c j - round (c j)) • b j)‖
        ≤ ∑ j, ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm ((c j - round (c j)) • b j)‖ :=
          norm_sum_le _ _
      _ = ∑ j, |c j - round (c j)| * ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (b j)‖ := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [LinearEquiv.map_smul, norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ _j : Fin N, (1 / 2) * |ℓ| :=
          Finset.sum_le_sum (fun j _ =>
            mul_le_mul (abs_sub_round _) (hbj j) (norm_nonneg _) (by norm_num))
      _ = (N : ℝ) * |ℓ| / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hdiff, dot_self_eq_sq_norm]
  calc ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (∑ j, (c j - round (c j)) • b j)‖ ^ 2
      ≤ ((N : ℝ) * |ℓ| / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = ((N : ℝ) * ℓ / 2) ^ 2 := by
      rw [div_pow, mul_pow, sq_abs, ← mul_pow, ← div_pow]

end Formalism.L2.Pj.FundamentalDomainD5

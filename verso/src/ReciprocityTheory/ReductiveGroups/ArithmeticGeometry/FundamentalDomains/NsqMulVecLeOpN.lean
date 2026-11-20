import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

def nsq {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ j, ‖v j‖ ^ 2

/- English proof (translation)
Replace the relevant objects with their definitions. Check the signs of the components of the expression.
-/
lemma nsq_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ nsq v := by
  unfold nsq
  positivity

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
lemma nsq_mulVec_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (A.mulVec v) ≤ (∑ i, ∑ j, ‖A i j‖ ^ 2) * nsq v := by
  unfold nsq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h1 : ‖A.mulVec v i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => norm_mul _ _
  calc ‖A.mulVec v i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
lemma opN_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    BddAbove {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
      t = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
  refine ⟨Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2), ?_⟩
  rintro t ⟨v, -, rfl⟩
  have hF : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by positivity
  have key := nsq_mulVec_le A v
  have hb : 0 ≤ nsq v := nsq_nonneg v
  unfold nsq at key hb
  rcases hb.eq_or_lt with h | h
  · rw [← h]
    simp
  · rw [div_le_iff₀ (Real.sqrt_pos.2 h), ← Real.sqrt_mul hF]
    exact Real.sqrt_le_sqrt key

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Check the signs of the components of the expression.
-/
lemma opN_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ Data.opN A := by
  unfold Data.opN
  apply Real.sSup_nonneg
  rintro t ⟨v, -, rfl⟩
  positivity

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
lemma nsq_mulVec_le_opN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (A.mulVec v) ≤ Data.opN A ^ 2 * nsq v := by
  by_cases hv : v = 0
  · subst hv
    simp [nsq, Matrix.mulVec_zero]
  have hmem : Real.sqrt (nsq (A.mulVec v)) / Real.sqrt (nsq v) ≤ Data.opN A :=
    le_csSup (opN_bdd A) ⟨v, hv, rfl⟩
  have hpos : 0 < nsq v := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    unfold nsq
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hj) 2)
      (Finset.single_le_sum (fun k _ => sq_nonneg ‖v k‖) (Finset.mem_univ j))
  rw [div_le_iff₀ (Real.sqrt_pos.2 hpos)] at hmem
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hmem 2
  rwa [mul_pow, Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt hpos.le] at h2

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
lemma opN_le_zN {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (Z : X.Coord) (τ : X.Ψ) : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z := by
  unfold Data.zN
  exact le_ciSup (f := fun τ : X.Ψ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

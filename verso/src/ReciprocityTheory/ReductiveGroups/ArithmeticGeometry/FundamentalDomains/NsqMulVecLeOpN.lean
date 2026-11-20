import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

def nsq {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ j, ‖v j‖ ^ 2

/- English proof (translation)
Unfold `nsq`. Check the signs of the components of the expression.
-/
lemma nsq_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ nsq v := by
  unfold nsq
  positivity

/- English proof (translation)
Unfold `nsq`. Rewrite using `[Finset.sum_mul]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Establish `h1 : ‖A.mulVec v i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun j _ => norm_mul _ _`. Combine the equalities or inequalities in the displayed calculation.
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
Use `⟨Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2), ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨v, -, rfl⟩`. Establish `hF : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2` using `by positivity`. Establish `key` using `nsq_mulVec_le A v`. Establish `hb : 0 ≤ nsq v` using `nsq_nonneg v`.

Unfold `nsq at key hb`. Break down `hb.eq_or_lt with h | h` into its components or cases. Rewrite using `[← h]`. Simplify using the standard rewrite rules. Rewrite using `[div_le_iff₀ (Real.sqrt_pos.2 h), ← Real.sqrt_mul hF]`.

Conclude with `Real.sqrt_le_sqrt key`.
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
Unfold `Data.opN`. Apply `Real.sSup_nonneg` to reduce the goal to its premises. Introduce and unpack `t ⟨v, -, rfl⟩`. Check the signs of the components of the expression.
-/
lemma opN_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ Data.opN A := by
  unfold Data.opN
  apply Real.sSup_nonneg
  rintro t ⟨v, -, rfl⟩
  positivity

/- English proof (translation)
Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Simplify using `[nsq, Matrix.mulVec_zero]`. Establish `hmem : Real.sqrt (nsq (A.mulVec v)) / Real.sqrt (nsq v) ≤ Data.opN A` using `le_csSup (opN_bdd A) ⟨v, hv, rfl⟩`. Establish `hpos : 0 < nsq v`.

Take `⟨j, hj⟩` from `Function.ne_iff.1 hv`. Unfold `nsq`. Conclude with `lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hj) 2) (Finset.single_le_sum (fun k _ => sq_nonneg ‖v k‖) (Finset.mem_univ j))`. Rewrite `hmem` using `[div_le_iff₀ (Real.sqrt_pos.2 hpos)]`. Establish `h2` using `pow_le_pow_left₀ (Real.sqrt_nonneg _) hmem 2`.

Rewrite `h2` using `[mul_pow, Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt hpos.le]`. Then use the resulting hypothesis.
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
Unfold `Data.zN`. Conclude with `le_ciSup (f := fun τ : X.Ψ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ`.
-/
lemma opN_le_zN {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (Z : X.Coord) (τ : X.Ψ) : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z := by
  unfold Data.zN
  exact le_ciSup (f := fun τ : X.Ψ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

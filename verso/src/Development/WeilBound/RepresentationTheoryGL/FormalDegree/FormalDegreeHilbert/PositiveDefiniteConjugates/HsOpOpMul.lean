import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumNormAdjointSqEqHsOp

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_toMK (PolarDecomposition.polar_k_mem hg)`. Use `⟨u, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, pP, Matrix.mul_assoc, PolarDecomposition.polar_exp_neg_mul, Matrix.mul_one]`.
-/
theorem polar_pP {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ k : KG ε, g = toMK k * pP g := by
  obtain ⟨u, hu⟩ := exists_toMK (PolarDecomposition.polar_k_mem hg)
  refine ⟨u, ?_⟩
  rw [hu, pP, Matrix.mul_assoc, PolarDecomposition.polar_exp_neg_mul, Matrix.mul_one]

/- English proof (translation)
Unfold `hsOp`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.mul_apply, KType_norm_op_apply]`.
-/
theorem hsOp_op_mul {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    hsOp (T.op k * A) = hsOp A := by
  unfold hsOp
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.mul_apply, KType_norm_op_apply]

/- English proof (translation)
Introduce `n ε g hg`. Use `⟨⟨PolarDecomposition.polar_L g, PolarDecomposition.polar_L_inP hg, rfl⟩, fun Λ T μ => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `polar_pP hg`. Establish `hL` using `PolarDecomposition.polar_L_inP hg`. Establish `hex : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧ g = toMK k' * NormedSpace.exp X'` using `⟨k, PolarDecomposition.polar_L g, hL, hk⟩`.

Unfold `PsiM`. Rewrite using `[dif_pos hex]`. Take `⟨hP, hEq⟩` from `hex.choose_spec.choose_spec`. Establish `hEq' : toMK k * NormedSpace.exp (PolarDecomposition.polar_L g) = toMK hex.choose * NormedSpace.exp hex.choose_spec.choose` using `hk.symm.trans hEq`. Take `⟨-, h2⟩` from `polar_unique hL hP hEq'`.

Rewrite using `[hsOp_op_mul, ← h2]`. Both sides reduce to the same expression.
-/
theorem hsPol : HsPol := by
  intro n ε g hg
  refine ⟨⟨PolarDecomposition.polar_L g, PolarDecomposition.polar_L_inP hg, rfl⟩, fun Λ T μ => ?_⟩
  obtain ⟨k, hk⟩ := polar_pP hg
  have hL := PolarDecomposition.polar_L_inP hg
  have hex : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧ g = toMK k' * NormedSpace.exp X' :=
    ⟨k, PolarDecomposition.polar_L g, hL, hk⟩
  unfold PsiM
  rw [dif_pos hex]
  obtain ⟨hP, hEq⟩ := hex.choose_spec.choose_spec
  have hEq' : toMK k * NormedSpace.exp (PolarDecomposition.polar_L g) = toMK hex.choose * NormedSpace.exp hex.choose_spec.choose :=
    hk.symm.trans hEq
  obtain ⟨-, h2⟩ := polar_unique hL hP hEq'
  rw [hsOp_op_mul, ← h2]
  rfl

end PositivityTheory.RgFd

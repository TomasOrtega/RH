import Formalism.PeriodIntegrals.AmpRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.NegOnePowMulSelf

open Matrix

noncomputable section

namespace PI.AmpRelAtPt

open Formalism.QuantumDeterminants Formalism.MainNotions.S

/- English proof (translation)
Unfold `ell`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Unfold `flagMat fvec`. Rewrite using `[dif_pos (show (Fin.castSucc a).val < r by simp)]`. Distinguish the cases in `h : a.val + 1 < r`.

Rewrite using `[dif_pos h, dif_pos (show (Fin.succ a).val < r by simpa using h), bvec, Matrix.mulVec_single_one, Matrix.col_apply]`. Both sides reduce to the same expression. Rewrite using `[dif_neg h, dif_neg (show ¬ (Fin.succ a).val < r by simpa using h)]`. Both sides reduce to the same expression.
-/
theorem ell_eq {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z g = ∑ a : Fin r, flagMat k r z g a.castSucc a.succ := by
  unfold ell
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold flagMat fvec
  rw [dif_pos (show (Fin.castSucc a).val < r by simp)]
  by_cases h : a.val + 1 < r
  · rw [dif_pos h, dif_pos (show (Fin.succ a).val < r by simpa using h), bvec, Matrix.mulVec_single_one,
      Matrix.col_apply]
    rfl
  · rw [dif_neg h, dif_neg (show ¬ (Fin.succ a).val < r by simpa using h)]
    rfl

end PI.AmpRelAtPt

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon PI.AmpRelAtPt in
/- English proof (translation)
Introduce `k r L p g₀ hc hP hG a ha`. Establish `key` using `sum_super (ptσ_invol p) (zhat_pt hP.2) (ptζ_ne p) (pt_adj p) (flagMat_upper ha.1) (flagMat_diag ha.1) (flagMat_upper ha.2) (flagMat_diag ha.2) (flag_rel L.hz.1 L.hz'.1 hP.1 ha)`. Establish `hre : ∀ X : ℂ, (L.c * star X).re = (L.c * X).re`. Introduce `X`. Combine the equalities or inequalities in the displayed calculation.

Unfold `psi`. Rewrite using `[ell_eq L.z a, ell_eq L.z' (g₀⁻¹ * a * g₀), key, hre]`.
-/
theorem amplifier_relation_at_point : PI.AmpRoot.RelAtPt := by
  intro k r L p g₀ hc hP hG a ha
  have key := sum_super (ptσ_invol p) (zhat_pt hP.2) (ptζ_ne p) (pt_adj p)
    (flagMat_upper ha.1) (flagMat_diag ha.1) (flagMat_upper ha.2) (flagMat_diag ha.2)
    (flag_rel L.hz.1 L.hz'.1 hP.1 ha)
  have hre : ∀ X : ℂ, (L.c * star X).re = (L.c * X).re := by
    intro X
    calc (L.c * star X).re = (star L.c * star X).re := by rw [hc]
      _ = (star (L.c * X)).re := by rw [star_mul']
      _ = (L.c * X).re := by rw [Complex.star_def, Complex.conj_re]
  unfold psi
  rw [ell_eq L.z a, ell_eq L.z' (g₀⁻¹ * a * g₀), key, hre]

import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefDens
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorEqPointMinor

noncomputable section

open scoped Classical
open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Unfold `kind at h`. Unfold `cornerSh`. Apply the tactic sequence `by_cases h1 : Dmin w D.R.rS = 0 <;> by_cases h2 : Dmin w' D.R.rS = 0`. Simplify using `[h1, h2]`. Simplify using `[h1, h2] at h`.

Simplify using `[h1, h2] at h`. Simplify using `only [h1, h2, if_false] at h ⊢`. Rewrite using `[Option.some.inj h]`.
-/
theorem cornerSh_of_kind (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D)
    {w w' : Point D.host.E (D.R.rS + 1)} (h : kind w = kind w') : cornerSh δ T T' p w = cornerSh δ T T' p w' := by
  unfold kind at h
  unfold cornerSh
  by_cases h1 : Dmin w D.R.rS = 0 <;> by_cases h2 : Dmin w' D.R.rS = 0
  · simp [h1, h2]
  · simp [h1, h2] at h
  · simp [h1, h2] at h
  · simp only [h1, h2, if_false] at h ⊢
    rw [Option.some.inj h]

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem sgn_sq (q : ℕ) :
    (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/- English proof (translation)
Establish `h1` using `Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_cell (ZhatOM Z) w hZ q`. Rewrite `h1` using `[Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_ZhatOM Z q hq, Formalism.L2.SG.NGCut.NormalVectorPairings.leadingMinor_eq_pointMinor w q hq]`. Rewrite using `[h1, ← mul_assoc, sgn_sq, one_mul]`.
-/
theorem lead_at {w : Point D.host.E (D.R.rS + 1)} {Z : PairVal.MatR D} (hZ : AtMat w Z) (q : ℕ) (hq : q ≤ D.R.rS + 1) :
    leadMinorE Z q = (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * Dmin w q := by
  have h1 := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_cell (ZhatOM Z) w hZ q
  rw [Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_ZhatOM Z q hq, Formalism.L2.SG.NGCut.NormalVectorPairings.leadingMinor_eq_pointMinor w q hq] at h1
  rw [h1, ← mul_assoc, sgn_sq, one_mul]

/- English proof (translation)
Rewrite using `[lead_at hZ _ (Nat.le_succ _), lead_at hZ' _ le_rfl, lead_at hZ' _ (Nat.le_succ _), lead_at hZ _ le_rfl]`. Establish `key : Dmin w D.R.rS * Dmin w' (D.R.rS + 1) = Dmin w' D.R.rS * Dmin w (D.R.rS + 1)`. Unfold `kind at hk`. Apply the tactic sequence `by_cases h1 : Dmin w D.R.rS = 0 <;> by_cases h2 : Dmin w' D.R.rS = 0`. Rewrite using `[h1, h2]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[h1, h2] at hk`. Simplify using `[h1, h2] at hk`. Simplify using `only [h1, h2, if_false, Option.some.injEq] at hk`. Unfold `zetaOf at hk`.

Clear denominators, using `at hk` for the nonvanishing conditions. Take the linear combination `-hk`. Take the linear combination `(∏ b : Fin D.R.rS, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * (∏ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * key`.
-/
theorem cross_of_kind {w w' : Point D.host.E (D.R.rS + 1)} {Z Z' : PairVal.MatR D} (hk : kind w = kind w')
    (hZ : AtMat w Z) (hZ' : AtMat w' Z') :
    leadMinorE Z D.R.rS * leadMinorE Z' (D.R.rS + 1) = leadMinorE Z' D.R.rS * leadMinorE Z (D.R.rS + 1) := by
  rw [lead_at hZ _ (Nat.le_succ _), lead_at hZ' _ le_rfl, lead_at hZ' _ (Nat.le_succ _), lead_at hZ _ le_rfl]
  have key : Dmin w D.R.rS * Dmin w' (D.R.rS + 1) = Dmin w' D.R.rS * Dmin w (D.R.rS + 1) := by
    unfold kind at hk
    by_cases h1 : Dmin w D.R.rS = 0 <;> by_cases h2 : Dmin w' D.R.rS = 0
    · rw [h1, h2]; ring
    · simp [h1, h2] at hk
    · simp [h1, h2] at hk
    · simp only [h1, h2, if_false, Option.some.injEq] at hk
      unfold zetaOf at hk
      field_simp at hk
      linear_combination -hk
  linear_combination (∏ b : Fin D.R.rS, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) *
    (∏ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * key

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, smul_eq_mul]`. Simplify using `only [Fin.succAbove_last, Fin.val_last]`. Rewrite using `[show ((-1 : K) ^ (m + m)) = 1 by rw [← two_mul, pow_mul]; simp, one_mul, mul_comm, ← mul_assoc, Ring.mul_inverse_cancel _ hY, one_mul]`.
-/
theorem inv_last_mul_det {K : Type*} [CommRing K] {m : ℕ} (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hY : IsUnit Y.det) :
    Y⁻¹ (Fin.last m) (Fin.last m) * Y.det = (Y.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, smul_eq_mul]
  simp only [Fin.succAbove_last, Fin.val_last]
  rw [show ((-1 : K) ^ (m + m)) = 1 by rw [← two_mul, pow_mul]; simp, one_mul, mul_comm, ← mul_assoc,
    Ring.mul_inverse_cancel _ hY, one_mul]

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

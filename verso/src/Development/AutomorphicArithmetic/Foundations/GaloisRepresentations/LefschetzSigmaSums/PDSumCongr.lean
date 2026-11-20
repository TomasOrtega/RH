import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.dSumCongr_of :
    DSumCongr := by
  classical
  intro p _ G wt wt' s hw K f r K' φ
  unfold GlobalTheory.LKDef.dSumIrr
  rw [mul_comm _ s, ← smul_eq_mul s, smul_finsum]
  refine finsum_congr (fun q => ?_)
  split_ifs
  · rw [smul_eq_mul, hw]
    ring
  · simp

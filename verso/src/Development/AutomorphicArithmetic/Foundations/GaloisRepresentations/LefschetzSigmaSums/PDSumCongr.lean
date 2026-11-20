import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `p _ G wt wt' s hw K f r K' φ`. Unfold `GlobalTheory.LKDef.dSumIrr`. Rewrite using `[mul_comm _ s, ← smul_eq_mul s, smul_finsum]`. Use `finsum_congr (fun q => ?_)` and prove the remaining obligations. Use `split_ifs`.

Rewrite using `[smul_eq_mul, hw]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
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

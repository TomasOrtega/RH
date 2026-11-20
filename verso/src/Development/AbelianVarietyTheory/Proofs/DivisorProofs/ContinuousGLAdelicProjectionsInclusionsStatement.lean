import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusions
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousGLAdelicProjectionsInclusions.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.continuous_GL_adelic_projections_inclusions : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pInf E) g) ∧ Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) ∧ Continuous (infGL E a) ∧ Continuous (finGL E a) := by
  first | exact @GlobalTheory.GLProj.continuous_proj_incl | exact GlobalTheory.GLProj.continuous_proj_incl | (intros; apply GlobalTheory.GLProj.continuous_proj_incl <;> assumption)

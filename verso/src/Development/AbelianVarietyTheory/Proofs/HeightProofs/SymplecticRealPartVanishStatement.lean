import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanish
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FockCompare.sympl_parts` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FSymplecticRealPartVanish.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.symplectic_real_part_vanish : ∀ (D : D7) (V W : HSp D) (x y : WA V W), ((IsRealW V W x ∨ IsRealW V W y) → sndA D.host.F (sympl V W x y) = 0) ∧ ((x.map (infPart D) = 0 ∨ y.map (infPart D) = 0) → fstA D.host.F (sympl V W x y) = 0) := by
  first | exact @GlobalTheory.FockCompare.sympl_parts | exact GlobalTheory.FockCompare.sympl_parts | (intros; apply GlobalTheory.FockCompare.sympl_parts <;> assumption)

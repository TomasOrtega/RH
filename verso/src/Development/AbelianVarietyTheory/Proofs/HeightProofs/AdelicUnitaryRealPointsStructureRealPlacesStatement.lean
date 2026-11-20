import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FAdelicUnitaryRealPointsStructureRealPlaces.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces : ∀ D : D7, (∀ θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → IsInfFam θ' → θ = θ') ∧ ∀ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → ∀ V : HSp D, RealPoints θ V := by
  first | exact @GlobalTheory.SmoothForms.RealPts.realPoints | exact GlobalTheory.SmoothForms.RealPts.realPoints | (intros; apply GlobalTheory.SmoothForms.RealPts.realPoints <;> assumption)

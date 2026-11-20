import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibilityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OmpinsOnto

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.ompins_onto_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FOmpinsOnto.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.bar_tie_om_pins_phase_tie_of_pt_split : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → BarTie (fw2 p) ∧ (∀ i, OMPins p.T (R2 p) p.κ p.v₀ (om2 p) i) ∧ ∀ i, PhaseTie p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i := by
  first | exact @_root_.GlobalTheory.BigOn.ompins_onto_alt | exact _root_.GlobalTheory.BigOn.ompins_onto_alt | (intros; apply _root_.GlobalTheory.BigOn.ompins_onto_alt <;> assumption)
end

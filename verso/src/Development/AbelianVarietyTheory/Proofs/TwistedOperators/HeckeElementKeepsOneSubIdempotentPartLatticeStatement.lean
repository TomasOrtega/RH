import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeElementKeepsOneSubIdempotentPartLattice
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeOffParts.off_parts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHeckeElementKeepsOneSubIdempotentPartLattice.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.hecke_element_keeps_one_sub_idempotent_part_lattice : ∀ (D : D7) (V : HSp D) (e : AE D) (ϖ : D.host.E) (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.Theta.IsSplitIdem D e → Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀ →
    ∀ y ∈ latGHat V g, (1 - finPart D e) • y ∈ latGHat V (g * a₀) := by
  first | exact @GlobalTheory.HeckeOffParts.off_parts | exact GlobalTheory.HeckeOffParts.off_parts | (intros; apply GlobalTheory.HeckeOffParts.off_parts <;> assumption)

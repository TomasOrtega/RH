import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagUnipotentCoordinateMeasurableEquiv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Unf.flagCoord_measEquiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsFlagUnipotentCoordinateMeasurableEquiv.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.exists_flagUnipotent_coordinate_measurableEquiv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ∃ e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d, ∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1) := by
  first | exact @GlobalTheory.Unf.flagCoord_measEquiv | exact GlobalTheory.Unf.flagCoord_measEquiv | (intros; apply GlobalTheory.Unf.flagCoord_measEquiv <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHermitianLinkMapAdditiveRationalEquivariant.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.hermitianLinkMap_additive_rational_equivariant : ∀ (D : D7) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (ε : ℤ), τᴴ ⬝ (L.gram ⬝ τ) = ((ε : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ κ : WO S L' → WO L S, (∀ w, κ w = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) → (∀ w w', κ (w + w') = κ w + κ w') ∧ Continuous κ ∧ (∀ w ∈ ratMx D L'.rank S.rank, κ w ∈ ratMx D S.rank L.rank) ∧ (∀ (g : GA D S) (w : WO S L'), κ (w ⬝ mt S g⁻¹) = mt S g ⬝ κ w) ∧ (∀ w w', symplO L S (κ w) (κ w') = -((ε : AF D.host.F) * symplO S L' w w')) ∧ (∀ w, (w.map (infPart D) = 0 → (κ w).map (infPart D) = 0) ∧ (w.map (finPart D) = 0 → (κ w).map (finPart D) = 0)) := by
  first | exact @GlobalTheory.LinkKappa.kappa_props | exact GlobalTheory.LinkKappa.kappa_props | (intros; apply GlobalTheory.LinkKappa.kappa_props <;> assumption)

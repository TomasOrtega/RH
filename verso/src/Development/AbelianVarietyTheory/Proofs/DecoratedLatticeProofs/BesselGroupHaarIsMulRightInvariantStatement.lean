import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupHaarIsMulRightInvariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BesUnimod.besGrp_isMulRightInvariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FBesselGroupHaarIsMulRightInvariant.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.besselGroup_haar_isMulRightInvariant : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L) (μ : Measure (besGrp d o)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.BesUnimod.besGrp_isMulRightInvariant | exact GlobalTheory.BesUnimod.besGrp_isMulRightInvariant | (intros; apply GlobalTheory.BesUnimod.besGrp_isMulRightInvariant <;> assumption)

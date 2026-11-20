import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphWittFlagCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MixPer.flagCoord_homeo` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsHomeomorphWittFlagCoordinates.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.exists_homeomorph_wittFlagCoordinates : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ e : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) ≃ₜ flagN d, ∀ p, (e p : GA D S) = d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2) := by
  first | exact @GlobalTheory.MixPer.flagCoord_homeo | exact GlobalTheory.MixPer.flagCoord_homeo | (intros; apply GlobalTheory.MixPer.flagCoord_homeo <;> assumption)

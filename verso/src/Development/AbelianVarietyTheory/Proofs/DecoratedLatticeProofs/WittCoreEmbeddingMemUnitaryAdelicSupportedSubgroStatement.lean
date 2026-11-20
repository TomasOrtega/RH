import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgro
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FWittCoreEmbeddingMemUnitaryAdelicSupportedSubgro.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.emb0_mem_grpAt_of_mem_grpAt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (P : Pl D → Prop) (g : GA D S₀), g ∈ grpAt S₀ P → d.emb0 g ∈ grpAt S P := by
  first | exact @GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup | exact GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup | (intros; apply GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup <;> assumption)

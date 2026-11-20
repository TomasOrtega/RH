import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepU
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryHighestWeight.exists_isHCTypeU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FExistsHighestWeightIrreducibleUnitaryRepU.lean&line=221#L221)
-/
theorem _root_.GlobalTheory.T.exists_highestWeight_irreducible_unitaryRep_U : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π → (∀ S : Submodule ℂ W, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∃ u, PI.UpqRep.IsHCTypeU k u π := by
  first | exact @GlobalTheory.UnitaryHighestWeight.exists_isHCTypeU | exact GlobalTheory.UnitaryHighestWeight.exists_isHCTypeU | (intros; apply GlobalTheory.UnitaryHighestWeight.exists_isHCTypeU <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSelfDualLatticesSingleOrbitTamePlace.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.selfDualLattices_single_orbit_tamePlace : ∀ (D : D7) (S₀ : HSp D) (v : Pl D) (Λ Λ' : AddSubgroup (Fin S₀.rank → AE D)), Tame D v → IsSDAt S₀ v Λ → IsSDAt S₀ v Λ' → ∃ γ ∈ grpAt S₀ (· = v), ∀ y : Fin S₀.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ mt S₀ γ *ᵥ y ∈ Λ') := by
  first | exact @GlobalTheory.IwaOrbit.selfDual_orbit | exact GlobalTheory.IwaOrbit.selfDual_orbit | (intros; apply GlobalTheory.IwaOrbit.selfDual_orbit <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCover
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCechVanishingFromCover.lean&line=185#L185)
-/
theorem _root_.GlobalTheory.T.cech_vanishing_from_cover : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS U S) j)) → ∀ j < s, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS U S) j)) → ∀ j, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS U S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H F j)) := by
  first | exact @GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover | exact GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover | (intros; apply GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover <;> assumption)

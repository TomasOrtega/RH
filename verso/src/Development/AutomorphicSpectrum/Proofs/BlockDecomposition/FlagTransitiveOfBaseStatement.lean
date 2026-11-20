import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagTransitiveOfBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFlagTransitiveOfBase.lean&line=654#L654)
-/
theorem _root_.GlobalTheory.T.flag_transitive_of_base : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 → HasBase c 𝔬 → FlagTransitive c 𝔬 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive | exact GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive | (intros; apply GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive <;> assumption)

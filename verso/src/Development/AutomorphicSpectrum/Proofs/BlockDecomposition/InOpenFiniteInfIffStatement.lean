import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FInOpenFiniteInfIff.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.inOpen_finite_inf_iff : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (T : Thick (nlFun γ p X q κ)), InU (⨅ α ∈ S, U α) T ↔ ∀ α ∈ S, InU (U α) T := by
  first | exact @GlobalTheory.CompanionTheory.Thick.inU_iInf_finset | exact GlobalTheory.CompanionTheory.Thick.inU_iInf_finset | (intros; apply GlobalTheory.CompanionTheory.Thick.inU_iInf_finset <;> assumption)

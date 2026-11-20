import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetUnitIdealIntegral
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCosetUnitIdealIntegral.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.coset_unit_ideal_integral : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  first | exact @GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top | exact GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top | (intros; apply GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top <;> assumption)

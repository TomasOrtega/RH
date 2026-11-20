import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCongruenceRefinement
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCosetCongruenceRefinement.lean&line=290#L290)
-/
theorem _root_.GlobalTheory.T.coset_congruence_refinement : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)), v ∉ S → ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → ¬ I ≤ v.asIdeal → ∀ (k : ℕ) (x0 : ι → F) (c : ι → Fv F v), ∃ x1 : ι → F, ∀ x : ι → F, (x ∈ cosetOff (insert v S) I x0 ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ cosetOff S (I * v.asIdeal ^ k) x1 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step | exact GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step | (intros; apply GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step <;> assumption)

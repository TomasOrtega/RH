import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitone
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlgWtHW.hw_exists_unique_antitone` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAlgWeightHighestWeightExistsUniqueAntitone.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (τ : L →+* ℂ), (∃! lam, a.HWAt τ lam) ∧ ∀ lam, a.HWAt τ lam → Antitone lam := by
  first | exact @GlobalTheory.AlgWtHW.hw_exists_unique_antitone | exact GlobalTheory.AlgWtHW.hw_exists_unique_antitone | (intros; apply GlobalTheory.AlgWtHW.hw_exists_unique_antitone <;> assumption)

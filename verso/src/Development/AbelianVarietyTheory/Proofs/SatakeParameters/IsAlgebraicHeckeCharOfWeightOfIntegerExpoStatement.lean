import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
open NumberField Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FIsAlgebraicHeckeCharOfWeightOfIntegerExpo.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.isAlgebraicHeckeCharOfWeight_of_integer_expo : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E) (n : (E →+* ℂ) → ℤ), (∀ τ, expo χ τ = n τ) → IsAlgPos χ n := by
  first | exact @GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo | exact GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo | (intros; apply GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo <;> assumption)

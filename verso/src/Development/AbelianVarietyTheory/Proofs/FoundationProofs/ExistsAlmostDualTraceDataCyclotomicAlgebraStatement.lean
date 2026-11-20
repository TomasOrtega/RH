import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataCyclotomicAlgebra
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RecOne.TrCyc.exists_trData_cycAlg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsAlmostDualTraceDataCyclotomicAlgebra.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.exists_almostDualTraceData_cyclotomicAlgebra : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ F : Finset A, ∃ (C : Subalgebra (fixA A) A) (tr : A → A) (n : ℕ) (a b : Fin n → A), (↑F : Set A) ⊆ C ∧ IsTrData (cycAlg l A) C tr a b (l : A) := by
  first | exact @GlobalTheory.RecOne.TrCyc.exists_trData_cycAlg | exact GlobalTheory.RecOne.TrCyc.exists_trData_cycAlg | (intros; apply GlobalTheory.RecOne.TrCyc.exists_trData_cycAlg <;> assumption)

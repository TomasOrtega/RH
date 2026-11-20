import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramifiedQuotient : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, dual1 W a = 1 := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified <;> assumption)

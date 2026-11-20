import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeSummand
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FLocallyFreeBaseChangeSummand.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.locally_free_base_change_summand : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] (b : V →ₗ[Ω] Vc), IsBaseChange C b → ∀ (L : AddSubgroup V) (U : Submodule Ω V), (∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) → Summand L U → Summand (spanOver RC (b '' L)) (Submodule.span C (b '' U)) ∧ spanOver RC (b '' L) ⊓ (Submodule.span C (b '' U)).toAddSubgroup = spanOver RC (b '' (L ⊓ U.toAddSubgroup : AddSubgroup V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange | exact GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange <;> assumption)

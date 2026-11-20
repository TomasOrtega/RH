import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeTestPointMembership
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FLocallyFreeTestPointMembership.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.locally_free_test_point_membership : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ {ι : Type} [Fintype ι] (N : ℕ) (L : AddSubgroup (ι → Ω)), LocFree R N L → ∀ v : ι → Ω, (∃ m : ℕ, (p : Ω) ^ m • v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → bcMap Ω C ι v ∈ spanOver RC (bcMap Ω C ι '' L)) → v ∈ L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main | exact GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main <;> assumption)

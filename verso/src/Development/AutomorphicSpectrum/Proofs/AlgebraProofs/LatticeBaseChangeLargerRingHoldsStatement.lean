import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBaseChangeLargerRingHolds
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FLatticeBaseChangeLargerRingHolds.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.lattice_base_change_larger_ring_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → CharData RC p (algebraMap Ω C w) (fun τ a => algebraMap Ω C (χ τ a)) ∧ (D.bc RC).Base RC p (algebraMap Ω C w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring | exact GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring <;> assumption)

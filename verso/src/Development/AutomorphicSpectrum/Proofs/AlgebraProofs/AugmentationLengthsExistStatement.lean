import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthsExist
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.GR.lens_exist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FAugmentationLengthsExist.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.augmentation_lengths_exist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∃ cA cN cO : NNReal, cA ≠ 0 ∧ cN ≠ 0 ∧ cO ≠ 0 ∧ HasLen v R (AFQuot p AA.carrier) cA ∧ HasColen R v AA.carrier cN ∧ HasLen v R (OmAA AA.carrier) cO := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.lens_exist | exact GlobalTheory.CompanionTheory.Ar.GR.lens_exist | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.lens_exist <;> assumption)

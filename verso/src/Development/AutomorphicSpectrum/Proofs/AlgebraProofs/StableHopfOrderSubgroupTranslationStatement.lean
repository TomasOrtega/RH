import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupTranslation
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.GR.step_hopf_line` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FStableHopfOrderSubgroupTranslation.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_translation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → (∃ S : HopfOrder (C := C) R F, S.carrier = stepOrder AA.carrier K t ∧ FStable F S.carrier) ∧ stepOrder AA.carrier K t = stepOrderRes AA.carrier K t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.step_hopf_line | exact GlobalTheory.CompanionTheory.Ar.GR.step_hopf_line | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.step_hopf_line <;> assumption)

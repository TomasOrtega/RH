import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsAddCharacters
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FHopfOrderContainsAddCharacters.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.hopf_order_contains_add_characters : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder | exact GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder <;> assumption)

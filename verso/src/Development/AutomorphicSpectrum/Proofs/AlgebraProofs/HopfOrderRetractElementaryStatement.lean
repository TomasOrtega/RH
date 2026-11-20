import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractElementary
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FHopfOrderRetractElementary.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.hopf_order_retract_elementary : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary | exact GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary | (intros; apply GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary <;> assumption)

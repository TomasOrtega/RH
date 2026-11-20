import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomLiftResiduePointFiniteFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ResiduePointLift.exists_algHom_lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAlgHomLiftResiduePointFiniteFlat.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_algHom_lift_residuePoint_finite_flat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] (c : A →ₐ[O] IsLocalRing.ResidueField O), ∃ x : A →ₐ[O] O, ∀ a, IsLocalRing.residue O (x a) = c a := by
  first | exact @GlobalTheory.ResiduePointLift.exists_algHom_lift | exact GlobalTheory.ResiduePointLift.exists_algHom_lift | (intros; apply GlobalTheory.ResiduePointLift.exists_algHom_lift <;> assumption)

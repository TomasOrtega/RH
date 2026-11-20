import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyRestrictScalars
import Mathlib
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.natCard_homology_restrictScalars` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNatCardHomologyRestrictScalars.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.natCard_homology_restrictScalars_alt : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ), Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  first | exact @GlobalTheory.natCard_homology_restrictScalars | exact GlobalTheory.natCard_homology_restrictScalars | (intros; apply GlobalTheory.natCard_homology_restrictScalars <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalHomFactorsAffineOpen
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.spec_local_hom_factors_affineOpen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpecLocalHomFactorsAffineOpen.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_ringHom_spec_factor_fromSpec_of_closedPoint_mem : ∀ (X : Scheme.{0}) (V : X.Opens) (hV : IsAffineOpen V) (A : Type) [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ X), f (IsLocalRing.closedPoint A) ∈ V →
    ∃ g : Γ(X, V) →+* A, f = Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec := by
  first | exact @GlobalTheory.spec_local_hom_factors_affineOpen | exact GlobalTheory.spec_local_hom_factors_affineOpen | (intros; apply GlobalTheory.spec_local_hom_factors_affineOpen <;> assumption)

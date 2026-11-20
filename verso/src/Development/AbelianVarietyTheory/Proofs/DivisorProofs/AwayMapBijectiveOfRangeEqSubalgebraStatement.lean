import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapBijectiveOfRangeEqSubalgebra
import Mathlib
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAwayMapBijectiveOfRangeEqSubalgebra.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by
  first | exact @GlobalTheory.awayMap_bijective_of_range_eq_subalgebra | exact GlobalTheory.awayMap_bijective_of_range_eq_subalgebra | (intros; apply GlobalTheory.awayMap_bijective_of_range_eq_subalgebra <;> assumption)

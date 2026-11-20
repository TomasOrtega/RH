import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightComapFlatHeightOne
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHeightComapFlatHeightOne.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.height_comap_flat_height_one : ∀ {A R : Type} [CommRing A] [IsDomain A] [CommRing R] (φ : A →+* R), φ.Flat → ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap φ ≠ ⊥ → (Q.comap φ).height = 1 := by
  first | exact @GlobalTheory.height_comap_eq_one_of_flat | exact GlobalTheory.height_comap_eq_one_of_flat | (intros; apply GlobalTheory.height_comap_eq_one_of_flat <;> assumption)

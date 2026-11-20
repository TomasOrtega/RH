import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatMapColonIdeal
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFlatMapColonIdeal.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.flat_map_colon_ideal : ∀ {A R : Type} [CommRing A] [IsNoetherianRing A] [CommRing R] (φ : A →+* R), φ.Flat → ∀ I J : Ideal A, (I.colon J).map φ = (I.map φ).colon (J.map φ) := by
  first | exact @GlobalTheory.ideal_map_colon_eq_of_flat | exact GlobalTheory.ideal_map_colon_eq_of_flat | (intros; apply GlobalTheory.ideal_map_colon_eq_of_flat <;> assumption)

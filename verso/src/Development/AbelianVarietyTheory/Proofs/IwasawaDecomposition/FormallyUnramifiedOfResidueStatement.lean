import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedOfResidue
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFormallyUnramifiedOfResidue.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.formallyUnramified_of_residue : ∀ {A B R : Type} [CommRing A] [CommRing B] [IsLocalRing B] [CommRing R] [IsLocalRing R] (ι : A →+* B) (ψ : B →+* R), ψ.Finite → (maximalIdeal B).map ψ = maximalIdeal R → ((residue R).comp (ψ.comp ι)).FormallyUnramified → ψ.FormallyUnramified := by
  first | exact @GlobalTheory.formallyUnramified_of_finite_map_maximalIdeal | exact GlobalTheory.formallyUnramified_of_finite_map_maximalIdeal | (intros; apply GlobalTheory.formallyUnramified_of_finite_map_maximalIdeal <;> assumption)

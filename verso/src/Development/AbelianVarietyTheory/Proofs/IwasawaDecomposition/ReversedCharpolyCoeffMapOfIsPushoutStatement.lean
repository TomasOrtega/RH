import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReversedCharpolyCoeffMapOfIsPushout
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FReversedCharpolyCoeffMapOfIsPushout.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout : ∀ {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    Function.Injective α → ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ),
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  first | exact @GlobalTheory.NormalDescent.normCoeff_map_of_isPushout | exact GlobalTheory.NormalDescent.normCoeff_map_of_isPushout | (intros; apply GlobalTheory.NormalDescent.normCoeff_map_of_isPushout <;> assumption)

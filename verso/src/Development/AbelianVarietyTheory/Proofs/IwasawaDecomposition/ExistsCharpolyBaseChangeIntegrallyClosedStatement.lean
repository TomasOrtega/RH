import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpolyBaseChangeIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormalDescent.exists_map_eq_charK` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCharpolyBaseChangeIntegrallyClosed.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed : ∀ {A B K : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K]
    [Algebra A K] [IsFractionRing A K] (φ : A →+* B) (hφ : φ.Finite) (b : B),
    ∃ P : A[X], P.map (algebraMap A K) = charK φ hφ K b := by
  first | exact @GlobalTheory.NormalDescent.exists_map_eq_charK | exact GlobalTheory.NormalDescent.exists_map_eq_charK | (intros; apply GlobalTheory.NormalDescent.exists_map_eq_charK <;> assumption)

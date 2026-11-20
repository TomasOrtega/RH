import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesKaehlerBasis
open scoped TensorProduct Polynomial
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleCoordinatesKaehlerBasis.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.etale_coordinates_kaehler_basis : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.Smooth R B] (d : ℕ) (t : Fin d → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) → ∃ h : B, algebraMap B K h ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away h)) (fun a => algebraMap B (Localization.Away h) (t a))).Etale := by
  first | exact @_root_.GlobalTheory.EtaleCoordSpread.exists_away_etale | exact _root_.GlobalTheory.EtaleCoordSpread.exists_away_etale | (intros; apply _root_.GlobalTheory.EtaleCoordSpread.exists_away_etale <;> assumption)

import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateQuotientRegular
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleCoordinateQuotientRegular.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.etale_coordinate_quotient_regular : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by
  first | exact @_root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate | exact _root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate | (intros; apply _root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIso
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HilbertSch.isHilbRep_transfer` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsHilbertSchemeRepresentableOfIso.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_iso : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z), eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  first | exact @GlobalTheory.HilbertSch.isHilbRep_transfer | exact GlobalTheory.HilbertSch.isHilbRep_transfer | (intros; apply GlobalTheory.HilbertSch.isHilbRep_transfer <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.VertProj.isProjOver_strHom_zmod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FClosedSubschemeModLProjective.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.closed_subscheme_mod_l_projective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) Z) := by
  first | exact @GlobalTheory.VertProj.isProjOver_strHom_zmod | exact GlobalTheory.VertProj.isProjOver_strHom_zmod | (intros; apply GlobalTheory.VertProj.isProjOver_strHom_zmod <;> assumption)

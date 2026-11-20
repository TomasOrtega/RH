import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverOverFiniteExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRegularCoverOverFiniteExtension.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.regular_cover_over_finite_extension : GlobalTheory.Published.RegularAlteration → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ (F : Type) [Field F] [Algebra X.functionField F], FiniteDimensional X.functionField F → ∃ (C : RegCover p) (t : Sp C.Y.functionField ⟶ Sp F), t ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)) ≫ X.fromSpecStalk (genericPoint X) = C.Y.fromSpecStalk (genericPoint C.Y) ≫ C.ρ := by
  first | exact @GlobalTheory.RegCoverExt.exists_regCover_extension | exact GlobalTheory.RegCoverExt.exists_regCover_extension | (intros; apply GlobalTheory.RegCoverExt.exists_regCover_extension <;> assumption)

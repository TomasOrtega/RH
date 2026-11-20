import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyExistsUniqueClassifyScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSiegelFamilyExistsUniqueClassifyScheme.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.siegelFamily_existsUnique_classify_scheme : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal → ∃! f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegFamAll.existsUnique_classify | exact GlobalTheory.SiegFamAll.existsUnique_classify | (intros; apply GlobalTheory.SiegFamAll.existsUnique_classify <;> assumption)

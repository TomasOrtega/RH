import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlat
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSiegelFamilyClassifiedOfFaithfullyFlat.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R R').comp β)), SiegPB c' c (spMap (algebraMap R R')) → ∃ f : Sp R' ⟶ F.X, f ≫ F.s = spMap ((algebraMap R R').comp β) ∧ SiegPB c' F.univ f) → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegFpqcDesc.classified_of_faithfullyFlat | exact GlobalTheory.SiegFpqcDesc.classified_of_faithfullyFlat | (intros; apply GlobalTheory.SiegFpqcDesc.classified_of_faithfullyFlat <;> assumption)

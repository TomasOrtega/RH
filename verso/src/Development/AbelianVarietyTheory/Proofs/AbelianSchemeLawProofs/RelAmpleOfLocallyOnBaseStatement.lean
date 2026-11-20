import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
/- English proof (citation)
Apply `GlobalTheory.AmpleLocal.relAmple_of_locally` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAbelianSchemeLawProofs%2FRelAmpleOfLocallyOnBase.lean&line=450#L450)
-/
theorem _root_.GlobalTheory.T.relAmple_of_locally_on_base : ∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom → QuasiSeparated A.hom → (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U), RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) → RelAmple A L := by
  first | exact @GlobalTheory.AmpleLocal.relAmple_of_locally | exact GlobalTheory.AmpleLocal.relAmple_of_locally | (intros; apply GlobalTheory.AmpleLocal.relAmple_of_locally <;> assumption)

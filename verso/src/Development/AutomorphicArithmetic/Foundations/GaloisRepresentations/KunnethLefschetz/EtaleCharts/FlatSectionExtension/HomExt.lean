import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Introduce `V X a b h`. Use `choose W hxW hW using h`. Establish `hcov : TopologicalSpace.IsOpenCover W`. Use `TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr ?_)` and prove the remaining obligations. Introduce `x _`.

Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩`. Conclude with `(V.openCoverOfIsOpenCover W hcov).hom_ext _ _ hW`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.homExt :
    ∀ {V X : Scheme.{0}} (a b : V ⟶ X), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ U.ι ≫ a = U.ι ≫ b) → a = b := by
  intro V X a b h
  choose W hxW hW using h
  have hcov : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr ?_)
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  exact (V.openCoverOfIsOpenCover W hcov).hom_ext _ _ hW

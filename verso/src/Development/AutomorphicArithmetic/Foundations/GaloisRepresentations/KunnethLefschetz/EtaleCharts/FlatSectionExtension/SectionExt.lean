import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Introduce `V s s' h`. Use `choose U hxU hU using h`. Use `TopCat.Sheaf.eq_of_locally_eq' V.sheaf (fun x => (U x).ι ''ᵁ ⊤) ⊤ (fun x => homOfLE le_top) ?_ s s' ?_` and prove the remaining obligations. Introduce `y _`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨y, ⟨⟨y, hxU y⟩, trivial, rfl⟩⟩`.

Introduce `x`. Conclude with `hU x`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sectionExt :
    ∀ {V : Scheme.{0}} (s s' : Γ(V, ⊤)), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ U.ι.appTop.hom s = U.ι.appTop.hom s') → s = s' := by
  intro V s s' h
  choose U hxU hU using h
  refine TopCat.Sheaf.eq_of_locally_eq' V.sheaf (fun x => (U x).ι ''ᵁ ⊤) ⊤
    (fun x => homOfLE le_top) ?_ s s' ?_
  · intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, ⟨⟨y, hxU y⟩, trivial, rfl⟩⟩
  · intro x
    exact hU x

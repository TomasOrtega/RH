import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealArithmeticVarietyImageStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealFibreChartDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

/- English proof (translation)
Introduce `K _ ι _ K₂ _ ι₂ _ P d g δ hP hg hne`. Take `⟨h1, h2⟩` from `GlobalTheory.T.graph_ideal_arithmetic_variety_image K ι K₂ ι₂ P d g δ hP hg hne`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Introduce `G J hJ`. Establish `hP' : IsArithVar (imageZ inlV (graphIdeal P g)) d` using `by rw [h2]; exact hP`.

Establish `hF : IsProjVarF (fibreIdeal Sum.inl G) 0` using `GlobalTheory.CompanionTheory.Ar.Giv.fibreDim K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV (graphIdeal P g) d 0 G isBlockMap_inl h1 hP'`. Establish `hrel` using `hF.1.2.2`. Set `i : ∀ k, fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k` to `fun k => (hrel k).choose`. Establish `hi : IsChart (fibreIdeal Sum.inl G) i` using `fun k => (hrel k).choose_spec`. Rewrite using `[hJ.1 _ _ i hF hi]`.

Conclude with `GlobalTheory.T.graph_ideal_fibre_chart_degree K ι K₂ ι₂ P g hP.2.1.1 hne h2 G i hi` after adjusting the coercions.
-/
theorem graphStatement : GraphStatement := by
  intro K _ ι _ K₂ _ ι₂ _ P d g δ hP hg hne
  obtain ⟨h1, h2⟩ := GlobalTheory.T.graph_ideal_arithmetic_variety_image K ι K₂ ι₂ P d g δ hP hg hne
  refine ⟨h1, h2, ?_⟩
  intro G J hJ
  have hP' : IsArithVar (imageZ inlV (graphIdeal P g)) d := by rw [h2]; exact hP
  have hF : IsProjVarF (fibreIdeal Sum.inl G) 0 :=
    GlobalTheory.CompanionTheory.Ar.Giv.fibreDim K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV (graphIdeal P g) d 0 G
      isBlockMap_inl h1 hP'
  have hrel := hF.1.2.2
  let i : ∀ k, fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k := fun k => (hrel k).choose
  have hi : IsChart (fibreIdeal Sum.inl G) i := fun k => (hrel k).choose_spec
  rw [hJ.1 _ _ i hF hi]
  exact_mod_cast GlobalTheory.T.graph_ideal_fibre_chart_degree K ι K₂ ι₂ P g hP.2.1.1 hne h2 G i hi

end GlobalTheory.CompanionTheory.Ar.Giv

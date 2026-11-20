import Mathlib
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

variable {X : Scheme.{u}}

/- English proof (authored)
Listing the values of the finite family in index order gives the factors of its finite product. The unit ideal is the multiplicative identity, so multiplying that list with the unit as the initial value gives this product.
-/
private theorem foldr_mul_ofFn_eq_prod {Z : Scheme.{u}} {n : ℕ} (f : Fin n → Z.IdealSheafData) :
    (List.ofFn f).foldr (· * ·) ⊤ = ∏ i, f i := by
  rw [← Scheme.IdealSheafData.one_eq_top]
  exact List.prod_ofFn

/- English proof (authored)
A boundary ideal in the list occurs at some index, so its restriction is a value of the indexed family. Conversely, every value of that family is the restriction of a listed ideal. This proves equality of the two sets.
-/
private theorem image_comap_eq_range_get (E : List X.IdealSheafData) (U : X.Opens) :
    (fun D : X.IdealSheafData => D.comap U.ι) '' {D | D ∈ E} =
      Set.range (fun i : Fin E.length => (E.get i).comap U.ι) := by
  ext w
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨i, hi, hEi⟩ := List.mem_iff_getElem.mp hD
    exact ⟨⟨i, hi⟩, by simp [hEi]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨E.get i, by simp, rfl⟩

/- English proof (authored)
The definition of being monomial near the point asks for an open neighborhood where the ideal is a product of powers of the restricted boundary ideals. Writing the powers in boundary index order gives precisely the stated product.
-/
private theorem isMonomialNear_iff_exists_pow_prod (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (x : ↥X) :
    IsMonomialNear E M x ↔ ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
      M.comap U.ι =
        (List.ofFn (fun i : Fin E.length => (E.get i).comap U.ι ^ a i)).foldr (· * ·) ⊤ :=
  Iff.rfl

/- English proof (authored)
On a proposed neighborhood, the restrictions of the listed boundary ideals are the finite indexed family of generators. A product of nonnegative powers of that family belongs to the generated submonoid. Conversely, a finite product of generators can be collected by index because ideal multiplication is commutative. The resulting exponents give the required monomial expression on the same neighborhood.
-/
theorem isMonomialNear_iff_mem_closure (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (x : ↥X) :
    IsMonomialNear E M x ↔ ∃ U : X.Opens, x ∈ U ∧
      M.comap U.ι ∈
        Submonoid.closure ((fun D : X.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}) := by
  rw [isMonomialNear_iff_exists_pow_prod]
  constructor
  · rintro ⟨U, hxU, a, ha⟩
    refine ⟨U, hxU, ?_⟩
    rw [image_comap_eq_range_get, ha, foldr_mul_ofFn_eq_prod, Submonoid.mem_closure_range_iff_of_fintype]
    exact ⟨a, rfl⟩
  · rintro ⟨U, hxU, hmem⟩
    rw [image_comap_eq_range_get, Submonoid.mem_closure_range_iff_of_fintype] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨U, hxU, a, ?_⟩
    rw [foldr_mul_ofFn_eq_prod, ha]

/- English proof (authored)
Keep the neighborhood on which the monomial expression holds. Each nonunit boundary ideal in the old list occurs in the new one, so its restriction belongs to the new generated submonoid. A unit ideal restricts to the multiplicative identity and also belongs. Thus the old generators, and hence the restricted monomial ideal they generate, belong to the new submonoid.
-/
theorem IsMonomialNear.mono {E E' : List X.IdealSheafData}
    (h : ∀ D ∈ E, D ≠ ⊤ → D ∈ E') {M : X.IdealSheafData} {x : ↥X}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x := by
  obtain ⟨U, hxU, hmem⟩ := (isMonomialNear_iff_mem_closure E M x).mp hM
  refine (isMonomialNear_iff_mem_closure E' M x).mpr ⟨U, hxU, ?_⟩
  refine Submonoid.closure_le.mpr ?_ hmem
  rintro w hw
  obtain ⟨D, hD, hDw⟩ := hw
  have hDw' : D.comap U.ι = w := hDw
  subst hDw'
  by_cases hDtop : D = ⊤
  · have hone : D.comap U.ι = 1 := by
      simp [hDtop, Scheme.IdealSheafData.one_eq_top]
    rw [hone]
    exact SetLike.mem_coe.mpr (one_mem _)
  · exact Submonoid.subset_closure ⟨D, h D hD hDtop, rfl⟩

/- English proof (authored)
Equality of the two sets of nonunit boundary ideals implies that each nonunit ideal from the first list belongs to the second. The monotonicity result transfers the local monomial expression.
-/
theorem IsMonomialNear.congr_setOf {E E' : List X.IdealSheafData}
    (h : {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} = {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤})
    {M : X.IdealSheafData} {x : ↥X} (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.mono fun D hD hne => (((Set.ext_iff.mp h) D).mp ⟨hD, hne⟩).1

/- English proof (authored)
The boundary relation implies equality of the sets of nonunit boundary ideals. Apply the result that local monomiality is preserved by such equality.
-/
theorem IsMonomialNear.congr_sameNontrivialBoundary {E E' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') {M : X.IdealSheafData} {x : ↥X}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.congr_setOf h.setOf_mem_ne_top_eq

/- English proof (authored)
The geometry hypotheses preserve admissibility when the boundary is replaced by one with the same nonunit entries. At each point of the cosupport the original triple provides a local monomial expression. The ideal and mark are unchanged, and equality of the nontrivial boundary entries lets that expression be read with the new boundary.
-/
theorem isLocallyMonomialTriple_withBoundary (hG : MonomialGeometryHypotheses.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : IsLocallyMonomialTriple T)
    (E' : List T.scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E') :
    IsLocallyMonomialTriple (T.withBoundary E') :=
  { valid := hG.withBoundary_valid T hT.valid E' hE
    monomialNear := fun x hx => (hT.monomialNear x hx).congr_sameNontrivialBoundary hE }

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end

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

/- English proof (translation)
Rewrite using `[← Scheme.IdealSheafData.one_eq_top]`. Conclude with `List.prod_ofFn`.
-/
private theorem foldr_mul_ofFn_eq_prod {Z : Scheme.{u}} {n : ℕ} (f : Fin n → Z.IdealSheafData) :
    (List.ofFn f).foldr (· * ·) ⊤ = ∏ i, f i := by
  rw [← Scheme.IdealSheafData.one_eq_top]
  exact List.prod_ofFn

/- English proof (translation)
Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨D, hD, rfl⟩`. Take `⟨i, hi, hEi⟩` from `List.mem_iff_getElem.mp hD`. Conclude with `⟨⟨i, hi⟩, by simp [hEi]⟩`.

Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨E.get i, by simp, rfl⟩`.
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

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem isMonomialNear_iff_exists_pow_prod (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (x : ↥X) :
    IsMonomialNear E M x ↔ ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
      M.comap U.ι =
        (List.ofFn (fun i : Fin E.length => (E.get i).comap U.ι ^ a i)).foldr (· * ·) ⊤ :=
  Iff.rfl

/- English proof (translation)
Rewrite using `[isMonomialNear_iff_exists_pow_prod]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨U, hxU, a, ha⟩`. Use `⟨U, hxU, ?_⟩` and prove the remaining obligations. Rewrite using `[image_comap_eq_range_get, ha, foldr_mul_ofFn_eq_prod, Submonoid.mem_closure_range_iff_of_fintype]`.

Conclude with `⟨a, rfl⟩`. Introduce and unpack `⟨U, hxU, hmem⟩`. Rewrite `hmem` using `[image_comap_eq_range_get, Submonoid.mem_closure_range_iff_of_fintype]`. Take `⟨a, ha⟩` from `hmem`. Use `⟨U, hxU, a, ?_⟩` and prove the remaining obligations.

Rewrite using `[foldr_mul_ofFn_eq_prod, ha]`.
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

/- English proof (translation)
Take `⟨U, hxU, hmem⟩` from `(isMonomialNear_iff_mem_closure E M x).mp hM`. Use `(isMonomialNear_iff_mem_closure E' M x).mpr ⟨U, hxU, ?_⟩` and prove the remaining obligations. Use `Submonoid.closure_le.mpr ?_ hmem` and prove the remaining obligations. Introduce and unpack `w hw`. Take `⟨D, hD, hDw⟩` from `hw`.

Establish `hDw' : D.comap U.ι = w` using `hDw`. Substitute `hDw'` using the available equality. Distinguish the cases in `hDtop : D = ⊤`. Establish `hone : D.comap U.ι = 1`. Simplify using `[hDtop, Scheme.IdealSheafData.one_eq_top]`.

Rewrite using `[hone]`. Conclude with `SetLike.mem_coe.mpr (one_mem _)`. Conclude with `Submonoid.subset_closure ⟨D, h D hD hDtop, rfl⟩`.
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

/- English proof (translation)
The claim follows from `hM.mono fun D hD hne => (((Set.ext_iff.mp h) D).mp ⟨hD, hne⟩).1`.
-/
theorem IsMonomialNear.congr_setOf {E E' : List X.IdealSheafData}
    (h : {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} = {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤})
    {M : X.IdealSheafData} {x : ↥X} (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.mono fun D hD hne => (((Set.ext_iff.mp h) D).mp ⟨hD, hne⟩).1

/- English proof (translation)
The claim follows from `hM.congr_setOf h.setOf_mem_ne_top_eq`.
-/
theorem IsMonomialNear.congr_sameNontrivialBoundary {E E' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') {M : X.IdealSheafData} {x : ↥X}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.congr_setOf h.setOf_mem_ne_top_eq

/- English proof (translation)
The claim follows from `{ valid := hG.withBoundary_valid T hT.valid E' hE monomialNear := fun x hx => (hT.monomialNear x hx).congr_sameNontrivialBoundary hE }`.
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

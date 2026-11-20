import Mathlib
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

/- English proof (translation)
Introduce `X Y _ π _ U V hU hV hne h hfin`. Establish `: IsAffine U` using `hU`. Establish `: IsAffine V` using `hV`. Establish `hf : IsFinite (π.resLE U V h)`. Establish `hS : IsFinite (Spec.map (π.resLE U V h).appTop)` using `(IsFinite.SpecMap_iff _).mpr ((RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso π U V h)).mpr hfin)`.

Rewrite using `[Arrow.iso_w' (arrowIsoSpecΓOfIsAffine (π.resLE U V h)).symm]`. Use `infer_instance`. Establish `: UniversallyClosed (Y.homOfLE h ≫ π ∣_ U)`. Express the relevant statement in the definitionally equal form `UniversallyClosed (π.resLE U V h)`. Use `infer_instance`.

Establish `: UniversallyClosed (Y.homOfLE h)` using `.of_comp_of_isSeparated _ (π ∣_ U)`. Take `⟨y, hy⟩` from `hne`. Establish `: Nonempty (π ⁻¹ᵁ U)` using `⟨⟨y, h hy⟩⟩`. Establish `hcl : IsClopen (Set.range (Y.homOfLE h).base)` using `⟨(Y.homOfLE h).isClosedMap.isClosed_range, (Y.homOfLE h).isOpenEmbedding.isOpenMap.isOpen_range⟩`. Establish `huniv : Set.range (Y.homOfLE h).base = Set.univ` using `(isClopen_iff.mp hcl).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨_, ⟨⟨y, hy⟩, rfl⟩⟩)`.

Use `le_antisymm (fun x hx => ?_) h` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨⟨w, hw⟩, hz⟩ : (⟨x, hx⟩ : π ⁻¹ᵁ U) ∈ Set.range (Y.homOfLE h).base := by`. Rewrite using `[huniv]`. Discharge the goal by the elementary cases of `trivial`. Establish `hz' : ((Y.homOfLE h) ⟨w, hw⟩).1 = x` using `congrArg Subtype.val hz`.

Establish `hzx : w = x` using `(Scheme.homOfLE_apply h ⟨w, hw⟩).symm.trans hz'`. Conclude with `hzx ▸ hw`.
-/
theorem preimage_eq_of_finite_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π] {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → IsAffineOpen V → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (π.appLE U V h).hom.Finite → π ⁻¹ᵁ U = V := by
  intro X Y _ π _ U V hU hV hne h hfin
  have : IsAffine U := hU
  have : IsAffine V := hV
  have hf : IsFinite (π.resLE U V h) := by
    have hS : IsFinite (Spec.map (π.resLE U V h).appTop) := (IsFinite.SpecMap_iff _).mpr
      ((RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso π U V h)).mpr hfin)
    rw [Arrow.iso_w' (arrowIsoSpecΓOfIsAffine (π.resLE U V h)).symm]
    infer_instance
  have : UniversallyClosed (Y.homOfLE h ≫ π ∣_ U) := by
    change UniversallyClosed (π.resLE U V h)
    infer_instance
  have : UniversallyClosed (Y.homOfLE h) := .of_comp_of_isSeparated _ (π ∣_ U)
  obtain ⟨y, hy⟩ := hne
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨y, h hy⟩⟩
  have hcl : IsClopen (Set.range (Y.homOfLE h).base) :=
    ⟨(Y.homOfLE h).isClosedMap.isClosed_range,
      (Y.homOfLE h).isOpenEmbedding.isOpenMap.isOpen_range⟩
  have huniv : Set.range (Y.homOfLE h).base = Set.univ :=
    (isClopen_iff.mp hcl).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨_, ⟨⟨y, hy⟩, rfl⟩⟩)
  refine le_antisymm (fun x hx => ?_) h
  obtain ⟨⟨w, hw⟩, hz⟩ : (⟨x, hx⟩ : π ⁻¹ᵁ U) ∈ Set.range (Y.homOfLE h).base := by
    rw [huniv]; trivial
  have hz' : ((Y.homOfLE h) ⟨w, hw⟩).1 = x := congrArg Subtype.val hz
  have hzx : w = x := (Scheme.homOfLE_apply h ⟨w, hw⟩).symm.trans hz'
  exact hzx ▸ hw

end GlobalTheory

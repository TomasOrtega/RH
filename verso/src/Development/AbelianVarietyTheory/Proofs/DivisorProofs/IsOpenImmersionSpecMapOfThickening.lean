import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.ThickGlue

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `B₀ 𝒰 haff 𝒜 p hp hloc`. Establish `hloc' : ∀ U ∈ 𝒰, ∀ (a : 𝒜.obj (Opposite.op U)) (W : B₀.Opens) (_ : W = B₀.basicOpen ((p.app (Opposite.op U)).hom a)) (h : W ≤ U), IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op))`. Introduce and unpack `U hU a W rfl h`. Use `letI := (𝒜.map (homOfLE h).op).hom.toAlgebra`. Use `haveI := hloc U hU a`.

Conclude with `IsOpenImmersion.of_isLocalization (S := 𝒜.obj (Opposite.op (B₀.basicOpen ((p.app (Opposite.op U)).hom a)))) a`. Establish `hci : ∀ U ∈ 𝒰, IsClosedImmersion (toSpec p U)` using `fun U hU ↦ isClosedImmersion_toSpec p (haff U hU) (hp U hU).1`. Establish `hsu : ∀ U ∈ 𝒰, Surjective (toSpec p U)` using `fun U hU ↦ surjective_toSpec p (haff U hU) (hp U hU).1 (hp U hU).2`. Establish `hnat : ∀ {U V : B₀.Opens} (h : U ≤ V) (x : U.toScheme), Spec.map (𝒜.map (homOfLE h).op) (toSpec p U x) = toSpec p V (B₀.homOfLE h x)` using `fun h x ↦ congr($(toSpec_naturality p h) x).symm`. Introduce `U hU V hV h`.

Use `hci V hV` as an intermediate fact. Use `hsu U hU` as an intermediate fact. Apply `IsOpenImmersion.of_forall_source_exists` to reduce the goal to its premises. Introduce `x y hxy`. Take `⟨x, rfl⟩` from `(toSpec p U).surjective x`.

Take `⟨y, rfl⟩` from `(toSpec p U).surjective y`. Rewrite `hxy` using `[hnat, hnat]`. Rewrite using `[(B₀.homOfLE h).isOpenEmbedding.injective ((toSpec p V).isClosedEmbedding.injective hxy)]`. Introduce `x`. Take `⟨x, rfl⟩` from `(toSpec p U).surjective x`.

Take `⟨f, hf, hxf⟩` from `(haff V hV).exists_basicOpen_le (V := U) ⟨x.1, x.2⟩ (h x.2)`. Take `⟨a, rfl⟩` from `(hp V hV).1 f`. Establish `h1` using `hloc' U hU ((𝒜.map (homOfLE h).op).hom a) _ (by`. Use `congr($(p.naturality (homOfLE h).op).hom a)` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`.

Rewrite using `[this, Scheme.basicOpen_res]`. Conclude with `(inf_eq_right.mpr hf).symm) hf`. Use `⟨_, _, h1, ⟨toSpec p _ ⟨x.1, hxf⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hnat]`. Use `congr 1`.

Conclude with `Subtype.ext (Scheme.homOfLE_apply _ _)`. Rewrite using `[← Spec.map_comp, ← 𝒜.map_comp]`. Conclude with `hloc' V hV a _ rfl (hf.trans h)`.
-/
theorem isOpenImmersion_specMap_of_thickening : ∀ (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, IsAffineOpen U) → ∀ (𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}) (π : 𝒜 ⟶ B₀.presheaf), (∀ U ∈ 𝒰, Function.Surjective (π.app (op U)).hom ∧ IsNilpotent (RingHom.ker (π.app (op U)).hom)) → (∀ U ∈ 𝒰, ∀ a : 𝒜.obj (op U), letI := (𝒜.map (homOfLE (B₀.basicOpen_le ((π.app (op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a (𝒜.obj (op (B₀.basicOpen ((π.app (op U)).hom a))))) → ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ h : U ≤ V, IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
  intro B₀ 𝒰 haff 𝒜 p hp hloc
  have hloc' : ∀ U ∈ 𝒰, ∀ (a : 𝒜.obj (Opposite.op U)) (W : B₀.Opens)
      (_ : W = B₀.basicOpen ((p.app (Opposite.op U)).hom a)) (h : W ≤ U),
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
    rintro U hU a W rfl h
    letI := (𝒜.map (homOfLE h).op).hom.toAlgebra
    haveI := hloc U hU a
    exact IsOpenImmersion.of_isLocalization
      (S := 𝒜.obj (Opposite.op (B₀.basicOpen ((p.app (Opposite.op U)).hom a)))) a
  have hci : ∀ U ∈ 𝒰, IsClosedImmersion (toSpec p U) := fun U hU ↦
    isClosedImmersion_toSpec p (haff U hU) (hp U hU).1
  have hsu : ∀ U ∈ 𝒰, Surjective (toSpec p U) := fun U hU ↦
    surjective_toSpec p (haff U hU) (hp U hU).1 (hp U hU).2
  have hnat : ∀ {U V : B₀.Opens} (h : U ≤ V) (x : U.toScheme),
      Spec.map (𝒜.map (homOfLE h).op) (toSpec p U x) = toSpec p V (B₀.homOfLE h x) :=
    fun h x ↦ congr($(toSpec_naturality p h) x).symm
  intro U hU V hV h
  have := hci V hV
  have := hsu U hU
  apply IsOpenImmersion.of_forall_source_exists
  · intro x y hxy
    obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
    obtain ⟨y, rfl⟩ := (toSpec p U).surjective y
    rw [hnat, hnat] at hxy
    rw [(B₀.homOfLE h).isOpenEmbedding.injective
      ((toSpec p V).isClosedEmbedding.injective hxy)]
  · intro x
    obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
    obtain ⟨f, hf, hxf⟩ := (haff V hV).exists_basicOpen_le (V := U) ⟨x.1, x.2⟩ (h x.2)
    obtain ⟨a, rfl⟩ := (hp V hV).1 f
    have h1 := hloc' U hU ((𝒜.map (homOfLE h).op).hom a) _ (by
      have := congr($(p.naturality (homOfLE h).op).hom a)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [this, Scheme.basicOpen_res]
      exact (inf_eq_right.mpr hf).symm) hf
    refine ⟨_, _, h1, ⟨toSpec p _ ⟨x.1, hxf⟩, ?_⟩, ?_⟩
    · rw [hnat]
      congr 1
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← Spec.map_comp, ← 𝒜.map_comp]
      exact hloc' V hV a _ rfl (hf.trans h)

end GlobalTheory.ThickGlue

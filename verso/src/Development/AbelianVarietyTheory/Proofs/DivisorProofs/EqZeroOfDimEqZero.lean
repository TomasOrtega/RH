import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Establish `hA` using `A.ab`. Establish `: IsProper A.X.hom` using `hA.proper`. Establish `hs : SmoothOfRelativeDimension 0 A.X.hom` using `h ▸ A.smooth`. Establish `: Etale A.X.hom` using `(Etale.iff_smoothOfRelativeDimension_zero _).2 hs`. Set `e : Sp K ⟶ A.X.left` to `(1 : 𝟙_ (Over (Sp K)) ⟶ A.X).left`.

Establish `he : e ≫ A.X.hom = 𝟙 _` using `Over.w (1 : 𝟙_ (Over (Sp K)) ⟶ A.X)`. Establish `: IsOpenImmersion e` using `isOpenImmersion_of_section_of_etale A.X.hom e he`. Establish `: IsClosedImmersion e`. Establish `: IsClosedImmersion (e ≫ A.X.hom)` using `by rw [he]; infer_instance`. Conclude with `IsClosedImmersion.of_comp e A.X.hom`.

Take `⟨hI, -, -⟩` from `isIntegral_isLocallyNoetherian_compactSpace K A`. Establish `: ConnectedSpace A.X.left` using `inferInstance`. Establish `hne : (Set.range e).Nonempty` using `⟨_, (default : PrimeSpectrum K), rfl⟩`. Establish `hsurj : Function.Surjective e` using `Set.range_eq_univ.1 (IsClopen.eq_univ ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩ hne)`. Establish `: Surjective e` using `⟨hsurj⟩`.

Establish `: IsIso e` using `IsOpenImmersion.isIso e`. Establish `: IsIso (e ≫ A.X.hom)` using `by rw [he]; infer_instance`. Conclude with `IsIso.of_isIso_comp_left e A.X.hom`.
-/
theorem isIso_hom_of_dim_eq_zero {K : Type} [Field K] (A : AbVar K) (h : A.dim = 0) : IsIso A.X.hom := by
  have hA := A.ab
  have : IsProper A.X.hom := hA.proper
  have hs : SmoothOfRelativeDimension 0 A.X.hom := h ▸ A.smooth
  have : Etale A.X.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hs
  let e : Sp K ⟶ A.X.left := (1 : 𝟙_ (Over (Sp K)) ⟶ A.X).left
  have he : e ≫ A.X.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over (Sp K)) ⟶ A.X)
  have : IsOpenImmersion e := isOpenImmersion_of_section_of_etale A.X.hom e he
  have : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ A.X.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.X.hom
  obtain ⟨hI, -, -⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  have : ConnectedSpace A.X.left := inferInstance
  have hne : (Set.range e).Nonempty := ⟨_, (default : PrimeSpectrum K), rfl⟩
  have hsurj : Function.Surjective e := Set.range_eq_univ.1
    (IsClopen.eq_univ ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩ hne)
  have : Surjective e := ⟨hsurj⟩
  have : IsIso e := IsOpenImmersion.isIso e
  have : IsIso (e ≫ A.X.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e A.X.hom

/- English proof (translation)
Use `ext`. Rewrite using `[← cancel_mono A.X.hom, Over.w, Over.w]`.
-/
theorem hom_eq_of_isIso {K : Type} [Field K] {A : AbVar K} (h : IsIso A.X.hom) {T : Over (Sp K)}
    (g₁ g₂ : T ⟶ A.X) : g₁ = g₂ := by
  ext
  rw [← cancel_mono A.X.hom, Over.w, Over.w]

/- English proof (translation)
Introduce `K _ A B h f`. Break down `h with h | h` into its components or cases. Establish `hi` using `isIso_hom_of_dim_eq_zero A h`. Use `hom_ext ?_` and prove the remaining obligations. Rewrite using `[zero_hom]`.

Establish `e1 : f.hom = (1 : A.X ⟶ A.X) ≫ f.hom`. Rewrite using `[hom_eq_of_isIso hi (1 : A.X ⟶ A.X) (𝟙 A.X), Category.id_comp]`. Rewrite using `[e1, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]`. Establish `hi` using `isIso_hom_of_dim_eq_zero B h`. Conclude with `hom_ext (hom_eq_of_isIso hi _ _)`.
-/
theorem eq_zero_of_dim_eq_zero :
    ∀ (K : Type) [Field K] (A B : AbVar K), (A.dim = 0 ∨ B.dim = 0) → ∀ f : A ⟶ B, f = 0 := by
  intro K _ A B h f
  rcases h with h | h
  · have hi := isIso_hom_of_dim_eq_zero A h
    refine hom_ext ?_
    rw [zero_hom]
    have e1 : f.hom = (1 : A.X ⟶ A.X) ≫ f.hom := by
      rw [hom_eq_of_isIso hi (1 : A.X ⟶ A.X) (𝟙 A.X), Category.id_comp]
    rw [e1, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  · have hi := isIso_hom_of_dim_eq_zero B h
    exact hom_ext (hom_eq_of_isIso hi _ _)

end GlobalTheory.AV.AbVar

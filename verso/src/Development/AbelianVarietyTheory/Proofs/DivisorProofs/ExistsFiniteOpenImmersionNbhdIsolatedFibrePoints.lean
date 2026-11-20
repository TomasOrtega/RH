import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompOpenImmersionOfQuasiFiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ZmtNbhd

/- English proof (translation)
Introduce `H X φ _ z O hzO hO`. Rewrite using `[Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← (φ.fiberHomeo (φ z)).isOpen_image]`. Simplify using `only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]`. Rewrite using `[isOpen_induced_iff]`. Use `⟨O, O.isOpen, ?_⟩` and prove the remaining obligations.

Use extensionality with `⟨w, hw⟩`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Subtype.ext (hO w h hw)`.

Introduce `h`. Establish `: w = z` using `congrArg Subtype.val h`. Conclude with `this ▸ hzO`.
-/
theorem quasiFiniteAt_of_isolated : ∀ (H X : Scheme.{0}) (φ : H ⟶ X), LocallyOfFiniteType φ →
    ∀ (z : H) (O : H.Opens), z ∈ O → (∀ w ∈ O, φ w = φ z → w = z) → φ.QuasiFiniteAt z := by
  intro H X φ _ z O hzO hO
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← (φ.fiberHomeo (φ z)).isOpen_image]
  simp only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
  rw [isOpen_induced_iff]
  refine ⟨O, O.isOpen, ?_⟩
  ext ⟨w, hw⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext (hO w h hw)
  · intro h
    have : w = z := congrArg Subtype.val h
    exact this ▸ hzO

/- English proof (translation)
Introduce `U T X j q _ _ _`. Use `⟨j.image, j.imageι ≫ q, j.toImage, inferInstance, inferInstance, by simp, inferInstance, ?_⟩` and prove the remaining obligations. Introduce `V`. Conclude with `TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (C := CommRingCat) (F := j.image.sheaf) j.toImage.c V (fun x _ => j.stalkFunctor_toImage_injective x)`.
-/
theorem exists_image_of_isOpenImmersion : ∀ (U T X : Scheme.{0}) (j : U ⟶ T) (q : T ⟶ X),
    IsOpenImmersion j → QuasiCompact j → IsFinite q →
    ∃ (X' : Scheme.{0}) (ν : X' ⟶ X) (i : U ⟶ X'), IsFinite ν ∧ IsOpenImmersion i ∧
      i ≫ ν = j ≫ q ∧ IsDominant i ∧ ∀ V : X'.Opens, Function.Injective (i.app V).hom := by
  intro U T X j q _ _ _
  refine ⟨j.image, j.imageι ≫ q, j.toImage, inferInstance, inferInstance, by simp, inferInstance, ?_⟩
  intro V
  exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (C := CommRingCat)
    (F := j.image.sheaf) j.toImage.c V (fun x _ => j.stalkFunctor_toImage_injective x)

/- English proof (translation)
Introduce `H X φ hX hsep hloft hqc Z hZ`. Set `H'` to `φ.quasiFiniteLocus`. Establish `hZH : Z ⊆ (H' : Set H)` using `fun z hz => by`. Take `⟨O, hzO, hO⟩` from `hZ z hz`. Conclude with `quasiFiniteAt_of_isolated H X φ hloft z O hzO hO`.

Establish `: IsLocallyNoetherian H` using `LocallyOfFiniteType.isLocallyNoetherian φ`. Establish `: QuasiCompact H'.ι` using `inferInstance`. Take `⟨T, q, j, hq, hj, hjq⟩` from `GlobalTheory.T.exists_finite_comp_openImmersion_of_quasiFinite H'.toScheme X (H'.ι ≫ φ) hX inferInstance inferInstance inferInstance inferInstance`. Establish `: QuasiCompact j`. Establish `: QuasiCompact (j ≫ q)` using `by rw [hjq]; infer_instance`.

Conclude with `QuasiCompact.of_comp j q`. Take `⟨X', ν, i, hν, hi, hiν, hdom, hinj⟩` from `exists_image_of_isOpenImmersion H'.toScheme T X j q hj this hq`. Conclude with `⟨H', X', ν, i, hZH, hν, hi, by rw [hiν, hjq], hdom, hinj⟩`.
-/
theorem exists_finite_openImmersion_nbhd : ∀ (H X : Scheme.{0}) (φ : H ⟶ X), IsNoetherian X → IsSeparated φ → LocallyOfFiniteType φ → QuasiCompact φ → ∀ Z : Set H, (∀ z ∈ Z, ∃ O : H.Opens, z ∈ O ∧ ∀ w ∈ O, φ w = φ z → w = z) → ∃ (H' : H.Opens) (X' : Scheme.{0}) (ν : X' ⟶ X) (i : H'.toScheme ⟶ X'), Z ⊆ H' ∧ IsFinite ν ∧ IsOpenImmersion i ∧ i ≫ ν = H'.ι ≫ φ ∧ IsDominant i ∧ ∀ V : X'.Opens, Function.Injective (i.app V).hom := by
  intro H X φ hX hsep hloft hqc Z hZ
  let H' := φ.quasiFiniteLocus
  have hZH : Z ⊆ (H' : Set H) := fun z hz => by
    obtain ⟨O, hzO, hO⟩ := hZ z hz
    exact quasiFiniteAt_of_isolated H X φ hloft z O hzO hO
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian φ
  have : QuasiCompact H'.ι := inferInstance
  obtain ⟨T, q, j, hq, hj, hjq⟩ := GlobalTheory.T.exists_finite_comp_openImmersion_of_quasiFinite H'.toScheme X (H'.ι ≫ φ) hX inferInstance
    inferInstance inferInstance inferInstance
  have : QuasiCompact j := by
    have : QuasiCompact (j ≫ q) := by rw [hjq]; infer_instance
    exact QuasiCompact.of_comp j q
  obtain ⟨X', ν, i, hν, hi, hiν, hdom, hinj⟩ := exists_image_of_isOpenImmersion H'.toScheme T X j q hj this hq
  exact ⟨H', X', ν, i, hZH, hν, hi, by rw [hiν, hjq], hdom, hinj⟩

end GlobalTheory.ZmtNbhd

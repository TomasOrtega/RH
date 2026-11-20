import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.GenericFibreGeom

/- English proof (translation)
Establish `hs : SurjectiveOnStalks j` using `inferInstance`. Use `(ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, j.stalkMap_surjective x⟩` and prove the remaining obligations. Establish `hl : IsLocalHom (j.stalkMap x).hom` using `inferInstance`. Establish `h` using `Flat.stalkMap j x`. Use `algebraize [(j.stalkMap x).hom]`.

Establish `: IsLocalHom (algebraMap (Y.presheaf.stalk (j x)) (X.presheaf.stalk x))` using `hl`. Use `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (j x)) (B := X.presheaf.stalk x)` as an intermediate fact. Conclude with `FaithfulSMul.algebraMap_injective _ _`.
-/
theorem isIso_stalkMap_of_flat_of_isPreimmersion {X Y : Scheme.{0}} (j : X ⟶ Y) [IsPreimmersion j]
    [Flat j] (x : X) : IsIso (j.stalkMap x) := by
  have hs : SurjectiveOnStalks j := inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, j.stalkMap_surjective x⟩
  have hl : IsLocalHom (j.stalkMap x).hom := inferInstance
  have h := Flat.stalkMap j x
  algebraize [(j.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (j x)) (X.presheaf.stalk x)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := Y.presheaf.stalk (j x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective _ _

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Conclude with `⟨fun hy => (hy.antisymm ((genericPoint_spec B).specializes (Set.mem_univ y))).eq, fun hy => hy ▸ specializes_rfl⟩`.
-/
theorem setOf_specializes_genericPoint (B : Scheme.{0}) [IsIntegral B] :
    {y : B | y ⤳ genericPoint B} = {genericPoint B} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun hy => (hy.antisymm ((genericPoint_spec B).specializes (Set.mem_univ y))).eq,
    fun hy => hy ▸ specializes_rfl⟩

/- English proof (translation)
Rewrite using `[← Scheme.Pullback.range_fst f g]`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨h.isoPullback.hom x, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩`.

Introduce and unpack `⟨z, rfl⟩`. Use `⟨h.isoPullback.inv z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]`.
-/
theorem range_of_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) : Set.range fst = f ⁻¹' Set.range g := by
  rw [← Scheme.Pullback.range_fst f g]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨h.isoPullback.hom x, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
  · rintro ⟨z, rfl⟩
    refine ⟨h.isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]

/- English proof (translation)
Introduce `B Y _ f G j s h`. Establish `hι : Flat (B.fromSpecStalk (genericPoint B))` using `GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk B _`. Establish `hj : IsPreimmersion j` using `MorphismProperty.of_isPullback (P := @IsPreimmersion) h.flip inferInstance`. Establish `hjf : Flat j` using `MorphismProperty.of_isPullback (P := @Flat) h.flip hι`. Establish `hr : Set.range j = f ⁻¹' {genericPoint B}`.

Rewrite using `[range_of_isPullback h, Scheme.range_fromSpecStalk, setOf_specializes_genericPoint]`. Establish `hiso : ∀ x : G, IsIso (j.stalkMap x)` using `fun x => isIso_stalkMap_of_flat_of_isPreimmersion j x`. Use `⟨hj, hr, hiso, ?_⟩` and prove the remaining obligations. Introduce `_ hne`. Take `⟨x₀⟩` from `hne`.

Establish `hfx : f (j x₀) = genericPoint B`. Establish `: j x₀ ∈ Set.range j` using `⟨x₀, rfl⟩`. Rewrite `this` using `[hr]`. Conclude with `this`. Establish `h1 : f (genericPoint Y) ⤳ genericPoint B`.

Rewrite using `[← hfx]`. Conclude with `((genericPoint_spec Y).specializes (Set.mem_univ _)).map f.continuous`. Establish `h2 : f (genericPoint Y) = genericPoint B` using `(h1.antisymm ((genericPoint_spec B).specializes (Set.mem_univ _))).eq`. Take `⟨ξ, hξ⟩ : genericPoint Y ∈ Set.range j` from `by rw [hr]; exact h2`. Establish `hemb` using `IsPreimmersion.isEmbedding j`.

Establish `hgen : IsGenericPoint ξ (⊤ : Set G)`. Rewrite using `[isGenericPoint_iff_specializes]`. Introduce `x`. Simplify using `only [Set.top_eq_univ, Set.mem_univ, iff_true]`. Rewrite using `[← hemb.isInducing.specializes_iff, hξ]`.

Conclude with `(genericPoint_spec Y).specializes (Set.mem_univ _)`. Establish `hirr : IrreducibleSpace G` using `(irreducibleSpace_def G).2 hgen.isIrreducible`. Establish `hred : ∀ x : G, _root_.IsReduced (G.presheaf.stalk x)` using `fun x => by`. Use `hiso x` as an intermediate fact. Conclude with `isReduced_of_injective (inv (j.stalkMap x)).hom (ConcreteCategory.bijective_of_isIso (inv (j.stalkMap x))).1`.

Establish `: AlgebraicGeometry.IsReduced G` using `isReduced_of_isReduced_stalk G`. Establish `hint : IsIntegral G` using `isIntegral_of_irreducibleSpace_of_isReduced G`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Rewrite using `[← hξ]`. Use `congr 1`.

Conclude with `(genericPoint_spec G).eq hgen`.
-/
theorem genericFibre_props : ∀ (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsPreimmersion j ∧ Set.range j = f ⁻¹' {genericPoint B} ∧ (∀ x : G, IsIso (j.stalkMap x)) ∧ ∀ [IsIntegral Y], Nonempty G → ∃ _ : IsIntegral G, j (genericPoint G) = genericPoint Y := by
  intro B Y _ f G j s h
  have hι : Flat (B.fromSpecStalk (genericPoint B)) :=
    GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk B _
  have hj : IsPreimmersion j :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) h.flip inferInstance
  have hjf : Flat j := MorphismProperty.of_isPullback (P := @Flat) h.flip hι
  have hr : Set.range j = f ⁻¹' {genericPoint B} := by
    rw [range_of_isPullback h, Scheme.range_fromSpecStalk, setOf_specializes_genericPoint]
  have hiso : ∀ x : G, IsIso (j.stalkMap x) := fun x => isIso_stalkMap_of_flat_of_isPreimmersion j x
  refine ⟨hj, hr, hiso, ?_⟩
  intro _ hne
  obtain ⟨x₀⟩ := hne

  have hfx : f (j x₀) = genericPoint B := by
    have : j x₀ ∈ Set.range j := ⟨x₀, rfl⟩
    rw [hr] at this
    exact this
  have h1 : f (genericPoint Y) ⤳ genericPoint B := by
    rw [← hfx]
    exact ((genericPoint_spec Y).specializes (Set.mem_univ _)).map f.continuous
  have h2 : f (genericPoint Y) = genericPoint B :=
    (h1.antisymm ((genericPoint_spec B).specializes (Set.mem_univ _))).eq
  obtain ⟨ξ, hξ⟩ : genericPoint Y ∈ Set.range j := by rw [hr]; exact h2
  have hemb := IsPreimmersion.isEmbedding j
  have hgen : IsGenericPoint ξ (⊤ : Set G) := by
    rw [isGenericPoint_iff_specializes]
    intro x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    rw [← hemb.isInducing.specializes_iff, hξ]
    exact (genericPoint_spec Y).specializes (Set.mem_univ _)
  have hirr : IrreducibleSpace G := (irreducibleSpace_def G).2 hgen.isIrreducible
  have hred : ∀ x : G, _root_.IsReduced (G.presheaf.stalk x) := fun x => by
    have := hiso x
    exact isReduced_of_injective (inv (j.stalkMap x)).hom
      (ConcreteCategory.bijective_of_isIso (inv (j.stalkMap x))).1
  have : AlgebraicGeometry.IsReduced G := isReduced_of_isReduced_stalk G
  have hint : IsIntegral G := isIntegral_of_irreducibleSpace_of_isReduced G
  refine ⟨hint, ?_⟩
  rw [← hξ]
  congr 1
  exact (genericPoint_spec G).eq hgen

end GlobalTheory.GenericFibreGeom

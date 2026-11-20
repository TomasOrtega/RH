import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

universe u

private def affineOpensLePreimageCover {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι : Type u}
    (U : ι → X.Opens) : Set X'.Opens :=
  {W : X'.Opens | IsAffineOpen W ∧ ∃ i, W ≤ φ ⁻¹ᵁ (U i)}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_affineOpensLePreimageCover {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι : Type u}
    (U : ι → X.Opens) {W : X'.Opens} :
    W ∈ affineOpensLePreimageCover φ U ↔ IsAffineOpen W ∧ ∃ i, W ≤ φ ⁻¹ᵁ (U i) :=
  Iff.rfl

/- English proof (translation)
Establish `hSmem : ∀ W : affineOpensLePreimageCover φ U, IsAffineOpen (W : X'.Opens) ∧ ∃ i, (W : X'.Opens) ≤ φ ⁻¹ᵁ (U i)` using `fun W => (mem_affineOpensLePreimageCover φ U).mp W.2`. Establish `hcov : ∀ x : X', ∃ W : affineOpensLePreimageCover φ U, x ∈ ((W : X'.Opens) : Set X')`. Introduce `x`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x ∈ (φ ⁻¹ᵁ (U i) : X'.Opens) := by`. Establish `hx : φ.base x ∈ (⊤ : X.Opens)` using `by simp`.

Rewrite `hx` using `[← hU]`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hx`. Conclude with `⟨i, hi⟩`. Take `⟨W, hW, hxW, hWle⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X') hi`. Establish `hW' : IsAffineOpen W` using `hW`.

Conclude with `⟨⟨W, (mem_affineOpensLePreimageCover φ U).mpr ⟨hW', i, hWle⟩⟩, hxW⟩`. Establish `hcomp : IsCompact (Set.univ : Set X')` using `isCompact_univ`. Take `⟨t, ht⟩` from `hcomp.elim_finite_subcover (fun W : affineOpensLePreimageCover φ U => ((W : X'.Opens) : Set X')) (fun W => (W : X'.Opens).isOpen) (fun x _ => Set.mem_iUnion.mpr (hcov x))`. Use `⟨{W : affineOpensLePreimageCover φ U // W ∈ t}, inferInstance, fun a => (a.1 : X'.Opens), fun a => (hSmem a.1).2.choose, fun a => (hSmem a.1).1, fun a => (hSmem a.1).2.choose_spec, ?_⟩` and prove the remaining obligations. Use `SetLike.coe_injective ?_` and prove the remaining obligations.

Rewrite using `[TopologicalSpace.Opens.coe_top]`. Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Establish `hx` using `ht (Set.mem_univ x)`. Simplify using `only [Set.mem_iUnion, exists_prop] at hx`. Take `⟨W, hWt, hxW⟩` from `hx`.

Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hWt⟩, hxW⟩`.
-/
theorem exists_finite_affine_cover_subordinate {X' X : Scheme.{u}} [CompactSpace X']
    (φ : X' ⟶ X) {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    ∃ (κ : Type u) (_ : Finite κ) (V : κ → X'.Opens) (β : κ → ι),
      (∀ a, IsAffineOpen (V a)) ∧ (∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) ∧ iSup V = ⊤ := by
  classical
  have hSmem : ∀ W : affineOpensLePreimageCover φ U,
      IsAffineOpen (W : X'.Opens) ∧ ∃ i, (W : X'.Opens) ≤ φ ⁻¹ᵁ (U i) :=
    fun W => (mem_affineOpensLePreimageCover φ U).mp W.2
  have hcov : ∀ x : X', ∃ W : affineOpensLePreimageCover φ U, x ∈ ((W : X'.Opens) : Set X') := by
    intro x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ (φ ⁻¹ᵁ (U i) : X'.Opens) := by
      have hx : φ.base x ∈ (⊤ : X.Opens) := by simp
      rw [← hU] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨i, hi⟩
    obtain ⟨W, hW, hxW, hWle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X') hi
    have hW' : IsAffineOpen W := hW
    exact ⟨⟨W, (mem_affineOpensLePreimageCover φ U).mpr ⟨hW', i, hWle⟩⟩, hxW⟩
  have hcomp : IsCompact (Set.univ : Set X') := isCompact_univ
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover
      (fun W : affineOpensLePreimageCover φ U => ((W : X'.Opens) : Set X'))
      (fun W => (W : X'.Opens).isOpen) (fun x _ => Set.mem_iUnion.mpr (hcov x))
  refine ⟨{W : affineOpensLePreimageCover φ U // W ∈ t}, inferInstance, fun a => (a.1 : X'.Opens),
    fun a => (hSmem a.1).2.choose, fun a => (hSmem a.1).1,
    fun a => (hSmem a.1).2.choose_spec, ?_⟩
  refine SetLike.coe_injective ?_
  rw [TopologicalSpace.Opens.coe_top]
  refine Set.eq_univ_of_forall fun x => ?_
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨W, hWt, hxW⟩ := hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hWt⟩, hxW⟩

noncomputable def opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    sigmaOpens X' V ⟶ sigmaOpens X U :=
  Sigma.desc fun a =>
    φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a)

@[simp]
/- English proof (translation)
Simplify using `[opensCoprodMapOfRefinement]`.
-/
theorem sigmaι_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) (a : κ) :
    Sigma.ι (fun a => (V a).toScheme) a ≫ opensCoprodMapOfRefinement φ U V β hβ =
      φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a) := by
  simp [opensCoprodMapOfRefinement]

/- English proof (translation)
Use `Limits.Sigma.hom_ext _ _ fun a => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, sigmaι_opensCoprodMapOfRefinement, Category.assoc, sigma_ι_sigmaOpensDesc, sigma_ι_sigmaOpensDesc_assoc]`. Simplify using the standard rewrite rules.
-/
theorem opensCoprodMapOfRefinement_comp_sigmaOpensDesc {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    opensCoprodMapOfRefinement φ U V β hβ ≫ sigmaOpensDesc X U = sigmaOpensDesc X' V ≫ φ := by
  refine Limits.Sigma.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, sigmaι_opensCoprodMapOfRefinement, Category.assoc, sigma_ι_sigmaOpensDesc,
    sigma_ι_sigmaOpensDesc_assoc]
  simp

/- English proof (translation)
Rewrite using `[← cancel_mono U.ι]`. Simplify using the standard rewrite rules.
-/
private theorem resLE_eq_homOfLE_comp_restrict {X' X : Scheme.{u}} (φ : X' ⟶ X)
    (U : X.Opens) (V : X'.Opens) (e : V ≤ φ ⁻¹ᵁ U) :
    φ.resLE U V e = X'.homOfLE e ≫ φ ∣_ U := by
  rw [← cancel_mono U.ι]
  simp

/- English proof (translation)
Rewrite using `[resLE_eq_homOfLE_comp_restrict]`. Use `infer_instance`.
-/
private theorem smooth_resLE {X' X : Scheme.{u}} (φ : X' ⟶ X) [Smooth φ]
    (U : X.Opens) (V : X'.Opens) (e : V ≤ φ ⁻¹ᵁ U) :
    Smooth (φ.resLE U V e) := by
  rw [resLE_eq_homOfLE_comp_restrict]
  infer_instance

/- English proof (translation)
Use `show Smooth (Sigma.desc fun a => φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a))`. Use `smooth_sigmaDesc _ fun a => ?_` and prove the remaining obligations. Use `smooth_resLE φ (U (β a)) (V a) (hβ a)` as an intermediate fact. Use `infer_instance`.
-/
theorem smooth_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) [Smooth φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    Smooth (opensCoprodMapOfRefinement φ U V β hβ) := by
  show Smooth (Sigma.desc fun a => φ.resLE (U (β a)) (V a) (hβ a) ≫
      Sigma.ι (fun i => (U i).toScheme) (β a))
  refine smooth_sigmaDesc _ fun a => ?_
  have := smooth_resLE φ (U (β a)) (V a) (hβ a)
  infer_instance

instance instSmoothOpensCoprodRefine {X' X : Scheme.{u}} (φ : X' ⟶ X) [Smooth φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    Smooth (opensCoprodMapOfRefinement φ U V β hβ) :=
  smooth_opensCoprodMapOfRefinement φ U V β hβ

/- English proof (translation)
Establish `h1 : LocallyOfFiniteType (sigmaOpensDesc X' V ≫ φ)` using `inferInstance`. Establish `h2 : LocallyOfFiniteType (opensCoprodMapOfRefinement φ U V β hβ ≫ sigmaOpensDesc X U)`. Rewrite using `[opensCoprodMapOfRefinement_comp_sigmaOpensDesc]`. Conclude with `h1`. Conclude with `locallyOfFiniteType_of_comp _ (sigmaOpensDesc X U)`.
-/
theorem locallyOfFiniteType_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X)
    [LocallyOfFiniteType φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    LocallyOfFiniteType (opensCoprodMapOfRefinement φ U V β hβ) := by
  have h1 : LocallyOfFiniteType (sigmaOpensDesc X' V ≫ φ) := inferInstance
  have h2 : LocallyOfFiniteType (opensCoprodMapOfRefinement φ U V β hβ ≫ sigmaOpensDesc X U) := by
    rw [opensCoprodMapOfRefinement_comp_sigmaOpensDesc]
    exact h1
  exact locallyOfFiniteType_of_comp _ (sigmaOpensDesc X U)

instance instLocallyOfFiniteTypeOpensCoprodRefine {X' X : Scheme.{u}} (φ : X' ⟶ X)
    [LocallyOfFiniteType φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    LocallyOfFiniteType (opensCoprodMapOfRefinement φ U V β hβ) :=
  locallyOfFiniteType_opensCoprodMapOfRefinement φ U V β hβ

end FunctorialResolution.EmbeddedResolution

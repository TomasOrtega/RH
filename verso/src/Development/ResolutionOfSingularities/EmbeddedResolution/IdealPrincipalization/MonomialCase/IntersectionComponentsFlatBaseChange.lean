import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IrreducibleComponentsFlatPreimage
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Pullback of ideal sheaves is left adjoint to the corresponding map on ideals and therefore preserves suprema. The finite sum is such a supremum, so it pulls back to the sum of the pulled-back terms.
-/
private theorem comap_biSup_finset_fin {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ}
    (s : Finset (Fin n)) (F : Fin n → Y.IdealSheafData) :
    (⨆ i ∈ s, F i).comap f = ⨆ i ∈ s, (F i).comap f :=
  (Scheme.IdealSheafData.map_gc f).l_iSup₂

/- English proof (authored)
The pulled-back boundary is obtained by applying pullback to each entry of the original list. The corresponding index has the same numeric position, so its entry is the pullback of the old entry.
-/
private theorem pullbackOverField_boundary_get (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (j : Fin T.boundary.length) :
    (T.pullbackOverField Y k' q g).boundary.get (pullbackOverFieldIndex T Y k' q g j)
      = (T.boundary.get j).comap g := by
  have h : (T.pullbackOverField Y k' q g).boundary.get (pullbackOverFieldIndex T Y k' q g j)
      = (T.boundary.map fun D => D.comap g).get
          (Fin.cast (MarkedIdealWithBoundary.pullbackOverField_boundary_length T Y k' q g).symm j) := rfl
  rw [h]
  simp only [List.get_eq_getElem, List.getElem_map]
  rfl

/- English proof (authored)
Both intersection ideals are sums over their selected boundary positions. Pullback preserves this sum. Every new selected index is the image of an old selected index and carries the pullback of that old ideal. Conversely, each old selected index contributes its corresponding new entry. Thus the sums agree.
-/
theorem intersectionIdeal_pullbackOverField (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (J : Finset (Fin T.boundary.length)) :
    intersectionIdeal (T.pullbackOverField Y k' q g).boundary (J.image (pullbackOverFieldIndex T Y k' q g)) =
      (intersectionIdeal T.boundary J).comap g := by
  rw [intersectionIdeal_eq_iSup, intersectionIdeal_eq_iSup, comap_biSup_finset_fin]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun j' => iSup_le fun hj' => ?_
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
    rw [pullbackOverField_boundary_get]
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
  · refine iSup_le fun j => iSup_le fun hj => ?_
    rw [← pullbackOverField_boundary_get T Y k' q g j]
    exact le_iSup_of_le (pullbackOverFieldIndex T Y k' q g j)
      (le_iSup_of_le (Finset.mem_image_of_mem _ hj) le_rfl)

/- English proof (authored)
The ideal of the pulled-back intersection is the pullback of the original intersection ideal. The support of a pulled-back ideal is the set-theoretic inverse image of the original support.
-/
theorem support_intersectionIdeal_pullbackOverField (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (J : Finset (Fin T.boundary.length)) :
    (↑(intersectionIdeal (T.pullbackOverField Y k' q g).boundary
          (J.image (pullbackOverFieldIndex T Y k' q g))).support :
        Set ↥(T.pullbackOverField Y k' q g).scheme) =
      ⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) := by
  have h : intersectionIdeal (T.pullbackOverField Y k' q g).boundary (J.image (pullbackOverFieldIndex T Y k' q g))
      = (intersectionIdeal T.boundary J).comap g := intersectionIdeal_pullbackOverField T Y k' q g J
  have h2 : (↑((intersectionIdeal T.boundary J).comap g).support : Set ↥Y)
      = ⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    support_comap g (intersectionIdeal T.boundary J)
  rw [h]
  exact h2

/- English proof (authored)
A member of the intersection-component family is a maximal irreducible subset of the support of the intersection ideal. For the new boundary this support is the inverse image of the old intersection support, giving the equivalence.
-/
theorem mem_intersectionComponents_pullbackOverField_iff (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (J : Finset (Fin T.boundary.length)) (C' : Set ↥Y) :
    C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary (J.image (pullbackOverFieldIndex T Y k' q g)) ↔
      IsIrreducibleComponentOf C' (⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme)) := by
  have h1 := mem_intersectionComponents_iff (T.pullbackOverField Y k' q g).boundary
      (J.image (pullbackOverFieldIndex T Y k' q g)) C'
  rw [support_intersectionIdeal_pullbackOverField T Y k' q g J] at h1
  exact h1

/- English proof (authored)
The closure of the component is irreducible and stays in the given closed set. Maximality therefore makes the closure equal to the component. An irreducible closed subset of a scheme has a generic point.
-/
theorem IsIrreducibleComponentOf.exists_isGenericPoint {Y : Scheme.{u}} {C S : Set ↥Y}
    (h : IsIrreducibleComponentOf C S) (hS : IsClosed S) :
    ∃ ξ : ↥Y, IsGenericPoint ξ C := by
  obtain ⟨hirr, hsub, hmax⟩ := h
  have hcl : closure C = C :=
    hmax (closure C) hirr.closure subset_closure (hS.closure_subset_iff.mpr hsub)
  have hCclosed : IsClosed C := closure_eq_iff_isClosed.mp hcl
  exact QuasiSober.sober hirr hCclosed

/- English proof (authored)
Suppose two opens meet the union. Choose a point of each intersection and a member of the chain containing that point. The larger of the two members contains both points, so each open meets it. Preirreducibility of that member gives a point of the intersection of the opens in the union.
-/
private theorem isPreirreducible_sUnion_of_isChain {α : Type u} [TopologicalSpace α]
    (c : Set (Set α)) (hcc : IsChain (· ⊆ ·) c)
    (hirr : ∀ t ∈ c, IsPreirreducible t) : IsPreirreducible (⋃₀ c) := by
  intro u v hu hv hxne hyne
  obtain ⟨x, hxU, hxu⟩ := hxne
  obtain ⟨y, hyU, hyv⟩ := hyne
  obtain ⟨t₁, ht₁c, hxt₁⟩ := Set.mem_sUnion.mp hxU
  obtain ⟨t₂, ht₂c, hyt₂⟩ := Set.mem_sUnion.mp hyU
  rcases eq_or_ne t₁ t₂ with rfl | hne
  · obtain ⟨z, hzt, hzuv⟩ := hirr t₁ ht₁c u v hu hv ⟨x, hxt₁, hxu⟩ ⟨y, hyt₂, hyv⟩
    exact ⟨z, Set.mem_sUnion.mpr ⟨t₁, ht₁c, hzt⟩, hzuv⟩
  · rcases hcc ht₁c ht₂c hne with h | h
    · obtain ⟨z, hzt, hzuv⟩ := hirr t₂ ht₂c u v hu hv ⟨x, h hxt₁, hxu⟩ ⟨y, hyt₂, hyv⟩
      exact ⟨z, Set.mem_sUnion.mpr ⟨t₂, ht₂c, hzt⟩, hzuv⟩
    · obtain ⟨z, hzt, hzuv⟩ := hirr t₁ ht₁c u v hu hv ⟨x, hxt₁, hxu⟩ ⟨y, h hyt₂, hyv⟩
      exact ⟨z, Set.mem_sUnion.mpr ⟨t₁, ht₁c, hzt⟩, hzuv⟩

/- English proof (authored)
Order the irreducible subsets of the specified set by inclusion, starting with the given irreducible subset. A nonempty chain has an upper bound given by its union. The union is nonempty, stays in the set, and is preirreducible by the chain property. The supplied initial subset handles the empty chain. Zorn's lemma gives a maximal irreducible set containing the initial one, which is a component.
-/
theorem exists_isIrreducibleComponentOf {Y : Scheme.{u}} (S A : Set ↥Y) (hA : IsIrreducible A)
    (hAS : A ⊆ S) :
    ∃ C : Set ↥Y, IsIrreducibleComponentOf C S ∧ A ⊆ C := by
  have hchain : ∀ c ⊆ {C : Set ↥Y | IsIrreducible C ∧ C ⊆ S}, IsChain (· ⊆ ·) c →
      c.Nonempty → ∃ ub ∈ {C : Set ↥Y | IsIrreducible C ∧ C ⊆ S}, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hcc hcn
    obtain ⟨t, htc⟩ := hcn
    have hne : (⋃₀ c).Nonempty := by
      obtain ⟨x, hx⟩ := (hcS htc).1.1
      exact ⟨x, Set.mem_sUnion.mpr ⟨t, htc, hx⟩⟩
    refine ⟨⋃₀ c, ⟨⟨hne, isPreirreducible_sUnion_of_isChain c hcc
        fun s hs => (hcS hs).1.2⟩, Set.sUnion_subset fun s hs => (hcS hs).2⟩,
      fun s hs => Set.subset_sUnion_of_mem hs⟩
  obtain ⟨C, hAC, hmax⟩ :=
    zorn_subset_nonempty {C : Set ↥Y | IsIrreducible C ∧ C ⊆ S} hchain A ⟨hA, hAS⟩
  have hmem : IsIrreducible C ∧ C ⊆ S := hmax.1
  refine ⟨C, ⟨hmem.1, hmem.2, ?_⟩, hAC⟩
  intro C' hC' hCle hC'S
  exact subset_antisymm (hmax.2 ⟨hC', hC'S⟩ hCle) hCle

/- English proof (authored)
Take the closure of the image of the upper generic point. It is irreducible, lies in the closed target set, and contains the image of the upper component by continuity. Suppose it is contained in a larger irreducible subset of the target set. A generic point of the larger subset's closure generalizes the image of the upper generic point. Lift this generalization upstairs using the generalizing property. Its closure lies in the inverse image of the target set and contains the upper component, so it equals that component by maximality. The image of the lift then belongs to the original image closure. Thus the larger subset is contained in that closure, proving maximality downstairs.
-/
theorem IsIrreducibleComponentOf.closure_image_genericPoint {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : GeneralizingMap (fun y : ↥Y => g y)) {S : Set ↥X} (hS : IsClosed S) {C' : Set ↥Y}
    (hC' : IsIrreducibleComponentOf C' (⇑g ⁻¹' S)) {ξ' : ↥Y} (hξ' : IsGenericPoint ξ' C') :
    IsIrreducibleComponentOf (closure {g ξ'}) S ∧ Set.MapsTo (⇑g) C' (closure {g ξ'}) := by
  have hC'unf : IsIrreducible C' ∧ C' ⊆ ⇑g ⁻¹' S ∧
      ∀ D : Set ↥Y, IsIrreducible D → C' ⊆ D → D ⊆ ⇑g ⁻¹' S → D = C' := hC'
  obtain ⟨-, hsub, hmax⟩ := hC'unf
  have hξ'eq : closure ({ξ'} : Set ↥Y) = C' := hξ'
  have hcont : Continuous (fun y : ↥Y => g y) := g.continuous
  have himg : ∀ z w : ↥Y, z ∈ closure ({w} : Set ↥Y) → g z ∈ closure ({g w} : Set ↥X) := by
    intro z w hz
    have h2 : (fun y : ↥Y => g y) '' closure ({w} : Set ↥Y)
        ⊆ closure ((fun y : ↥Y => g y) '' ({w} : Set ↥Y)) :=
      image_closure_subset_closure_image hcont
    have h3 : g z ∈ closure ((fun y : ↥Y => g y) '' ({w} : Set ↥Y)) := h2 ⟨z, hz, rfl⟩
    rwa [Set.image_singleton] at h3
  have hξ'mem : ξ' ∈ C' := by
    rw [← hξ'eq]
    exact subset_closure rfl
  have hgS : g ξ' ∈ S := hsub hξ'mem
  have hDsub : closure ({g ξ'} : Set ↥X) ⊆ S :=
    hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hgS)
  have hDirr : IsIrreducible (closure ({g ξ'} : Set ↥X)) := isIrreducible_singleton.closure
  have hmaps : Set.MapsTo (⇑g) C' (closure ({g ξ'} : Set ↥X)) := by
    intro y hy
    refine himg y ξ' ?_
    rw [hξ'eq]
    exact hy
  have hirred : IsIrreducible (closure ({g ξ'} : Set ↥X)) ∧
      closure ({g ξ'} : Set ↥X) ⊆ S ∧
      ∀ E : Set ↥X, IsIrreducible E → closure ({g ξ'} : Set ↥X) ⊆ E → E ⊆ S →
        E = closure ({g ξ'} : Set ↥X) := by
    refine ⟨hDirr, hDsub, ?_⟩
    intro E hE hsubE hES
    obtain ⟨η, hη⟩ := QuasiSober.sober hE.closure (isClosed_closure (s := E))
    have hηeq : closure ({η} : Set ↥X) = closure E := hη
    have hgξ'E : g ξ' ∈ E := hsubE (subset_closure rfl)
    have hspec0 : (η : ↥X) ⤳ g ξ' := by
      refine specializes_iff_mem_closure.mpr ?_
      rw [hηeq]
      exact subset_closure hgξ'E
    obtain ⟨ξ'', hspec, hgη⟩ := hg hspec0
    have hgη' : g ξ'' = η := hgη
    have hspec' : ξ' ∈ closure ({ξ''} : Set ↥Y) := specializes_iff_mem_closure.mp hspec
    have hclE : closure E ⊆ S := hS.closure_subset_iff.mpr hES
    have hsub2 : closure ({ξ''} : Set ↥Y) ⊆ ⇑g ⁻¹' S := by
      intro z hz
      have h3 : g z ∈ closure ({g ξ''} : Set ↥X) := himg z ξ'' hz
      rw [hgη', hηeq] at h3
      exact hclE h3
    have hsub3 : C' ⊆ closure ({ξ''} : Set ↥Y) := by
      rw [← hξ'eq]
      exact closure_minimal (Set.singleton_subset_iff.mpr hspec') isClosed_closure
    have heq : closure ({ξ''} : Set ↥Y) = C' :=
      hmax (closure ({ξ''} : Set ↥Y)) isIrreducible_singleton.closure hsub3 hsub2
    have hξ''mem : ξ'' ∈ C' := by
      rw [← heq]
      exact subset_closure rfl
    have hηmem : η ∈ closure ({g ξ'} : Set ↥X) := by
      have h4 := hmaps hξ''mem
      rwa [hgη'] at h4
    have hZsub : closure E ⊆ closure ({g ξ'} : Set ↥X) := by
      rw [← hηeq]
      exact closure_minimal (Set.singleton_subset_iff.mpr hηmem) isClosed_closure
    exact Set.Subset.antisymm (Set.Subset.trans subset_closure hZsub) hsubE
  exact ⟨hirred, hmaps⟩

/- English proof (authored)
Choose the generic point of the given downstairs component. It generalizes the image of the specified upper point, so lift it to a generalization of that upper point. The closure of the lift lies in the preimage of the closed set. Choose a component containing this closure and thus the specified point. The image closure of a generic point of the chosen upper component is a downstairs component and contains the original downstairs generic point, since the lift lies in the upper component. By maximality it equals the given downstairs component. The upper component maps into it and its generic point maps to the downstairs generic point by uniqueness.
-/
theorem exists_isIrreducibleComponentOf_preimage {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : GeneralizingMap (fun y : ↥Y => g y)) {S : Set ↥X} (hS : IsClosed S) {C : Set ↥X}
    (hC : IsIrreducibleComponentOf C S) (y : ↥Y) (hy : g y ∈ C) :
    ∃ C' : Set ↥Y, IsIrreducibleComponentOf C' (⇑g ⁻¹' S) ∧ y ∈ C' ∧ Set.MapsTo (⇑g) C' C ∧
      ∀ (ξ' : ↥Y) (ξ : ↥X), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ := by
  classical
  have hcont : Continuous (⇑g : ↥Y → ↥X) := g.continuous
  have hSY : IsClosed (⇑g ⁻¹' S) := IsClosed.preimage hcont hS
  obtain ⟨ξ, hξ⟩ := IsIrreducibleComponentOf.exists_isGenericPoint hC hS
  have hξeq : closure ({ξ} : Set ↥X) = C := hξ
  obtain ⟨-, hCS, hCmax⟩ := hC
  have hmemC : g y ∈ closure ({ξ} : Set ↥X) := by
    rw [hξeq]; exact hy
  have hspec : ξ ⤳ g y := specializes_iff_mem_closure.mpr hmemC
  obtain ⟨y₀, hy₀spec, hy₀eq⟩ := hg hspec
  have hgy₀ : g y₀ = ξ := hy₀eq
  have hymem : y ∈ closure ({y₀} : Set ↥Y) := specializes_iff_mem_closure.mp hy₀spec
  have hξC : ξ ∈ C := by
    have h0 : ξ ∈ ({ξ} : Set ↥X) := Set.mem_singleton_iff.mpr rfl
    have h1 := subset_closure h0
    rwa [hξeq] at h1
  have hy₀S : y₀ ∈ ⇑g ⁻¹' S := by
    have h2 : g y₀ ∈ S := by rw [hgy₀]; exact hCS hξC
    exact h2
  have hsub : closure ({y₀} : Set ↥Y) ⊆ ⇑g ⁻¹' S :=
    closure_minimal (Set.singleton_subset_iff.mpr hy₀S) hSY
  obtain ⟨C', hC', hAC'⟩ :=
    exists_isIrreducibleComponentOf (⇑g ⁻¹' S) (closure ({y₀} : Set ↥Y))
      (IsIrreducible.closure isIrreducible_singleton) hsub
  have hy₀C' : y₀ ∈ C' := by
    have h3 : y₀ ∈ ({y₀} : Set ↥Y) := Set.mem_singleton_iff.mpr rfl
    exact hAC' (subset_closure h3)
  have key : ∀ ζ : ↥Y, IsGenericPoint ζ C' → closure ({g ζ} : Set ↥X) = C := by
    intro ζ hζ
    obtain ⟨hcomp, -⟩ := IsIrreducibleComponentOf.closure_image_genericPoint g hg hS hC' hζ
    obtain ⟨hirr2, hsub2, -⟩ := hcomp
    have hζeq : closure ({ζ} : Set ↥Y) = C' := hζ
    have h4 : y₀ ∈ closure ({ζ} : Set ↥Y) := by rw [hζeq]; exact hy₀C'
    have h6 := image_closure_subset_closure_image hcont (Set.mem_image_of_mem (⇑g) h4)
    rw [Set.image_singleton] at h6
    rw [hgy₀] at h6
    have hCsub : C ⊆ closure ({g ζ} : Set ↥X) := by
      rw [← hξeq]
      exact closure_minimal (Set.singleton_subset_iff.mpr h6) isClosed_closure
    exact hCmax (closure ({g ζ} : Set ↥X)) hirr2 hCsub hsub2
  obtain ⟨ζ₀, hζ₀⟩ := IsIrreducibleComponentOf.exists_isGenericPoint hC' hSY
  have hmapsC : Set.MapsTo (⇑g) C' C := by
    have h7 := (IsIrreducibleComponentOf.closure_image_genericPoint g hg hS hC' hζ₀).2
    rwa [key ζ₀ hζ₀] at h7
  refine ⟨C', hC', hAC' hymem, hmapsC, ?_⟩
  intro ζ ξ₂ hgen1 hgen2
  have h8 : closure ({g ζ} : Set ↥X) = C := key ζ hgen1
  have h9 : closure ({ξ₂} : Set ↥X) = C := hgen2
  have hm1 : g ζ ∈ closure ({ξ₂} : Set ↥X) := by
    rw [h9, ← h8]
    exact subset_closure (Set.mem_singleton_iff.mpr rfl)
  have hm2 : ξ₂ ∈ closure ({g ζ} : Set ↥X) := by
    rw [h8, ← h9]
    exact subset_closure (Set.mem_singleton_iff.mpr rfl)
  exact ((specializes_iff_mem_closure.mpr hm2).antisymm
    (specializes_iff_mem_closure.mpr hm1)).eq

/- English proof (authored)
The closed subscheme defined by the pulled-back ideal is canonically isomorphic to the scheme pullback of the original inclusion. Its map to the original subscheme is the isomorphism followed by the corresponding pullback projection. The other projection is the inclusion of the new subscheme. These are the arrows of the pullback square.
-/
private theorem exists_isPullback_comapSubscheme {X Y : Scheme.{u}} (W : X.IdealSheafData)
    (g : Y ⟶ X) :
    ∃ c : (W.comap g).subscheme ⟶ W.subscheme,
      IsPullback c (W.comap g).subschemeι W.subschemeι g := by
  obtain ⟨e, he⟩ : ∃ e : (W.comap g).subscheme ≅ Limits.pullback g W.subschemeι,
      e.hom ≫ Limits.pullback.fst g W.subschemeι = (W.comap g).subschemeι :=
    ⟨W.comapIso g, W.comapIso_hom_fst g⟩
  refine ⟨e.hom ≫ Limits.pullback.snd g W.subschemeι, ?_⟩
  have hsq : (W.comap g).subschemeι ≫ g
      = (e.hom ≫ Limits.pullback.snd g W.subschemeι) ≫ W.subschemeι := by
    rw [← he]
    simp only [Category.assoc, Limits.pullback.condition]
  exact (IsPullback.of_iso_pullback ⟨hsq⟩ e he rfl).flip

def comapSubschemeHom {X Y : Scheme.{u}} (W : X.IdealSheafData) (g : Y ⟶ X) :
    (W.comap g).subscheme ⟶ W.subscheme :=
  (exists_isPullback_comapSubscheme W g).choose

/- English proof (authored)
The comparison morphism is chosen from the existence of a map that makes the square of closed subschemes a pullback. It therefore has the required pullback property.
-/
theorem isPullback_comapSubschemeHom {X Y : Scheme.{u}} (W : X.IdealSheafData) (g : Y ⟶ X) :
    IsPullback (comapSubschemeHom W g) (W.comap g).subschemeι W.subschemeι g :=
  (exists_isPullback_comapSubscheme W g).choose_spec

/- English proof (authored)
The square of the two closed subschemes over the ambient morphism is a pullback and therefore commutes. The two routes to the original ambient scheme are the stated composites.
-/
theorem comapSubschemeHom_comp_subschemeι {X Y : Scheme.{u}} (W : X.IdealSheafData) (g : Y ⟶ X) :
    comapSubschemeHom W g ≫ W.subschemeι = (W.comap g).subschemeι ≫ g :=
  (isPullback_comapSubschemeHom W g).w

/- English proof (authored)
The support of the new intersection is the inverse image of the closed original intersection support. The upper component has a generic point there. Flatness makes the underlying map generalizing, so the closure of the image of that point is a component of the original support and contains the upper component's image. The image point is generic in this closure, and the generic point of each component is unique.
-/
theorem exists_intersectionComponents_mapsTo_of_flat (T : MarkedIdealWithBoundary.{u}) (_hT : T.IsAdmissible)
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g]
    (_hT' : (T.pullbackOverField Y k' q g).IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (C' : Set ↥Y)
    (hC' : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (J.image (pullbackOverFieldIndex T Y k' q g))) :
    ∃ C ∈ intersectionComponents T.boundary J,
      Set.MapsTo (⇑g) C' C ∧
        ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ := by
  have hg : GeneralizingMap (fun y : ↥Y => g y) :=
    AlgebraicGeometry.Flat.generalizingMap (f := g)
  have hS : IsClosed (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    (intersectionIdeal T.boundary J).support.2
  have hcomp : IsIrreducibleComponentOf C'
      (⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme)) :=
    (mem_intersectionComponents_pullbackOverField_iff T Y k' q g J C').mp hC'
  have hS' : IsClosed (⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme)) :=
    hS.preimage g.continuous
  obtain ⟨ξ₀, hξ₀⟩ := IsIrreducibleComponentOf.exists_isGenericPoint hcomp hS'
  obtain ⟨hCmem, hmaps⟩ := IsIrreducibleComponentOf.closure_image_genericPoint g hg hS hcomp hξ₀
  refine ⟨closure ({g ξ₀} : Set ↥T.scheme),
    (mem_intersectionComponents_iff T.boundary J (closure ({g ξ₀} : Set ↥T.scheme))).mpr hCmem, hmaps, ?_⟩
  intro ξ' ξ hξ' hξ
  have h1 : ξ' = ξ₀ := hξ'.eq hξ₀
  have h2 : IsGenericPoint (g ξ₀) (closure ({g ξ₀} : Set ↥T.scheme)) := rfl
  rw [h1]
  exact h2.eq hξ

/- English proof (authored)
Flatness gives a generalizing map. View the given downstairs component as a component of the closed original intersection support. The component-lifting result gives a component of its inverse-image support containing the specified upper point and carrying its generic point to the downstairs one. The inverse-image support is exactly that of the pulled-back intersection ideal.
-/
theorem exists_mem_intersectionComponents_pullbackOverField_of_flat (T : MarkedIdealWithBoundary.{u}) (_hT : T.IsAdmissible)
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g]
    (_hT' : (T.pullbackOverField Y k' q g).IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme)
    (hC : C ∈ intersectionComponents T.boundary J) (y : ↥Y) (hy : g y ∈ C) :
    ∃ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
        (J.image (pullbackOverFieldIndex T Y k' q g)),
      y ∈ C' ∧
        ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ := by
  classical
  have hg : GeneralizingMap (fun z : ↥Y => g z) := by
    apply AlgebraicGeometry.Flat.generalizingMap
  have hS : IsClosed (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    (intersectionIdeal T.boundary J).support.2
  have hC0 : IsIrreducibleComponentOf C (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    (mem_intersectionComponents_iff T.boundary J C).mp hC
  obtain ⟨C', hC'comp, hyC', _, hgen⟩ :=
    exists_isIrreducibleComponentOf_preimage g hg hS hC0 y hy
  exact ⟨C', (mem_intersectionComponents_pullbackOverField_iff T Y k' q g J C').mpr hC'comp, hyC', hgen⟩

private def subschemePreimageOpens {X : Scheme.{u}} (W : X.IdealSheafData) (A : Set ↥X)
    (h : IsOpen (⇑W.subschemeι ⁻¹' A)) : W.subscheme.Opens :=
  ⟨⇑W.subschemeι ⁻¹' A, h⟩

/- English proof (authored)
The composite of the open immersion and the closed immersion is a topological embedding, so the source is a subspace of the Noetherian target and is itself Noetherian. Every subset of the source is quasi-compact, in particular the inverse image of each quasi-compact open of the target. The composite is therefore quasi-compact.
-/
private theorem quasiCompact_comp_of_noetherianSpace {Z₁ Z₂ Z₃ : Scheme.{u}} (a : Z₁ ⟶ Z₂)
    (b : Z₂ ⟶ Z₃) [AlgebraicGeometry.IsOpenImmersion a] [AlgebraicGeometry.IsClosedImmersion b]
    (h : TopologicalSpace.NoetherianSpace ↥Z₃) :
    AlgebraicGeometry.QuasiCompact (a ≫ b) :=
  haveI := h
  haveI : TopologicalSpace.NoetherianSpace ↥Z₁ :=
    (((AlgebraicGeometry.Scheme.Hom.isClosedEmbedding b).toIsEmbedding.toIsInducing).comp
      a.isOpenEmbedding.toIsEmbedding.toIsInducing).noetherianSpace
  ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩

/- English proof (authored)
Replace the new ideal and the new set by their given pullback descriptions. The square of closed subschemes commutes, so the part over the inverse image of the ambient set is the inverse image of the original open part under the comparison of closed subschemes. It is open by continuity. Base change of that open immersion, pasted with the closed-subscheme square, gives the pullback square for the composite inclusion into the ambient scheme. This inclusion is quasi-compact by base change of the original inclusion. Flat base change then identifies the kernel of the new composite with the pullback of the original kernel.
-/
private theorem exists_isOpen_comap_ker_of_flat {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g]
    (W : X.IdealSheafData) (W' : Y.IdealSheafData) (hW : W' = W.comap g)
    (A : Set ↥X) (A' : Set ↥Y) (hA' : A' = ⇑g ⁻¹' A)
    (hA : IsOpen (⇑W.subschemeι ⁻¹' A))
    (hqc : AlgebraicGeometry.QuasiCompact ((subschemePreimageOpens W A hA).ι ≫ W.subschemeι)) :
    ∃ h' : IsOpen (⇑W'.subschemeι ⁻¹' A'),
      (Scheme.Hom.ker ((subschemePreimageOpens W A hA).ι ≫ W.subschemeι)).comap g =
        Scheme.Hom.ker ((subschemePreimageOpens W' A' h').ι ≫ W'.subschemeι) := by
  subst hW
  subst hA'
  have := hqc
  have hbase : ∀ x : ↥(W.comap g).subscheme,
      W.subschemeι (comapSubschemeHom W g x) = g ((W.comap g).subschemeι x) := by
    intro x
    exact congrArg (fun m : (W.comap g).subscheme ⟶ X => m x) (comapSubschemeHom_comp_subschemeι W g)
  have hset : ⇑(W.comap g).subschemeι ⁻¹' (⇑g ⁻¹' A)
      = ⇑(comapSubschemeHom W g) ⁻¹' (⇑W.subschemeι ⁻¹' A) := by
    ext x
    simp only [Set.mem_preimage]
    rw [hbase x]
  have hopen : IsOpen (⇑(W.comap g).subschemeι ⁻¹' (⇑g ⁻¹' A)) := by
    rw [hset]
    exact hA.preimage (comapSubschemeHom W g).continuous
  refine ⟨hopen, ?_⟩
  have hV : subschemePreimageOpens (W.comap g) (⇑g ⁻¹' A) hopen
      = comapSubschemeHom W g ⁻¹ᵁ subschemePreimageOpens W A hA := by
    apply TopologicalSpace.Opens.ext
    exact hset
  rw [hV]
  have hsq2 := (AlgebraicGeometry.isPullback_morphismRestrict (comapSubschemeHom W g)
    (subschemePreimageOpens W A hA)).paste_vert (isPullback_comapSubschemeHom W g)
  have := quasiCompact_of_isPullback hsq2
  exact (ker_eq_comap_ker_of_isPullback_of_flat hsq2).symm

/- English proof (authored)
The union of upper components mapping into selected lower components lies in the inverse image of the selected union. For the reverse inclusion, start with an upper point mapping to a selected lower component. Flatness lifts it into an upper component whose generic point maps to the generic point of the selected component. This upper component maps into a lower component with that same generic point, so its image lies in the selected component. The two unions therefore have the required inverse-image relation. The intersection ideal also pulls back, since it is a sum of selected boundary ideals. The inclusion of the selected open into the lower intersection and then the ambient scheme is quasi-compact by Noetherianity. Apply flat base change to its kernel and the two inverse-image descriptions. This gives the upper open and identifies its component-union ideal with the pulled-back ideal.
-/
theorem comap_componentUnionIdeal_of_flat (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g]
    (hT' : (T.pullbackOverField Y k' q g).IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme))
    (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J)
    (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    ∃ hop' : IsOpen (⇑(intersectionIdeal (T.pullbackOverField Y k' q g).boundary
            (J.image (pullbackOverFieldIndex T Y k' q g))).subschemeι ⁻¹'
          ⋃₀ {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (J.image (pullbackOverFieldIndex T Y k' q g)) ∧
            ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C}),
      (componentUnionIdeal T.boundary J 𝒞 hop).comap g =
        componentUnionIdeal (T.pullbackOverField Y k' q g).boundary
          (J.image (pullbackOverFieldIndex T Y k' q g))
          {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (J.image (pullbackOverFieldIndex T Y k' q g)) ∧
            ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C} hop' := by
  classical
  have := hT.isNoetherian
  have hns : TopologicalSpace.NoetherianSpace ↥T.scheme := inferInstance
  have hSclosed : IsClosed (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    (intersectionIdeal T.boundary J).support.2
  have hSclosed' : IsClosed (⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme)) :=
    hSclosed.preimage g.continuous
  have hU : (⋃₀ {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
        (J.image (pullbackOverFieldIndex T Y k' q g)) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C})
      = ⇑g ⁻¹' ⋃₀ 𝒞 := by
    ext y
    simp only [Set.mem_sUnion, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨C', ⟨-, C, hC𝒞, hmaps⟩, hyC'⟩
      exact ⟨C, hC𝒞, hmaps hyC'⟩
    · rintro ⟨C, hC𝒞, hyC⟩
      obtain ⟨C', hC'mem, hyC', hgen⟩ :=
        exists_mem_intersectionComponents_pullbackOverField_of_flat T hT Y k' q g hT' J C (h𝒞 hC𝒞) y hyC
      obtain ⟨C₀, hC₀mem, hmaps0, hgen0⟩ :=
        exists_intersectionComponents_mapsTo_of_flat T hT Y k' q g hT' J C' hC'mem
      obtain ⟨ξ', hξ'⟩ := IsIrreducibleComponentOf.exists_isGenericPoint
        ((mem_intersectionComponents_pullbackOverField_iff T Y k' q g J C').mp hC'mem) hSclosed'
      obtain ⟨ξ, hξ⟩ := IsIrreducibleComponentOf.exists_isGenericPoint
        ((mem_intersectionComponents_iff T.boundary J C).mp (h𝒞 hC𝒞)) hSclosed
      obtain ⟨ξ₀, hξ₀⟩ := IsIrreducibleComponentOf.exists_isGenericPoint
        ((mem_intersectionComponents_iff T.boundary J C₀).mp hC₀mem) hSclosed
      have h1 : g ξ' = ξ := hgen ξ' ξ hξ' hξ
      have h2 : g ξ' = ξ₀ := hgen0 ξ' ξ₀ hξ' hξ₀
      have hξe : closure ({ξ} : Set ↥T.scheme) = C := hξ
      have hξ0e : closure ({ξ₀} : Set ↥T.scheme) = C₀ := hξ₀
      have h3 : C₀ = C := by rw [← hξ0e, ← hξe, ← h1, ← h2]
      refine ⟨C', ⟨hC'mem, C, hC𝒞, ?_⟩, hyC'⟩
      rw [← h3]
      exact hmaps0
  have hqc := quasiCompact_comp_of_noetherianSpace
    (subschemePreimageOpens (intersectionIdeal T.boundary J) (⋃₀ 𝒞) hop).ι
    (intersectionIdeal T.boundary J).subschemeι hns
  obtain ⟨h', hker⟩ := exists_isOpen_comap_ker_of_flat g (intersectionIdeal T.boundary J)
    (intersectionIdeal (T.pullbackOverField Y k' q g).boundary (J.image (pullbackOverFieldIndex T Y k' q g)))
    (intersectionIdeal_pullbackOverField T Y k' q g J) (⋃₀ 𝒞)
    (⋃₀ {C' : Set ↥Y | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
        (J.image (pullbackOverFieldIndex T Y k' q g)) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C})
    hU hop hqc
  exact ⟨h', hker⟩

end FunctorialResolution.EmbeddedResolution

end

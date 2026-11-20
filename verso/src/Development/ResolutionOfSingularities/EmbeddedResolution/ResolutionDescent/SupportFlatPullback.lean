import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
A flat ring map satisfies going down for prime ideals. On affine neighborhoods this lifts any generization of an image point to a generization of the given source point, so the scheme map is generalizing.
-/
private theorem generalizingMap_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f] :
    GeneralizingMap (fun x : ↥X => f x) :=
  AlgebraicGeometry.Flat.generalizingMap f

/- English proof (authored)
Choose the generic point of the given component. The closure of the component’s image is the closure of the image generic point, by continuity and the presence of that point in the image. Every generization of the image generic point lifts to a generization of the original generic point. A component generic point has no distinct generization, since the closure of a generization is an irreducible set containing that component, which must coincide with it. Thus the image generic point has no distinct generization either. In a scheme an irreducible closed set has a generic point. Applying this to the closure of any irreducible set containing the image point’s closure proves maximality of that closure, making it a component.
-/
theorem closure_image_mem_irreducibleComponents_of_generalizingMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap (fun x : ↥X => f x))
    {C : Set ↥X} (hC : C ∈ irreducibleComponents ↥X) :
    closure ((fun x : ↥X => f x) '' C) ∈ irreducibleComponents ↥Y := by
  have hcont : Continuous (fun x : ↥X => f x) := f.continuous
  have hCirr : IsIrreducible C := hC.1
  have hCmax : ∀ ⦃b : Set ↥X⦄, IsIrreducible b → C ≤ b → b ≤ C := hC.2
  have hCcl : closure C = C :=
    subset_antisymm (hCmax hCirr.closure subset_closure) subset_closure
  have hCclosed : IsClosed C := by rw [← hCcl]; exact isClosed_closure
  obtain ⟨η, hη⟩ := QuasiSober.sober hCirr hCclosed
  have hη' : closure ({η} : Set ↥X) = C := hη
  have hηC : η ∈ C := by rw [← hη']; exact subset_closure rfl
  have key : closure ((fun x : ↥X => f x) '' C) = closure ({f η} : Set ↥Y) := by
    have h1 : (fun x : ↥X => f x) '' C ⊆ closure ({f η} : Set ↥Y) := by
      rw [← hη']
      intro w hw
      have hw2 := image_closure_subset_closure_image hcont hw
      rwa [Set.image_singleton] at hw2
    have h2 : ({f η} : Set ↥Y) ⊆ (fun x : ↥X => f x) '' C :=
      Set.singleton_subset_iff.mpr (Set.mem_image_of_mem _ hηC)
    exact subset_antisymm (closure_minimal h1 isClosed_closure) (closure_mono h2)
  have hmax : ∀ y : ↥Y, y ⤳ f η → y = f η := by
    intro y hy
    obtain ⟨x', hx'η, hfx'⟩ := hf hy
    have h1 : η ∈ closure ({x'} : Set ↥X) := specializes_iff_mem_closure.mp hx'η
    have h2 : C ⊆ closure ({x'} : Set ↥X) := by
      rw [← hη']
      exact closure_minimal (Set.singleton_subset_iff.mpr h1) isClosed_closure
    have h3 : closure ({x'} : Set ↥X) ⊆ C := hCmax isIrreducible_singleton.closure h2
    have hx'C : x' ∈ C := h3 (subset_closure rfl)
    have hηx' : η ⤳ x' := specializes_iff_mem_closure.mpr (by rw [hη']; exact hx'C)
    have hA : nhds x' ≤ nhds η := hx'η
    have hB : nhds η ≤ nhds x' := hηx'
    have hins : Inseparable x' η := le_antisymm hA hB
    have hxx : x' = η := hins.eq
    rw [← hfx', hxx]
  rw [key]
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro Z hZ hsub
  have hZ' : IsIrreducible Z := hZ
  have hsub' : closure ({f η} : Set ↥Y) ⊆ Z := hsub
  obtain ⟨z, hz⟩ := QuasiSober.sober hZ'.closure isClosed_closure
  have hz' : closure ({z} : Set ↥Y) = closure Z := hz
  have h1 : f η ∈ closure ({z} : Set ↥Y) := by
    rw [hz']
    exact subset_closure (hsub' (subset_closure rfl))
  have h2 : z = f η := hmax z (specializes_iff_mem_closure.mpr h1)
  show Z ⊆ closure ({f η} : Set ↥Y)
  intro w hw
  rw [← h2, hz']
  exact subset_closure hw

/- English proof (authored)
An ideal sheaf pulled back to a source point is proper in the local ring exactly when the original ideal is proper at its image. Accordingly its support is the inverse image of the original support.
-/
theorem support_comap {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set ↥X) = (fun x : ↥X => f x) ⁻¹' (I.support : Set ↥Y) := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap I f]
  rfl

namespace NonzeroOnComponents

/- English proof (authored)
If a source component were contained in the pullback support, its image would lie in the original support. This support is closed, so it would contain the closure of the image. The generalizing-map result makes that closure an irreducible component of the target, contradicting nonvanishing on components.
-/
theorem comap_of_generalizingMap {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y)
    (hf : GeneralizingMap (fun x : ↥X => f x)) :
    NonzeroOnComponents (I.comap f) := by
  intro T hT hsub
  have hsub' : closure ((fun x : ↥X => f x) '' T) ⊆ (I.support : Set ↥Y) := by
    refine closure_minimal ?_ I.support.2
    rintro _ ⟨x, hxT, rfl⟩
    have hx : x ∈ ((I.comap f).support : Set ↥X) := hsub hxT
    rw [support_comap f I] at hx
    exact hx
  exact hI _ (closure_image_mem_irreducibleComponents_of_generalizingMap f hf hT) hsub'

/- English proof (authored)
A flat morphism is generalizing. The result for generalizing maps therefore applies to the given ideal under this flat pullback.
-/
theorem comap_of_flat {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y) [AlgebraicGeometry.Flat f] :
    NonzeroOnComponents (I.comap f) :=
  hI.comap_of_generalizingMap f (generalizingMap_of_flat f)

/- English proof (authored)
An open immersion is generalizing because every generization of a point of an open set still lies in the open. Apply the nonvanishing result for generalizing maps to this immersion.
-/
theorem comap_of_isOpenImmersion {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    NonzeroOnComponents (I.comap f) :=
  hI.comap_of_generalizingMap f f.isOpenEmbedding.generalizingMap

end NonzeroOnComponents

/- English proof (authored)
Flatness makes the map generalizing. The closure of the image of a component under such a map is a target component by the component-tracking theorem.
-/
theorem closure_image_mem_irreducibleComponents_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
    {C : Set ↥X} (hC : C ∈ irreducibleComponents ↥X) :
    closure ((fun x : ↥X => f x) '' C) ∈ irreducibleComponents ↥Y :=
  closure_image_mem_irreducibleComponents_of_generalizingMap f (generalizingMap_of_flat f) hC

end FunctorialResolution.EmbeddedResolution

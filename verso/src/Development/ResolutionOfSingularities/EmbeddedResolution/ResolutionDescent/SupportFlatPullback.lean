import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
The claim follows from `AlgebraicGeometry.Flat.generalizingMap f`.
-/
private theorem generalizingMap_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f] :
    GeneralizingMap (fun x : ↥X => f x) :=
  AlgebraicGeometry.Flat.generalizingMap f

/- English proof (translation)
Establish `hcont : Continuous (fun x : ↥X => f x)` using `f.continuous`. Establish `hCirr : IsIrreducible C` using `hC.1`. Establish `hCmax : ∀ ⦃b : Set ↥X⦄, IsIrreducible b → C ≤ b → b ≤ C` using `hC.2`. Establish `hCcl : closure C = C` using `subset_antisymm (hCmax hCirr.closure subset_closure) subset_closure`. Establish `hCclosed : IsClosed C` using `by rw [← hCcl]; exact isClosed_closure`.

Take `⟨η, hη⟩` from `QuasiSober.sober hCirr hCclosed`. Establish `hη' : closure ({η} : Set ↥X) = C` using `hη`. Establish `hηC : η ∈ C` using `by rw [← hη']; exact subset_closure rfl`. Establish `key : closure ((fun x : ↥X => f x) '' C) = closure ({f η} : Set ↥Y)`. Establish `h1 : (fun x : ↥X => f x) '' C ⊆ closure ({f η} : Set ↥Y)`.

Rewrite using `[← hη']`. Introduce `w hw`. Establish `hw2` using `image_closure_subset_closure_image hcont hw`. Rewrite `hw2` using `[Set.image_singleton]`. Then use the resulting hypothesis. Establish `h2 : ({f η} : Set ↥Y) ⊆ (fun x : ↥X => f x) '' C` using `Set.singleton_subset_iff.mpr (Set.mem_image_of_mem _ hηC)`.

Conclude with `subset_antisymm (closure_minimal h1 isClosed_closure) (closure_mono h2)`. Establish `hmax : ∀ y : ↥Y, y ⤳ f η → y = f η`. Introduce `y hy`. Take `⟨x', hx'η, hfx'⟩` from `hf hy`. Establish `h1 : η ∈ closure ({x'} : Set ↥X)` using `specializes_iff_mem_closure.mp hx'η`.

Establish `h2 : C ⊆ closure ({x'} : Set ↥X)`. Rewrite using `[← hη']`. Conclude with `closure_minimal (Set.singleton_subset_iff.mpr h1) isClosed_closure`. Establish `h3 : closure ({x'} : Set ↥X) ⊆ C` using `hCmax isIrreducible_singleton.closure h2`. Establish `hx'C : x' ∈ C` using `h3 (subset_closure rfl)`.

Establish `hηx' : η ⤳ x'` using `specializes_iff_mem_closure.mpr (by rw [hη']; exact hx'C)`. Establish `hA : nhds x' ≤ nhds η` using `hx'η`. Establish `hB : nhds η ≤ nhds x'` using `hηx'`. Establish `hins : Inseparable x' η` using `le_antisymm hA hB`. Establish `hxx : x' = η` using `hins.eq`.

Rewrite using `[← hfx', hxx]`. Rewrite using `[key]`. Use `⟨isIrreducible_singleton.closure, ?_⟩` and prove the remaining obligations. Introduce `Z hZ hsub`. Establish `hZ' : IsIrreducible Z` using `hZ`.

Establish `hsub' : closure ({f η} : Set ↥Y) ⊆ Z` using `hsub`. Take `⟨z, hz⟩` from `QuasiSober.sober hZ'.closure isClosed_closure`. Establish `hz' : closure ({z} : Set ↥Y) = closure Z` using `hz`. Establish `h1 : f η ∈ closure ({z} : Set ↥Y)`. Rewrite using `[hz']`.

Conclude with `subset_closure (hsub' (subset_closure rfl))`. Establish `h2 : z = f η` using `hmax z (specializes_iff_mem_closure.mpr h1)`. Use `show Z ⊆ closure ({f η} : Set ↥Y)`. Introduce `w hw`. Rewrite using `[← h2, hz']`.

Conclude with `subset_closure hw`.
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

/- English proof (translation)
Rewrite using `[AlgebraicGeometry.Scheme.IdealSheafData.support_comap I f]`. Both sides reduce to the same expression.
-/
theorem support_comap {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set ↥X) = (fun x : ↥X => f x) ⁻¹' (I.support : Set ↥Y) := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap I f]
  rfl

namespace NonzeroOnComponents

/- English proof (translation)
Introduce `T hT hsub`. Establish `hsub' : closure ((fun x : ↥X => f x) '' T) ⊆ (I.support : Set ↥Y)`. Use `closure_minimal ?_ I.support.2` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hxT, rfl⟩`. Establish `hx : x ∈ ((I.comap f).support : Set ↥X)` using `hsub hxT`.

Rewrite `hx` using `[support_comap f I]`. Conclude with `hx`. Conclude with `hI _ (closure_image_mem_irreducibleComponents_of_generalizingMap f hf hT) hsub'`.
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

/- English proof (translation)
The claim follows from `hI.comap_of_generalizingMap f (generalizingMap_of_flat f)`.
-/
theorem comap_of_flat {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y) [AlgebraicGeometry.Flat f] :
    NonzeroOnComponents (I.comap f) :=
  hI.comap_of_generalizingMap f (generalizingMap_of_flat f)

/- English proof (translation)
The claim follows from `hI.comap_of_generalizingMap f f.isOpenEmbedding.generalizingMap`.
-/
theorem comap_of_isOpenImmersion {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    NonzeroOnComponents (I.comap f) :=
  hI.comap_of_generalizingMap f f.isOpenEmbedding.generalizingMap

end NonzeroOnComponents

/- English proof (translation)
The claim follows from `closure_image_mem_irreducibleComponents_of_generalizingMap f (generalizingMap_of_flat f) hC`.
-/
theorem closure_image_mem_irreducibleComponents_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
    {C : Set ↥X} (hC : C ∈ irreducibleComponents ↥X) :
    closure ((fun x : ↥X => f x) '' C) ∈ irreducibleComponents ↥Y :=
  closure_image_mem_irreducibleComponents_of_generalizingMap f (generalizingMap_of_flat f) hC

end FunctorialResolution.EmbeddedResolution

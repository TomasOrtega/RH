import Mathlib
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `hcont : Continuous (fun x : ↥X => f x)` using `f.base.hom.continuous`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨η, hη⟩` from `QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)`. Establish `hη' : closure ({η} : Set ↥Y) = C` using `hη`.

Establish `hxmem : (fun x : ↥X => f x) x ∈ closure ({η} : Set ↥Y)`. Rewrite using `[hη']`. Conclude with `hx`. Establish `hspec : η ⤳ (fun x : ↥X => f x) x` using `specializes_iff_mem_closure.mpr hxmem`. Take `⟨x', hx'spec, hfx'⟩` from `hf hspec`.

Use `⟨irreducibleComponent x', irreducibleComponent_mem_irreducibleComponents x', ?_, ?_⟩` and prove the remaining obligations. Establish `hsub : closure ({x'} : Set ↥X) ⊆ irreducibleComponent x'` using `closure_minimal (Set.singleton_subset_iff.2 mem_irreducibleComponent) isClosed_irreducibleComponent`. Conclude with `hsub (specializes_iff_mem_closure.mp hx'spec)`. Establish `hsub : C ⊆ closure ((fun x : ↥X => f x) '' irreducibleComponent x')`. Rewrite using `[← hη']`.

Use `closure_minimal (Set.singleton_subset_iff.2 ?_) isClosed_closure` and prove the remaining obligations. Conclude with `subset_closure ⟨x', mem_irreducibleComponent, hfx'⟩`. Establish `hirr : IsIrreducible (closure ((fun x : ↥X => f x) '' irreducibleComponent x'))` using `(isIrreducible_irreducibleComponent.image (fun x : ↥X => f x) hcont.continuousOn).closure`. Conclude with `Set.Subset.antisymm (hC.2 hirr hsub) hsub`. Introduce and unpack `⟨C', -, hxC', rfl⟩`.

Conclude with `subset_closure ⟨x, hxC', rfl⟩`.
-/
theorem apply_mem_irreducibleComponent_iff_of_generalizingMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap (fun x : ↥X => f x))
    {C : Set ↥Y} (hC : C ∈ irreducibleComponents ↥Y) (x : ↥X) :
    (fun x : ↥X => f x) x ∈ C ↔
      ∃ C' : Set ↥X, C' ∈ irreducibleComponents ↥X ∧ x ∈ C' ∧
        closure ((fun x : ↥X => f x) '' C') = C := by
  have hcont : Continuous (fun x : ↥X => f x) := f.base.hom.continuous
  constructor
  · intro hx
    obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
    have hη' : closure ({η} : Set ↥Y) = C := hη
    have hxmem : (fun x : ↥X => f x) x ∈ closure ({η} : Set ↥Y) := by
      rw [hη']
      exact hx
    have hspec : η ⤳ (fun x : ↥X => f x) x := specializes_iff_mem_closure.mpr hxmem
    obtain ⟨x', hx'spec, hfx'⟩ := hf hspec
    refine ⟨irreducibleComponent x', irreducibleComponent_mem_irreducibleComponents x',
      ?_, ?_⟩
    · have hsub : closure ({x'} : Set ↥X) ⊆ irreducibleComponent x' :=
        closure_minimal (Set.singleton_subset_iff.2 mem_irreducibleComponent)
          isClosed_irreducibleComponent
      exact hsub (specializes_iff_mem_closure.mp hx'spec)
    · have hsub : C ⊆ closure ((fun x : ↥X => f x) '' irreducibleComponent x') := by
        rw [← hη']
        refine closure_minimal (Set.singleton_subset_iff.2 ?_) isClosed_closure
        exact subset_closure ⟨x', mem_irreducibleComponent, hfx'⟩
      have hirr : IsIrreducible (closure ((fun x : ↥X => f x) '' irreducibleComponent x')) :=
        (isIrreducible_irreducibleComponent.image (fun x : ↥X => f x)
          hcont.continuousOn).closure
      exact Set.Subset.antisymm (hC.2 hirr hsub) hsub
  · rintro ⟨C', -, hxC', rfl⟩
    exact subset_closure ⟨x, hxC', rfl⟩

/- English proof (translation)
Establish `hf : GeneralizingMap (fun x : ↥X => f x)` using `AlgebraicGeometry.Flat.generalizingMap (f := f)`. Conclude with `apply_mem_irreducibleComponent_iff_of_generalizingMap f hf hC x`.
-/
theorem apply_mem_irreducibleComponent_iff_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
    {C : Set ↥Y} (hC : C ∈ irreducibleComponents ↥Y) (x : ↥X) :
    (fun x : ↥X => f x) x ∈ C ↔
      ∃ C' : Set ↥X, C' ∈ irreducibleComponents ↥X ∧ x ∈ C' ∧
        closure ((fun x : ↥X => f x) '' C') = C := by
  have hf : GeneralizingMap (fun x : ↥X => f x) :=
    AlgebraicGeometry.Flat.generalizingMap (f := f)
  exact apply_mem_irreducibleComponent_iff_of_generalizingMap f hf hC x

end FunctorialResolution.EmbeddedResolution

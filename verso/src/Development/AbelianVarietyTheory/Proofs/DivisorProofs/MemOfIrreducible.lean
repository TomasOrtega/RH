import Mathlib

universe u_1 u_2

namespace GlobalTheory.IrreducibleMembership

/- English proof (translation)
Break down `subsingleton_or_nontrivial V with hV | hV` into its components or cases. Establish `hf1 : f = 1` using `LinearMap.ext fun v => Subsingleton.elim _ _`. Rewrite using `[hf1]`. Conclude with `S.one_mem`. Establish `hso : IsSimpleOrder (Submodule S V)`.

Use `⟨fun N => ?_⟩` and prove the remaining obligations. Establish `hN` using `h (N.restrictScalars K) fun g hg v hv => by`. Establish `hmem : (⟨g, hg⟩ : S) • v ∈ N` using `N.smul_mem _ hv`. Conclude with `hmem`. Break down `hN with hN | hN` into its components or cases.

Use `left`. Conclude with `(Submodule.restrictScalars_eq_bot_iff K S V).1 hN`. Use `right`. Conclude with `(Submodule.restrictScalars_eq_top_iff K S V).1 hN`. Establish `hsimp : IsSimpleModule S V` using `⟨⟩`.

Establish `hbij` using `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K`. Set `F : Module.End (Module.End S V) V` to `{ toFun := f map_add' := f.map_add map_smul' := fun g v => by`. Take `⟨c, hc⟩` from `hbij.2 g`. Rewrite using `[← hc]`. Simplify using `}`.

Set `b` to `Module.finBasis K V`. Take `⟨r, hr⟩` from `jacobson_density F (Finset.univ.image b)`. Establish `hfr : f = (r : Module.End K V)`. Use `b.ext fun i => ?_` and prove the remaining obligations. Use `hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))` as an intermediate fact.

Conclude with `this`. Rewrite using `[hfr]`. Conclude with `r.2`.
-/
theorem mem_of_irreducible {K : Type u_1} {V : Type u_2} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hf1 : f = 1 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hf1]
    exact S.one_mem
  · have hso : IsSimpleOrder (Submodule S V) := by
      refine ⟨fun N => ?_⟩
      have hN := h (N.restrictScalars K) fun g hg v hv => by
        have hmem : (⟨g, hg⟩ : S) • v ∈ N := N.smul_mem _ hv
        exact hmem
      rcases hN with hN | hN
      · left
        exact (Submodule.restrictScalars_eq_bot_iff K S V).1 hN
      · right
        exact (Submodule.restrictScalars_eq_top_iff K S V).1 hN
    have hsimp : IsSimpleModule S V := ⟨⟩
    have hbij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K
    let F : Module.End (Module.End S V) V :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := fun g v => by
          obtain ⟨c, hc⟩ := hbij.2 g
          rw [← hc]
          simp }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
    have hfr : f = (r : Module.End K V) := by
      refine b.ext fun i => ?_
      have := hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))
      exact this
    rw [hfr]
    exact r.2

end GlobalTheory.IrreducibleMembership

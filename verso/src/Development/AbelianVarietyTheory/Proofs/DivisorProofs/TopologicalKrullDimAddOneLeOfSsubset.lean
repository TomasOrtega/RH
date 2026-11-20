import Mathlib

open TopologicalSpace

namespace GlobalTheory

/- English proof (translation)
Establish `hsub : A ⊆ B` using `hAB.subset`. Establish `hemb : Topology.IsClosedEmbedding (Set.inclusion hsub)` using `Topology.IsClosedEmbedding.inclusion hsub (hA.preimage continuous_subtype_val)`. Use `haveI : IrreducibleSpace A := Subtype.irreducibleSpace hAi`. Use `haveI : IrreducibleSpace B := Subtype.irreducibleSpace hBi`. Set `f : IrreducibleCloseds A → IrreducibleCloseds B` to `fun Z => ⟨Set.inclusion hsub '' (Z : Set A), Z.isIrreducible.image _ hemb.continuous.continuousOn, hemb.isClosedMap _ Z.isClosed⟩`.

Set `top : IrreducibleCloseds B` to `⟨Set.univ, IrreducibleSpace.isIrreducible_univ B, isClosed_univ⟩`. Establish `hf : StrictMono f`. Introduce `Z W h`. Establish `h' : (Z : Set A) ⊂ (W : Set A)` using `h`. Use `show Set.inclusion hsub '' (Z : Set A) ⊂ Set.inclusion hsub '' (W : Set A)`.

Conclude with `hemb.injective.injOn.image_ssubset_image_iff (Set.subset_univ _) (Set.subset_univ _) |>.mpr h'`. Establish `htop : ∀ Z, f Z < top`. Introduce `Z`. Use `show Set.inclusion hsub '' (Z : Set A) ⊂ Set.univ`. Take `⟨x, hxB, hxA⟩` from `Set.exists_of_ssubset hAB`.

Use `Set.ssubset_univ_iff.mpr ?_` and prove the remaining obligations. Introduce `h`. Establish `: (⟨x, hxB⟩ : B) ∈ Set.inclusion hsub '' (Z : Set A)` using `h ▸ Set.mem_univ _`. Take `⟨y, -, hy⟩` from `this`. Establish `: (y : T) = x` using `congrArg Subtype.val hy`.

Conclude with `hxA (this ▸ y.2)`. Use `haveI : Nonempty (IrreducibleCloseds A) := ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ A, isClosed_univ⟩⟩`. Set `g : WithTop (IrreducibleCloseds A) → IrreducibleCloseds B` to `WithTop.recTopCoe top f`. Establish `hg : StrictMono g`. Rewrite using `[WithTop.strictMono_iff]`.

Conclude with `⟨hf, htop⟩`. Use `Order.krullDim_le_of_strictMono g hg` as an intermediate fact. Rewrite `this` using `[Order.krullDim_WithTop]`. Then use the resulting hypothesis.
-/
theorem topologicalKrullDim_add_one_le_of_ssubset (T : Type) [TopologicalSpace T] (A B : Set T)
    (hA : IsClosed A) (hAi : IsIrreducible A) (hBi : IsIrreducible B) (hAB : A ⊂ B) :
    topologicalKrullDim A + 1 ≤ topologicalKrullDim B := by
  have hsub : A ⊆ B := hAB.subset
  have hemb : Topology.IsClosedEmbedding (Set.inclusion hsub) :=
    Topology.IsClosedEmbedding.inclusion hsub (hA.preimage continuous_subtype_val)
  haveI : IrreducibleSpace A := Subtype.irreducibleSpace hAi
  haveI : IrreducibleSpace B := Subtype.irreducibleSpace hBi
  let f : IrreducibleCloseds A → IrreducibleCloseds B := fun Z =>
    ⟨Set.inclusion hsub '' (Z : Set A),
      Z.isIrreducible.image _ hemb.continuous.continuousOn,
      hemb.isClosedMap _ Z.isClosed⟩
  let top : IrreducibleCloseds B := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ B, isClosed_univ⟩
  have hf : StrictMono f := by
    intro Z W h
    have h' : (Z : Set A) ⊂ (W : Set A) := h
    show Set.inclusion hsub '' (Z : Set A) ⊂ Set.inclusion hsub '' (W : Set A)
    exact hemb.injective.injOn.image_ssubset_image_iff (Set.subset_univ _) (Set.subset_univ _) |>.mpr h'
  have htop : ∀ Z, f Z < top := by
    intro Z
    show Set.inclusion hsub '' (Z : Set A) ⊂ Set.univ
    obtain ⟨x, hxB, hxA⟩ := Set.exists_of_ssubset hAB
    refine Set.ssubset_univ_iff.mpr ?_
    intro h
    have : (⟨x, hxB⟩ : B) ∈ Set.inclusion hsub '' (Z : Set A) := h ▸ Set.mem_univ _
    obtain ⟨y, -, hy⟩ := this
    have : (y : T) = x := congrArg Subtype.val hy
    exact hxA (this ▸ y.2)
  haveI : Nonempty (IrreducibleCloseds A) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ A, isClosed_univ⟩⟩
  let g : WithTop (IrreducibleCloseds A) → IrreducibleCloseds B := WithTop.recTopCoe top f
  have hg : StrictMono g := by
    rw [WithTop.strictMono_iff]
    exact ⟨hf, htop⟩
  have := Order.krullDim_le_of_strictMono g hg
  rwa [Order.krullDim_WithTop] at this

end GlobalTheory

import Mathlib

namespace GlobalTheory.ClosureDimensionSpecialization

open Order TopologicalSpace Topology

/- English proof (translation)
Introduce `X z w j hzw hne hdim`. Establish `hsub : closure ({w} : Set X) ⊆ closure {z}` using `closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hzw)) isClosed_closure`. Establish `hind : IsInducing (Set.inclusion hsub)` using `(IsEmbedding.inclusion hsub).isInducing`. Use `haveI : IrreducibleSpace (closure ({z} : Set X)) := Subtype.irreducibleSpace isIrreducible_singleton.closure`. Set `top : IrreducibleCloseds (closure ({z} : Set X))` to `⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩`.

Establish `hlt : ∀ a, IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a < top`. Introduce `a`. Use `lt_of_le_of_ne (fun _ _ => Set.mem_univ _) ?_` and prove the remaining obligations. Introduce `h`. Establish `hz : (⟨z, subset_closure rfl⟩ : closure ({z} : Set X)) ∈ (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _)`.

Rewrite using `[h]`. Conclude with `Set.mem_univ _`. Establish `hcl : IsClosed {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)}` using `isClosed_closure.preimage continuous_subtype_val`. Establish `hsub' : (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) ⊆ {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)}`. Rewrite using `[IrreducibleCloseds.coe_map]`.

Use `closure_minimal ?_ hcl` and prove the remaining obligations. Introduce and unpack `_ ⟨y, -, rfl⟩`. Conclude with `y.2`. Establish `hwz : w ⤳ z` using `specializes_iff_mem_closure.mpr (hsub' hz)`. Conclude with `hne ((hzw.antisymm hwz).eq).symm`.

Rewrite using `[topologicalKrullDim, krullDim_eq_iSup_height]`. Use `iSup_le fun a => ?_` and prove the remaining obligations. Establish `h1 : height a + 1 ≤ height top`. Combine the equalities or inequalities in the displayed calculation. Conclude with `height_le_height_apply_of_strictMono _ (IrreducibleCloseds.map_strictMono_of_isInducing hind) a`.

Use `_ ≤ height top := height_add_one_le (hlt a)`. Establish `h2 : (height top : WithBot ℕ∞) ≤ (↑(j + (1 : ℕ)) : WithBot ℕ∞)`. Rewrite using `[← hdim]`. Conclude with `height_le_krullDim top`. Establish `h3 : height top ≤ ((j : ℕ∞) + 1)` using `by exact_mod_cast h2`.

Establish `h4 : height a ≤ (j : ℕ∞)` using `(WithTop.add_le_add_iff_right ENat.one_ne_top).mp (h1.trans h3)`. Conclude with `h4` after adjusting the coercions.
-/
theorem dim_closure_le_of_specializes : ∀ (X : AlgebraicGeometry.Scheme) (z w : ↥X) (j : ℕ),
    z ⤳ w → w ≠ z →
    topologicalKrullDim (↑(closure {z}) : Type) = (↑(j + (1 : ℕ)) : WithBot ℕ∞) →
    topologicalKrullDim (↑(closure {w}) : Type) ≤ (↑j : WithBot ℕ∞) := by
  intro X z w j hzw hne hdim
  have hsub : closure ({w} : Set X) ⊆ closure {z} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hzw))
      isClosed_closure
  have hind : IsInducing (Set.inclusion hsub) := (IsEmbedding.inclusion hsub).isInducing
  haveI : IrreducibleSpace (closure ({z} : Set X)) :=
    Subtype.irreducibleSpace isIrreducible_singleton.closure
  let top : IrreducibleCloseds (closure ({z} : Set X)) :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have hlt : ∀ a, IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a < top := by
    intro a
    refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) ?_
    intro h
    have hz : (⟨z, subset_closure rfl⟩ : closure ({z} : Set X)) ∈
        (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) := by
      rw [h]; exact Set.mem_univ _
    have hcl : IsClosed {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)} :=
      isClosed_closure.preimage continuous_subtype_val
    have hsub' : (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) ⊆
        {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)} := by
      rw [IrreducibleCloseds.coe_map]
      refine closure_minimal ?_ hcl
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hwz : w ⤳ z := specializes_iff_mem_closure.mpr (hsub' hz)
    exact hne ((hzw.antisymm hwz).eq).symm
  rw [topologicalKrullDim, krullDim_eq_iSup_height]
  refine iSup_le fun a => ?_
  have h1 : height a + 1 ≤ height top :=
    calc height a + 1 ≤ height (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a) + 1 := by
          gcongr
          exact height_le_height_apply_of_strictMono _
            (IrreducibleCloseds.map_strictMono_of_isInducing hind) a
      _ ≤ height top := height_add_one_le (hlt a)
  have h2 : (height top : WithBot ℕ∞) ≤ (↑(j + (1 : ℕ)) : WithBot ℕ∞) := by
    rw [← hdim]; exact height_le_krullDim top
  have h3 : height top ≤ ((j : ℕ∞) + 1) := by exact_mod_cast h2
  have h4 : height a ≤ (j : ℕ∞) :=
    (WithTop.add_le_add_iff_right ENat.one_ne_top).mp (h1.trans h3)
  exact_mod_cast h4

end GlobalTheory.ClosureDimensionSpecialization

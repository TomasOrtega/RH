import Mathlib

open Module

noncomputable section

namespace GlobalTheory.RatSpan

section Lin

variable {K' V' W : Type} [Field K'] [AddCommGroup V'] [Module K' V'] [AddCommGroup W] [Module ℂ W]
  {σ' : K' →+* ℂ} (j' : V' →ₛₗ[σ'] W)

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`.
-/
private theorem span_range_le_comap_span_image {κ : Type} (x : κ → V') :
    Submodule.span K' (Set.range x) ≤ (Submodule.span ℂ (Set.range fun k => j' (x k))).comap j' := by
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact Submodule.subset_span ⟨k, rfl⟩

/- English proof (translation)
Use `Module.Finite.of_basis b'` as an intermediate fact. Establish `hcard : Fintype.card ι' = Fintype.card κ`. Rewrite using `[← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis c]`. Establish `hle : Submodule.span ℂ (Set.range fun i => j' (b' i)) ≤ Submodule.span ℂ (Set.range fun k => j' (c k))`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hi : b' i ∈ Submodule.span K' (Set.range c)` using `by rw [c.span_eq]; trivial`. Conclude with `span_range_le_comap_span_image j' c hi`. Establish `: Module.Finite ℂ (Submodule.span ℂ (Set.range fun k => j' (c k)))` using `Module.Finite.span_of_finite ℂ (Set.finite_range _)`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hcard, linearIndependent_iff_card_eq_finrank_span.mp hb]`. Conclude with `Submodule.finrank_mono hle`. Conclude with `finrank_range_le_card _`.
-/
private theorem linearIndependent_image_basis_of_linearIndependent {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V')
    (hb : LinearIndependent ℂ fun i => j' (b' i)) {κ : Type} [Fintype κ] (c : Basis κ K' V') :
    LinearIndependent ℂ fun k => j' (c k) := by
  have := Module.Finite.of_basis b'
  have hcard : Fintype.card ι' = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis c]
  have hle : Submodule.span ℂ (Set.range fun i => j' (b' i)) ≤
      Submodule.span ℂ (Set.range fun k => j' (c k)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : b' i ∈ Submodule.span K' (Set.range c) := by rw [c.span_eq]; trivial
    exact span_range_le_comap_span_image j' c hi
  have : Module.Finite ℂ (Submodule.span ℂ (Set.range fun k => j' (c k))) :=
    Module.Finite.span_of_finite ℂ (Set.finite_range _)
  rw [linearIndependent_iff_card_eq_finrank_span]
  apply le_antisymm
  · rw [← hcard, linearIndependent_iff_card_eq_finrank_span.mp hb]
    exact Submodule.finrank_mono hle
  · exact finrank_range_le_card _

/- English proof (translation)
Use `Module.Finite.of_basis b'` as an intermediate fact. Establish `hs : LinearIndepOn K' id (Set.range x)` using `(linearIndepOn_id_range_iff hx.injective).mpr hx`. Establish `: Fintype (hs.extend (Set.subset_univ _))`. Use `Module.Finite.finite_basis (Basis.extend hs)` as an intermediate fact. Conclude with `Fintype.ofFinite _`.

Establish `he` using `linearIndependent_image_basis_of_linearIndependent j' b' hb (Basis.extend hs)`. Set `g : κ → hs.extend (Set.subset_univ _)` to `fun k => ⟨x k, Basis.subset_extend hs ⟨k, rfl⟩⟩`. Establish `hg : Function.Injective g` using `fun a b h => hx.injective (congrArg Subtype.val h)`. Establish `h2` using `he.comp g hg`. Simplify `h2` using `[g, Function.comp_def, Basis.coe_extend]`.
-/
theorem linInd_comp {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V') (hb : LinearIndependent ℂ fun i => j' (b' i))
    {κ : Type} {x : κ → V'} (hx : LinearIndependent K' x) : LinearIndependent ℂ fun k => j' (x k) := by
  have := Module.Finite.of_basis b'
  have hs : LinearIndepOn K' id (Set.range x) := (linearIndepOn_id_range_iff hx.injective).mpr hx
  have : Fintype (hs.extend (Set.subset_univ _)) := by
    have := Module.Finite.finite_basis (Basis.extend hs)
    exact Fintype.ofFinite _
  have he := linearIndependent_image_basis_of_linearIndependent j' b' hb (Basis.extend hs)
  let g : κ → hs.extend (Set.subset_univ _) := fun k => ⟨x k, Basis.subset_extend hs ⟨k, rfl⟩⟩
  have hg : Function.Injective g := fun a b h => hx.injective (congrArg Subtype.val h)
  have h2 := he.comp g hg
  simpa [g, Function.comp_def, Basis.coe_extend] using h2

end Lin

section Main

variable {K K' V V' W : Type} [Field K] [Field K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {σ : K →+* ℂ} {σ' : K' →+* ℂ}

/- English proof (translation)
Use `Module.Finite.of_basis b'` as an intermediate fact. Set `e` to `Module.finBasis K' X`. Set `x : Fin (finrank K' X) → V'` to `fun i => (e i : V')`. Establish `hx : LinearIndependent K' x` using `e.linearIndependent.map' X.subtype X.ker_subtype`. Establish `hjx` using `linInd_comp j' b' hb hx`.

Establish `hspan : Submodule.span ℂ (j' '' X) = Submodule.span ℂ (Set.range fun i => j' (x i))`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Establish `hvx : v ∈ Submodule.span K' (Set.range x)`.

Establish `h1 : (⟨v, hv⟩ : X) ∈ Submodule.span K' (Set.range e)` using `by rw [e.span_eq]; trivial`. Establish `h2` using `Submodule.mem_map_of_mem (f := X.subtype) h1`. Rewrite `h2` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `h2`. Conclude with `span_range_le_comap_span_image j' x hvx`.

Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨x i, (e i).2, rfl⟩`. Rewrite using `[hspan, finrank_span_eq_card hjx, Fintype.card_fin]`.
-/
theorem finrank_span_image (j' : V' →ₛₗ[σ'] W) {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V')
    (hb : LinearIndependent ℂ fun i => j' (b' i)) (X : Submodule K' V') :
    finrank ℂ (Submodule.span ℂ (j' '' X)) = finrank K' X := by
  have := Module.Finite.of_basis b'
  let e := Module.finBasis K' X
  let x : Fin (finrank K' X) → V' := fun i => (e i : V')
  have hx : LinearIndependent K' x := e.linearIndependent.map' X.subtype X.ker_subtype
  have hjx := linInd_comp j' b' hb hx
  have hspan : Submodule.span ℂ (j' '' X) = Submodule.span ℂ (Set.range fun i => j' (x i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      have hvx : v ∈ Submodule.span K' (Set.range x) := by
        have h1 : (⟨v, hv⟩ : X) ∈ Submodule.span K' (Set.range e) := by rw [e.span_eq]; trivial
        have h2 := Submodule.mem_map_of_mem (f := X.subtype) h1
        rw [Submodule.map_span, ← Set.range_comp] at h2
        exact h2
      exact span_range_le_comap_span_image j' x hvx
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨x i, (e i).2, rfl⟩
  rw [hspan, finrank_span_eq_card hjx, Fintype.card_fin]

/- English proof (translation)
Use `Module.Finite.of_basis b'` as an intermediate fact. Establish `hle : Submodule.span K' (ι '' (U.comap j)) ≤ U.comap j'`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `show j' (ι v) ∈ U`.

Rewrite using `[hj]`. Conclude with `hv`. Use `symm`. Apply `Submodule.eq_of_le_of_finrank_le hle` to reduce the goal to its premises. Rewrite using `[← finrank_span_image j' b' hb, ← finrank_span_image j' b' hb]`.

Combine the equalities or inequalities in the displayed calculation. Apply `Submodule.finrank_mono` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `hv`.

Use `_ ≤ finrank ℂ (Submodule.span ℂ (j' '' (Submodule.span K' (ι '' (U.comap j))))) := by`. Apply `Submodule.finrank_mono` to reduce the goal to its premises. Use `hU.trans (Submodule.span_mono ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `⟨ι v, Submodule.subset_span ⟨v, hv, rfl⟩, hj v⟩`.
-/
theorem comap_eq_span (j : V →ₛₗ[σ] W) (j' : V' →ₛₗ[σ'] W) (ι : V → V') (hj : ∀ v, j' (ι v) = j v)
    {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V') (hb : LinearIndependent ℂ fun i => j' (b' i))
    (U : Submodule ℂ W) (hU : U ≤ Submodule.span ℂ (j '' (U.comap j))) :
    U.comap j' = Submodule.span K' (ι '' (U.comap j)) := by
  have := Module.Finite.of_basis b'
  have hle : Submodule.span K' (ι '' (U.comap j)) ≤ U.comap j' := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    show j' (ι v) ∈ U
    rw [hj]
    exact hv
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [← finrank_span_image j' b' hb, ← finrank_span_image j' b' hb]
  calc finrank ℂ (Submodule.span ℂ (j' '' (U.comap j'))) ≤ finrank ℂ U := by
        apply Submodule.finrank_mono
        rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        exact hv
    _ ≤ finrank ℂ (Submodule.span ℂ (j' '' (Submodule.span K' (ι '' (U.comap j))))) := by
        apply Submodule.finrank_mono
        refine hU.trans (Submodule.span_mono ?_)
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨ι v, Submodule.subset_span ⟨v, hv, rfl⟩, hj v⟩

end Main

end GlobalTheory.RatSpan

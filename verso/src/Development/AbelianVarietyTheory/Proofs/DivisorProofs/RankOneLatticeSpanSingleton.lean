import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Take `⟨e, -, he⟩` from `finrank_eq_one_iff'.mp h1`. Use `choose c hc using fun i => he (u i)`. Take `⟨j, hj⟩` from `hu`. Use `haveI : Nonempty I := ⟨j⟩`. Take `⟨i0, hi0⟩` from `Finite.exists_max (fun i => v (c i))`.

Establish `hcj : c j ≠ 0`. Introduce and unpack `h`. Apply `hj` to reduce the goal to its premises. Rewrite using `[← hc j, h, zero_smul]`. Establish `hc0 : c i0 ≠ 0`.

Introduce `h`. Use `hi0 j` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `hcj ((Valuation.zero_iff v).mp (le_antisymm this zero_le'))`. Establish `key : ∀ i, ∃ t : O, u i = t • u i0`.

Introduce `i`. Establish `hle : v (c i / c i0) ≤ 1`. Rewrite using `[map_div₀, div_le_one₀ ((Valuation.pos_iff v).mpr hc0)]`. Conclude with `hi0 i`. Take `⟨t, ht⟩` from `hv.exists_of_le_one hle`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C t (u i0), ht, ← hc i, ← hc i0, smul_smul, div_mul_cancel₀ _ hc0]`. Use `⟨u i0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc i0]; exact smul_ne_zero hc0 (by rintro rfl; apply hj; rw [← hc j, smul_zero])`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨t, ht⟩` from `key i`. Rewrite using `[ht]`. Conclude with `Submodule.smul_mem _ t (Submodule.subset_span rfl)`.

Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `Submodule.subset_span ⟨i0, rfl⟩`.
-/
theorem finGen_line_span_principal (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    (I : Type) [Finite I] (u : I → V) (hv : v.Integers O) (h1 : Module.finrank C V = 1)
    (hu : ∃ i, u i ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ Submodule.span O (Set.range u) = Submodule.span O {w} := by
  obtain ⟨e, -, he⟩ := finrank_eq_one_iff'.mp h1
  choose c hc using fun i => he (u i)
  obtain ⟨j, hj⟩ := hu
  haveI : Nonempty I := ⟨j⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => v (c i))
  have hcj : c j ≠ 0 := by
    rintro h; apply hj; rw [← hc j, h, zero_smul]
  have hc0 : c i0 ≠ 0 := by
    intro h
    have := hi0 j
    rw [h, map_zero] at this
    exact hcj ((Valuation.zero_iff v).mp (le_antisymm this zero_le'))
  have key : ∀ i, ∃ t : O, u i = t • u i0 := by
    intro i
    have hle : v (c i / c i0) ≤ 1 := by
      rw [map_div₀, div_le_one₀ ((Valuation.pos_iff v).mpr hc0)]
      exact hi0 i
    obtain ⟨t, ht⟩ := hv.exists_of_le_one hle
    refine ⟨t, ?_⟩
    rw [← algebraMap_smul C t (u i0), ht, ← hc i, ← hc i0, smul_smul, div_mul_cancel₀ _ hc0]
  refine ⟨u i0, ?_, ?_⟩
  · rw [← hc i0]; exact smul_ne_zero hc0 (by rintro rfl; apply hj; rw [← hc j, smul_zero])
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨t, ht⟩ := key i
      rw [ht]; exact Submodule.smul_mem _ t (Submodule.subset_span rfl)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨i0, rfl⟩

/- English proof (translation)
Introduce `C _ v O _ _ V _ _ _ _ I _ u hv h1 hu` and use `finGen_line_span_principal C v O V I u hv h1 hu`.
-/
theorem finGen_line_span_principal_target : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (I : Type) [Finite I] (u : I → V), v.Integers O → Module.finrank C V = 1 → (∃ i, u i ≠ 0) → ∃ w : V, w ≠ 0 ∧ Submodule.span O (Set.range u) = Submodule.span O {w} :=
  fun C _ v O _ _ V _ _ _ _ I _ u hv h1 hu => finGen_line_span_principal C v O V I u hv h1 hu
end GlobalTheory

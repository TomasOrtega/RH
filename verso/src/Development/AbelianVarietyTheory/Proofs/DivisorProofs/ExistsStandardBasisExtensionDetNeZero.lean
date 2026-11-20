import Mathlib

open Module Submodule

namespace GlobalTheory

/- English proof (translation)
Introduce `hv`. Use `set std : Fin n → (Fin n → K) := fun i => Pi.single i (1 : K) with hstd`. Use `set W : Submodule K (Fin n → K) := span K (Set.range v) with hWdef`. Take `⟨κ, a, ha, hspan, hli⟩` from `exists_linearIndependent' K (W.mkQ ∘ std)`. Use `haveI : Finite κ := Finite.of_injective a ha`.

Use `haveI : Fintype κ := Fintype.ofFinite κ`. Establish `hW : finrank K W = Fintype.card J` using `finrank_span_eq_card hv`. Establish `hQ` using `Submodule.finrank_quotient_add_finrank W`. Establish `hfin : finrank K (Fin n → K) = n` using `Module.finrank_fin_fun K`. Establish `hκ : Fintype.card κ ≤ finrank K ((Fin n → K) ⧸ W)` using `hli.fintype_card_le_finrank`.

Set `C` to `{i : Fin n // i ∉ Set.range a}`. Establish `hC : Fintype.card C = n - Fintype.card κ`. Establish `h1 : Fintype.card C = Fintype.card (Fin n) - Fintype.card (Set.range a)`. Simplify using `only [C]`. Rewrite using `[Fintype.card_subtype_compl]`.

Rewrite using `[h1, Fintype.card_fin, Set.card_range_of_injective ha]`. Establish `hJC : Fintype.card J ≤ Fintype.card C` using `by omega`. Take `⟨φ⟩` from `Function.Embedding.nonempty_of_card_le hJC`. Set `e : J → Fin n` to `fun j => (φ j).1`. Establish `he : Function.Injective e` using `fun x y h => φ.injective (Subtype.ext h)`.

Establish `heC : ∀ j, e j ∉ Set.range a` using `fun j => (φ j).2`. Use `⟨e, he, ?_⟩` and prove the remaining obligations. Use `set f := Function.extend e v std with hf`. Establish `hfe : ∀ j, f (e j) = v j` using `fun j => he.extend_apply v std j`. Establish `hfa : ∀ k, f (a k) = std (a k)`.

Introduce `k`. Apply `Function.extend_apply'` to reduce the goal to its premises. Introduce and unpack `⟨j, hj⟩`. Conclude with `heC j ⟨k, hj.symm⟩`. Establish `hstdspan : span K (Set.range std) = ⊤`.

Use `(Pi.basisFun K (Fin n)).span_eq` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using `[std, Pi.basisFun_apply]`. Establish `hspanf : span K (Set.range f) = ⊤`.

Establish `hWle : W ≤ span K (Set.range f)`. Apply `span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `subset_span ⟨e j, hfe j⟩`. Establish `hAle : span K (Set.range (std ∘ a)) ≤ span K (Set.range f)`.

Apply `span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `subset_span ⟨a k, hfa k⟩`. Establish `htop : W ⊔ span K (Set.range (std ∘ a)) = ⊤`. Rewrite using `[← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]`.

Establish `: (W.mkQ ∘ std ∘ a) = (W.mkQ ∘ std) ∘ a` using `rfl`. Rewrite `*` using `[← Function.comp_assoc]`. Rewrite using `[hspan, Set.range_comp, ← Submodule.map_span, hstdspan, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `W.mkQ_surjective`. Conclude with `eq_top_iff.mpr (htop ▸ sup_le hWle hAle)`.

Establish `hlin : LinearIndependent K f`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanf, finrank_top, hfin, Fintype.card_fin]`. Establish `hunit : IsUnit (Matrix.of f)`. Rewrite using `[← Matrix.linearIndependent_rows_iff_isUnit]`. Conclude with `hlin`.

Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero`.
-/
theorem extend_linearIndependent_rows_by_standard_basis
    {K : Type} [Field K] {J : Type} [Fintype J] {n : ℕ} (v : J → Fin n → K) :
    LinearIndependent K v → ∃ e : J → Fin n, Function.Injective e ∧
      (Matrix.of (Function.extend e v (fun i => Pi.single i (1 : K)))).det ≠ 0 := by
  intro hv
  set std : Fin n → (Fin n → K) := fun i => Pi.single i (1 : K) with hstd
  set W : Submodule K (Fin n → K) := span K (Set.range v) with hWdef
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (W.mkQ ∘ std)
  classical
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hW : finrank K W = Fintype.card J := finrank_span_eq_card hv
  have hQ := Submodule.finrank_quotient_add_finrank W
  have hfin : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hκ : Fintype.card κ ≤ finrank K ((Fin n → K) ⧸ W) := hli.fintype_card_le_finrank

  let C := {i : Fin n // i ∉ Set.range a}
  have hC : Fintype.card C = n - Fintype.card κ := by
    have h1 : Fintype.card C = Fintype.card (Fin n) - Fintype.card (Set.range a) := by
      simp only [C]
      rw [Fintype.card_subtype_compl]
    rw [h1, Fintype.card_fin, Set.card_range_of_injective ha]
  have hJC : Fintype.card J ≤ Fintype.card C := by omega
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hJC
  let e : J → Fin n := fun j => (φ j).1
  have he : Function.Injective e := fun x y h => φ.injective (Subtype.ext h)
  have heC : ∀ j, e j ∉ Set.range a := fun j => (φ j).2
  refine ⟨e, he, ?_⟩
  set f := Function.extend e v std with hf
  have hfe : ∀ j, f (e j) = v j := fun j => he.extend_apply v std j
  have hfa : ∀ k, f (a k) = std (a k) := by
    intro k
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    exact heC j ⟨k, hj.symm⟩

  have hstdspan : span K (Set.range std) = ⊤ := by
    have := (Pi.basisFun K (Fin n)).span_eq
    convert this using 2
    ext i
    simp [std, Pi.basisFun_apply]
  have hspanf : span K (Set.range f) = ⊤ := by
    have hWle : W ≤ span K (Set.range f) := by
      apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact subset_span ⟨e j, hfe j⟩
    have hAle : span K (Set.range (std ∘ a)) ≤ span K (Set.range f) := by
      apply span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact subset_span ⟨a k, hfa k⟩
    have htop : W ⊔ span K (Set.range (std ∘ a)) = ⊤ := by
      rw [← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
      have : (W.mkQ ∘ std ∘ a) = (W.mkQ ∘ std) ∘ a := rfl
      rw [← Function.comp_assoc] at *
      rw [hspan, Set.range_comp, ← Submodule.map_span, hstdspan, Submodule.map_top, LinearMap.range_eq_top]
      exact W.mkQ_surjective
    exact eq_top_iff.mpr (htop ▸ sup_le hWle hAle)
  have hlin : LinearIndependent K f := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanf, finrank_top, hfin,
      Fintype.card_fin]
  have hunit : IsUnit (Matrix.of f) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hlin
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero

end GlobalTheory

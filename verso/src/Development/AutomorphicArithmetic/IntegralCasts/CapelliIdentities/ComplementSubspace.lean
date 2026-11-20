import Mathlib

noncomputable def UpperTheory.Reformulated.B.ComplementSubspace.IsCompl :
    {K : Type} → [Field K] → {n r : ℕ} → Matrix (Fin r) (Fin n) K → Matrix (Fin n) (Fin n) K → Prop :=
    fun {K : Type} [Field K] {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (a : Matrix (Fin n) (Fin n) K) ↦
      IsUnit a.det ∧ ∀ (i : Fin n) (hi : (↑i : ℕ) < r), a i = c (⟨(↑i : ℕ), hi⟩ : Fin r)

namespace ComplementBasis

/- English proof (translation)
Set `b` to `Module.finBasis K U`. Use `⟨fun i => (b i : Fin n → K), ?_, ?_⟩` and prove the remaining obligations. Conclude with `b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)`. Establish `: Set.range (fun i => (b i : Fin n → K)) = U.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]`.
-/
private lemma basis_sub {K : Type} [Field K] {n : ℕ} (U : Submodule K (Fin n → K)) :
    ∃ c : Fin (Module.finrank K U) → (Fin n → K),
      LinearIndependent K c ∧ Submodule.span K (Set.range c) = U := by
  let b := Module.finBasis K U
  refine ⟨fun i => (b i : Fin n → K), ?_, ?_⟩
  · exact b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · have : Set.range (fun i => (b i : Fin n → K)) = U.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

end ComplementBasis

open ComplementBasis in
/- English proof (translation)
Introduce `K _ n U`. Take `⟨c, hcli, hcsp⟩` from `basis_sub U`. Take `⟨W, hUW⟩` from `Submodule.exists_isCompl U`. Take `⟨w, hwli, hwsp⟩` from `basis_sub W`. Establish `hrm : Module.finrank K U + Module.finrank K W = n`.

Use `Submodule.finrank_add_eq_of_isCompl hUW` as an intermediate fact. Rewrite `this` using `[Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Set `a : Matrix (Fin n) (Fin n) K` to `fun i => if h : (i : ℕ) < Module.finrank K U then c ⟨i, h⟩ else w ⟨(i : ℕ) - Module.finrank K U, by have := i.2; omega⟩`. Use `⟨c, a, ⟨hcli, hcsp⟩, ?_, ?_⟩` and prove the remaining obligations.

Set `e : Fin (Module.finrank K U) ⊕ Fin (Module.finrank K W) ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrm)`. Establish `hg : LinearIndependent K (Sum.elim c w)`. Apply `LinearIndependent.sum_type hcli hwli` to reduce the goal to its premises. Rewrite using `[hcsp, hwsp]`. Conclude with `hUW.disjoint`.

Establish `hae : (fun i => a i) ∘ e = Sum.elim c w`. Use function extensionality and compare the values at `x`. Break down `x with j | k` into its components or cases. Simplify using `[e, a]`. Simplify using `[e, a]`.

Establish `hla : LinearIndependent K (fun i => a i)`. Rewrite using `[← linearIndependent_equiv e, hae]`. Conclude with `hg`. Rewrite using `[← Matrix.isUnit_iff_isUnit_det]`. Conclude with `Matrix.linearIndependent_rows_iff_isUnit.mp hla`.

Introduce `i hi`. Simplify using `[a, hi]`.
-/
theorem UpperTheory.Reformulated.B.ComplementSubspace.main :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (U : Submodule K (Fin n → K)),
      ∃ (c : Matrix (Fin (Module.finrank K ↥U)) (Fin n) K) (a : Matrix (Fin n) (Fin n) K),
        (LinearIndependent K c ∧ Submodule.span K (Set.range c) = U) ∧ UpperTheory.Reformulated.B.ComplementSubspace.IsCompl c a := by
  intro K _ n U
  obtain ⟨c, hcli, hcsp⟩ := basis_sub U
  obtain ⟨W, hUW⟩ := Submodule.exists_isCompl U
  obtain ⟨w, hwli, hwsp⟩ := basis_sub W
  have hrm : Module.finrank K U + Module.finrank K W = n := by
    have := Submodule.finrank_add_eq_of_isCompl hUW
    rw [Module.finrank_fin_fun] at this
    omega
  let a : Matrix (Fin n) (Fin n) K := fun i =>
    if h : (i : ℕ) < Module.finrank K U then c ⟨i, h⟩ else w ⟨(i : ℕ) - Module.finrank K U, by have := i.2; omega⟩
  refine ⟨c, a, ⟨hcli, hcsp⟩, ?_, ?_⟩
  · let e : Fin (Module.finrank K U) ⊕ Fin (Module.finrank K W) ≃ Fin n := finSumFinEquiv.trans (finCongr hrm)
    have hg : LinearIndependent K (Sum.elim c w) := by
      apply LinearIndependent.sum_type hcli hwli
      rw [hcsp, hwsp]; exact hUW.disjoint
    have hae : (fun i => a i) ∘ e = Sum.elim c w := by
      funext x
      rcases x with j | k
      · simp [e, a]
      · simp [e, a]
    have hla : LinearIndependent K (fun i => a i) := by
      rw [← linearIndependent_equiv e, hae]; exact hg
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.linearIndependent_rows_iff_isUnit.mp hla
  · intro i hi
    simp [a, hi]

import Mathlib

noncomputable def UpperTheory.Reformulated.B.SpanTopFamily.Mι :
    {E K : Type} →
      [inst : Field E] →
        [inst_1 : Field K] →
          (O : ValuationSubring K) →
            (E →+* K) → {n : Type} → Submodule (NumberField.RingOfIntegers E) (n → E) → Submodule (↥O) (n → K) :=
    fun {E K : Type} [Field E] [Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
        (L : Submodule (NumberField.RingOfIntegers E) (n → E)) ↦
      Submodule.span (↥O) ((fun (l : n → E) (j : n) ↦ (ι : E → K) (l j)) '' (↑L : Set (n → E)))

/- English proof (translation)
Introduce `E K _ _ _ O ι n _ _ L hL`. Establish `key : ∀ v : n → E, v ∈ Submodule.span E (↑L : Set (n → E)) → (fun j => ι (v j)) ∈ Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K))`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`.

Conclude with `Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)`. Consider the case `zero`. Establish `: (fun j : n => ι ((0 : n → E) j)) = 0`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: (fun j : n => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j))`. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Establish `: (fun j : n => ι ((a • x) j)) = ι a • (fun j => ι (x j))`.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[eq_top_iff]`.

Introduce `w _`. Rewrite using `[pi_eq_sum_univ' w]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `h` using `key (Pi.single i 1) (by rw [hL]; trivial)`. Establish `e : (fun j : n => ι ((Pi.single i 1 : n → E) j)) = Pi.single i (1 : K)`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`.

Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem UpperTheory.Reformulated.B.SpanTopFamily.span_top :
    ∀ {E K : Type} [inst : Field E] [NumberField E] [inst_2 : Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
      [Fintype n] [DecidableEq n] (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
      Submodule.span E (↑L : Set (n → E)) = ⊤ → Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) = ⊤ := by
  intro E K _ _ _ O ι n _ _ L hL
  have key : ∀ v : n → E, v ∈ Submodule.span E (↑L : Set (n → E)) →
      (fun j => ι (v j)) ∈ Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero =>
      have : (fun j : n => ι ((0 : n → E) j)) = 0 := by
        funext j; simp
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun j : n => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j)) := by
        funext j; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : (fun j : n => ι ((a • x) j)) = ι a • (fun j => ι (x j)) := by
        funext j; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_univ' w]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h := key (Pi.single i 1) (by rw [hL]; trivial)
  have e : (fun j : n => ι ((Pi.single i 1 : n → E) j)) = Pi.single i (1 : K) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [e] at h
  exact h

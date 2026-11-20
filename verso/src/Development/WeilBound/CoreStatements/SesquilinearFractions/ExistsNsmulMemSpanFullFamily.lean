import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
open NumberField

namespace PositivityTheory.Xgf

/- English proof (translation)
Use `set N := Submodule.span (𝓞 E) (Set.range e) with hN`. Establish `htor : ∀ y : M, ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ N`. Introduce `y`. Establish `hnot : ¬ LinearIndependent (𝓞 E) (Sum.elim e (fun _ : Unit => y))`. Introduce `hli`.

Use `hli.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[Fintype.card_sum, Fintype.card_unit, hcard]`. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg, i, hi⟩` from `Fintype.not_linearIndependent_iff.mp hnot`. Rewrite `hg` using `[Fintype.sum_sum_type]`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton] at hg`. Distinguish the cases in `hc : g (Sum.inr ()) = 0`. It suffices to derive a contradiction. Rewrite `hg` using `[hc, zero_smul, add_zero]`. Establish `h0` using `Fintype.linearIndependent_iff.mp he (fun j => g (Sum.inl j)) hg`.

Break down `i with j | ⟨⟩` into its components or cases. Conclude with `hi (h0 j)`. Conclude with `hi hc`. Use `⟨g (Sum.inr ()), hc, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_neg_of_add_eq_zero_right hg]`.

Conclude with `N.neg_mem (N.sum_mem fun j _ => N.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩))`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := 𝓞 E) (M := M)`. Use `choose c hc0 hcN using htor`. Establish `ha0 : (∏ y ∈ s, c y) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun y _ => hc0 y`. Establish `haN : ∀ y : M, (∏ y ∈ s, c y) • y ∈ N`.

Introduce `y`. Establish `hy : y ∈ Submodule.span (𝓞 E) (s : Set M)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Rewrite using `[← Finset.prod_erase_mul s c hx, mul_smul]`.

Conclude with `N.smul_mem _ (hcN x)`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [smul_add]`. Conclude with `N.add_mem hx hz`. Consider the case `smul b x _ hx => rw [smul_comm]`.

Conclude with `N.smul_mem b hx`. Establish `hI : Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E)) ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Use `⟨Ideal.absNorm (Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E))), Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E))))`.

Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E), ← hb, mul_smul]`. Conclude with `N.smul_mem b (haN y)`.
-/
theorem exists_nsmul_mem_span_full_family {E : Type} [Field E] [NumberField E] {M : Type} [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] {I : Type} [Fintype I] (e : I → M)
    (hcard : Fintype.card I = Module.finrank (𝓞 E) M) (he : LinearIndependent (𝓞 E) e) :
    ∃ n : ℕ, 0 < n ∧ ∀ y : M, n • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
  classical
  set N := Submodule.span (𝓞 E) (Set.range e) with hN
  have htor : ∀ y : M, ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ N := by
    intro y
    have hnot : ¬ LinearIndependent (𝓞 E) (Sum.elim e (fun _ : Unit => y)) := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [Fintype.card_sum, Fintype.card_unit, hcard] at this
      omega
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton] at hg
    by_cases hc : g (Sum.inr ()) = 0
    · exfalso
      rw [hc, zero_smul, add_zero] at hg
      have h0 := Fintype.linearIndependent_iff.mp he (fun j => g (Sum.inl j)) hg
      rcases i with j | ⟨⟩
      · exact hi (h0 j)
      · exact hi hc
    · refine ⟨g (Sum.inr ()), hc, ?_⟩
      rw [eq_neg_of_add_eq_zero_right hg]
      exact N.neg_mem (N.sum_mem fun j _ => N.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩))
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M)
  choose c hc0 hcN using htor
  have ha0 : (∏ y ∈ s, c y) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun y _ => hc0 y
  have haN : ∀ y : M, (∏ y ∈ s, c y) • y ∈ N := by
    intro y
    have hy : y ∈ Submodule.span (𝓞 E) (s : Set M) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
        rw [← Finset.prod_erase_mul s c hx, mul_smul]
        exact N.smul_mem _ (hcN x)
    | zero => simp
    | add x z _ _ hx hz => rw [smul_add]; exact N.add_mem hx hz
    | smul b x _ hx => rw [smul_comm]; exact N.smul_mem b hx
  have hI : Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  refine ⟨Ideal.absNorm (Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E))),
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y => ?_⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E))))
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hb, mul_smul]
  exact N.smul_mem b (haN y)

end PositivityTheory.Xgf

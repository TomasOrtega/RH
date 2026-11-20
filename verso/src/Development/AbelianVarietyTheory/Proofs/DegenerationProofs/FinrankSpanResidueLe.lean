import Mathlib

namespace GlobalTheory.ResidueSpanScale

/- English proof (translation)
Use `haveI : Nonempty J := ⟨j⟩`. Take `⟨j₀, h₀⟩` from `Finite.exists_max (fun i => ValuationRing.valuation O K (c i))`. Establish `hv : ValuationRing.valuation O K (c j₀) ≠ 0`. Introduce `h`. Establish `h1` using `h₀ j`.

Rewrite `h1` using `[h, le_zero_iff]`. Conclude with `hj ((Valuation.zero_iff _).1 h1)`. Establish `hc : c j₀ ≠ 0` using `fun h => hv (by rw [h, map_zero])`. Establish `hex : ∀ i, ∃ a : O, algebraMap O K a = c i / c j₀`. Introduce `i`.

Rewrite using `[← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff, map_div₀]`. Conclude with `div_le_one_of_le₀ (h₀ i) zero_le`. Use `choose d hd using hex`. Use `⟨j₀, d, hc, ?_, fun i => ?_⟩` and prove the remaining obligations. Apply `IsFractionRing.injective O K` to reduce the goal to its premises.

Rewrite using `[hd, div_self hc, map_one]`. Rewrite using `[hd]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_scale {O K J : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite J] (c : J → K) (j : J) (hj : c j ≠ 0) :
    ∃ (j₀ : J) (d : J → O), c j₀ ≠ 0 ∧ d j₀ = 1 ∧ ∀ i, c i = c j₀ * algebraMap O K (d i) := by
  classical
  haveI : Nonempty J := ⟨j⟩
  obtain ⟨j₀, h₀⟩ := Finite.exists_max (fun i => ValuationRing.valuation O K (c i))
  have hv : ValuationRing.valuation O K (c j₀) ≠ 0 := by
    intro h
    have h1 := h₀ j
    rw [h, le_zero_iff] at h1
    exact hj ((Valuation.zero_iff _).1 h1)
  have hc : c j₀ ≠ 0 := fun h => hv (by rw [h, map_zero])
  have hex : ∀ i, ∃ a : O, algebraMap O K a = c i / c j₀ := by
    intro i
    rw [← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (h₀ i) zero_le
  choose d hd using hex
  refine ⟨j₀, d, hc, ?_, fun i => ?_⟩
  · apply IsFractionRing.injective O K
    rw [hd, div_self hc, map_one]
  · rw [hd]; field_simp

/- English proof (translation)
Take `⟨κ, e, he, hsp, hli⟩` from `exists_linearIndependent' (IsLocalRing.ResidueField O) g`. Use `haveI : Finite κ := Finite.of_injective e he`. Use `haveI : Fintype κ := Fintype.ofFinite κ`. Establish `hf : LinearIndependent K (f ∘ e)`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `c hc`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨j, hj⟩` from `hne`. Take `⟨j₀, d, hc₀, hd₀, hd⟩` from `exists_scale (O := O) c j hj`.

Establish `hz : ∑ i, IsLocalRing.residue O (d i) • (g ∘ e) i = 0`. Use function extensionality and compare the values at `b`. Take `⟨a, w, hw⟩` from `h b`. Establish `h1` using `congrFun hc a`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply] at h1 ⊢`.

Establish `h2 : c j₀ * algebraMap O K (∑ i, d i * w (e i)) = 0`. Rewrite using `[← h1, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, (hw (e i)).1, ← mul_assoc, ← hd i]`. Establish `h3 : ∑ i, d i * w (e i) = 0`.

Apply `IsFractionRing.injective O K` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `(mul_eq_zero.1 h2).resolve_left hc₀`. Establish `h4` using `congrArg (IsLocalRing.residue O) h3`. Rewrite `h4` using `[map_sum, map_zero]`.

Rewrite using `[← h4]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, (hw (e i)).2]`. Use `Fintype.linearIndependent_iff.1 hli _ hz j₀` as an intermediate fact. Rewrite `this` using `[hd₀, map_one]`.

Conclude with `one_ne_zero this`. Use `haveI : Module.Finite K (Submodule.span K (Set.range f)) := Module.Finite.span_of_finite K (Set.finite_range f)`. Rewrite using `[← hsp, finrank_span_eq_card hli, ← finrank_span_eq_card hf]`. Conclude with `Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range e f))`.
-/
theorem finrank_span_residue_le {O K I A B : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] [Finite I] (f : I → A → K)
    (g : I → B → IsLocalRing.ResidueField O)
    (h : ∀ b : B, ∃ (a : A) (w : I → O), ∀ i : I,
      f i a = algebraMap O K (w i) ∧ g i b = IsLocalRing.residue O (w i)) :
    Module.finrank (IsLocalRing.ResidueField O)
        (Submodule.span (IsLocalRing.ResidueField O) (Set.range g)) ≤
      Module.finrank K (Submodule.span K (Set.range f)) := by
  classical
  obtain ⟨κ, e, he, hsp, hli⟩ := exists_linearIndependent' (IsLocalRing.ResidueField O) g
  haveI : Finite κ := Finite.of_injective e he
  haveI : Fintype κ := Fintype.ofFinite κ
  have hf : LinearIndependent K (f ∘ e) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    obtain ⟨j, hj⟩ := hne
    obtain ⟨j₀, d, hc₀, hd₀, hd⟩ := exists_scale (O := O) c j hj
    have hz : ∑ i, IsLocalRing.residue O (d i) • (g ∘ e) i = 0 := by
      funext b
      obtain ⟨a, w, hw⟩ := h b
      have h1 := congrFun hc a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply] at h1 ⊢
      have h2 : c j₀ * algebraMap O K (∑ i, d i * w (e i)) = 0 := by
        rw [← h1, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, (hw (e i)).1, ← mul_assoc, ← hd i]
      have h3 : ∑ i, d i * w (e i) = 0 := by
        apply IsFractionRing.injective O K
        rw [map_zero]
        exact (mul_eq_zero.1 h2).resolve_left hc₀
      have h4 := congrArg (IsLocalRing.residue O) h3
      rw [map_sum, map_zero] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, (hw (e i)).2]
    have := Fintype.linearIndependent_iff.1 hli _ hz j₀
    rw [hd₀, map_one] at this
    exact one_ne_zero this
  haveI : Module.Finite K (Submodule.span K (Set.range f)) :=
    Module.Finite.span_of_finite K (Set.finite_range f)
  rw [← hsp, finrank_span_eq_card hli, ← finrank_span_eq_card hf]
  exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range e f))

end GlobalTheory.ResidueSpanScale

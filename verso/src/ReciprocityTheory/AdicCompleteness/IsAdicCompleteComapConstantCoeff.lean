import Mathlib

universe u

open PowerSeries IsLocalRing

noncomputable section

namespace ReciprocityTheory.P1

section Complete

variable {A : Type*} [CommRing A] (I : Ideal A)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Simplify using `using ha`.

Simplify using `[Ideal.span_singleton_le_iff_mem]`. Introduce `f hf`. Rewrite using `[f.eq_X_mul_shift_add_const]`. Conclude with `add_mem (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))) (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))`.
-/
theorem map_C_sup_span_X :
    I.map (C : A →+* A⟦X⟧) ⊔ Ideal.span {X} = I.comap (constantCoeff (R := A)) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using ha
    · simp [Ideal.span_singleton_le_iff_mem]
  · intro f hf
    rw [f.eq_X_mul_shift_add_const]
    exact add_mem
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Proceed by induction on `n generalizing f with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Introduce `hf`.

Rewrite `hf` using `[pow_succ]`. Use `Submodule.mul_induction_on hf (fun a ha b hb i => ?_) (fun a b ha hb i => ?_)` and prove the remaining obligations. Rewrite using `[coeff_mul]`. Use `sum_mem fun x hx => ?_` and prove the remaining obligations. Establish `hx'` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hx`.

Establish `h1` using `ih a ha x.1`. Establish `h2 : coeff x.2 b ∈ I ^ (1 - x.2)`. Break down `Nat.eq_zero_or_pos x.2 with h | h` into its components or cases. Rewrite using `[h]`. Simplify using `using hb`.

Rewrite using `[show 1 - x.2 = 0 by omega]; simp`. Establish `h3` using `Ideal.mul_mem_mul h1 h2`. Rewrite `h3` using `[← pow_add]`. Conclude with `Ideal.pow_le_pow_right (by omega) h3`. Rewrite using `[map_add]`.

Conclude with `add_mem (ha i) (hb i)`. Introduce `h`. Establish `hX : (X : A⟦X⟧) ∈ I.comap (constantCoeff (R` using `A)) := by simp`. Rewrite using `[f.eq_X_pow_mul_shift_add_trunc n]`. Use `add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hX n)) ?_` and prove the remaining obligations.

Rewrite using `[trunc_apply, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]`. Use `sum_mem fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i < n` using `(Finset.mem_Ico.1 hi).2`. Rewrite using `[Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial, monomial_eq_C_mul_X_pow]`. Establish `h1 : C (coeff i f) ∈ I.comap (constantCoeff (R` using `A)) ^ (n - i) := by`.

Use `Ideal.mem_map_of_mem (C : A →+* A⟦X⟧) (h i)` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow]`. Use `Ideal.pow_right_mono ?_ _ this` and prove the remaining obligations. Rewrite using `[← map_C_sup_span_X]`. Conclude with `le_sup_left`.

Establish `h2` using `Ideal.mul_mem_mul h1 (Ideal.pow_mem_pow hX i)`. Rewrite `h2` using `[← pow_add, Nat.sub_add_cancel hi'.le]`. Then use the resulting hypothesis.
-/
theorem mem_pow_comap_constantCoeff_iff (n : ℕ) (f : A⟦X⟧) :
    f ∈ I.comap (constantCoeff (R := A)) ^ n ↔ ∀ i, coeff i f ∈ I ^ (n - i) := by
  constructor
  · induction n generalizing f with
    | zero => simp
    | succ n ih =>
      intro hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf (fun a ha b hb i => ?_) (fun a b ha hb i => ?_)
      · rw [coeff_mul]
        refine sum_mem fun x hx => ?_
        have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
        have h1 := ih a ha x.1
        have h2 : coeff x.2 b ∈ I ^ (1 - x.2) := by
          rcases Nat.eq_zero_or_pos x.2 with h | h
          · rw [h]; simpa using hb
          · rw [show 1 - x.2 = 0 by omega]; simp
        have h3 := Ideal.mul_mem_mul h1 h2
        rw [← pow_add] at h3
        exact Ideal.pow_le_pow_right (by omega) h3
      · rw [map_add]; exact add_mem (ha i) (hb i)
  · intro h
    have hX : (X : A⟦X⟧) ∈ I.comap (constantCoeff (R := A)) := by simp
    rw [f.eq_X_pow_mul_shift_add_trunc n]
    refine add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hX n)) ?_
    rw [trunc_apply, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine sum_mem fun i hi => ?_
    have hi' : i < n := (Finset.mem_Ico.1 hi).2
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial,
      monomial_eq_C_mul_X_pow]
    have h1 : C (coeff i f) ∈ I.comap (constantCoeff (R := A)) ^ (n - i) := by
      have := Ideal.mem_map_of_mem (C : A →+* A⟦X⟧) (h i)
      rw [Ideal.map_pow] at this
      refine Ideal.pow_right_mono ?_ _ this
      rw [← map_C_sup_span_X]; exact le_sup_left
    have h2 := Ideal.mul_mem_mul h1 (Ideal.pow_mem_pow hX i)
    rwa [← pow_add, Nat.sub_add_cancel hi'.le] at h2

/- English proof (translation)
Use extensionality with `i`. Use `IsHausdorff.haus' (I := I) _ fun n => ?_` and prove the remaining obligations. Use `hf (n + i)` as an intermediate fact. Rewrite `this`, the goal using `[SModEq.zero]`. Simplify using `only [smul_eq_mul, Ideal.mul_top] at this ⊢`.

Simplify using `using (mem_pow_comap_constantCoeff_iff I _ f).1 this i`.
-/
theorem isHausdorff_comap_constantCoeff [IsHausdorff I A] :
    IsHausdorff (I.comap (constantCoeff (R := A))) A⟦X⟧ where
  haus' f hf := by
    ext i
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hf (n + i)
    rw [SModEq.zero] at this ⊢
    simp only [smul_eq_mul, Ideal.mul_top] at this ⊢
    simpa using (mem_pow_comap_constantCoeff_iff I _ f).1 this i

/- English proof (translation)
Simplify using `only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_pow_comap_constantCoeff_iff] at hF ⊢`. Establish `: ∀ i, ∃ L : A, ∀ n, coeff i (F (n + i)) - L ∈ I ^ n`. Introduce `i`. Use `IsPrecomplete.prec' (I := I) (fun n => coeff i (F (n + i))) (by` as an intermediate fact. Introduce `m n h`.

Simplify using `only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Simplify using `using hF (show m + i ≤ n + i by omega) i)`. Simplify `this` using `only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Use `choose L hL using this`. Use `⟨mk L, fun n i => ?_⟩` and prove the remaining obligations.

Break down `le_or_gt i n with h | h` into its components or cases. Use `hL i (n - i)` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel h]`. Simplify using `using this`. Rewrite using `[show n - i = 0 by omega]; simp`.
-/
theorem isPrecomplete_comap_constantCoeff [IsPrecomplete I A] :
    IsPrecomplete (I.comap (constantCoeff (R := A))) A⟦X⟧ where
  prec' F hF := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_pow_comap_constantCoeff_iff] at hF ⊢
    have : ∀ i, ∃ L : A, ∀ n, coeff i (F (n + i)) - L ∈ I ^ n := by
      intro i
      have := IsPrecomplete.prec' (I := I) (fun n => coeff i (F (n + i))) (by
        intro m n h
        simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using hF (show m + i ≤ n + i by omega) i)
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using this
    choose L hL using this
    refine ⟨mk L, fun n i => ?_⟩
    rcases le_or_gt i n with h | h
    · have := hL i (n - i)
      rw [Nat.sub_add_cancel h] at this
      simpa using this
    · rw [show n - i = 0 by omega]; simp

/- English proof (translation)
The claim follows from `{ isHausdorff_comap_constantCoeff I, isPrecomplete_comap_constantCoeff I with }`.
-/
theorem isAdicComplete_comap_constantCoeff [IsAdicComplete I A] :
    IsAdicComplete (I.comap (constantCoeff (R := A))) A⟦X⟧ :=
  { isHausdorff_comap_constantCoeff I, isPrecomplete_comap_constantCoeff I with }

end Complete

/- English proof (translation)
Establish `h : maximalIdeal R⟦X⟧ = (maximalIdeal R).comap (constantCoeff (R` using `R)) := by`. Use extensionality with `f`. Rewrite using `[Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_iff_constantCoeff]`. Rewrite using `[h]`. Conclude with `isAdicComplete_comap_constantCoeff _`.
-/
theorem isAdicComplete_ps {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal R⟦X⟧) R⟦X⟧ := by
  have h : maximalIdeal R⟦X⟧ = (maximalIdeal R).comap (constantCoeff (R := R)) := by
    ext f
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_iff_constantCoeff]
  rw [h]
  exact isAdicComplete_comap_constantCoeff _

end ReciprocityTheory.P1

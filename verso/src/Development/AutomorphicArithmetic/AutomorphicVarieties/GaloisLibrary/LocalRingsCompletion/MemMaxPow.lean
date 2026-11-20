import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]`.
-/
private theorem mem_max_iff {O : Type} [CommRing O] [IsLocalRing O] (f : O⟦X⟧) :
    f ∈ maximalIdeal O⟦X⟧ ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]

/- English proof (translation)
Establish `h1 : Ideal.map (C : O →+* O⟦X⟧) (maximalIdeal O) ≤ maximalIdeal O⟦X⟧`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, mem_max_iff]`. Simplify using `using hx`.

Establish `h2` using `Ideal.mem_map_of_mem (C : O →+* O⟦X⟧) ha`. Rewrite `h2` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h1 k h2`.
-/
private theorem C_mem_pow {O : Type} [CommRing O] [IsLocalRing O] (k : ℕ) (a : O)
    (ha : a ∈ maximalIdeal O ^ k) : (C a : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ ^ k := by
  have h1 : Ideal.map (C : O →+* O⟦X⟧) (maximalIdeal O) ≤ maximalIdeal O⟦X⟧ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_max_iff]
    simpa using hx
  have h2 := Ideal.mem_map_of_mem (C : O →+* O⟦X⟧) ha
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 k h2

/- English proof (translation)
Introduce `O _ _ f n`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Proceed by induction on `n generalizing f with`. Consider the case `zero => intro i`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Rewrite `hf` using `[pow_succ]`. Use `Submodule.mul_induction_on hf ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb i`.

Rewrite using `[PowerSeries.coeff_mul]`. Use `Ideal.sum_mem _ ?_` and prove the remaining obligations. Introduce `p hp`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `h1` using `ih a ha p.1`.

Establish `h2 : coeff p.2 b ∈ maximalIdeal O ^ (1 - p.2)`. Break down `Nat.eq_zero_or_pos p.2 with h | h` into its components or cases. Rewrite using `[h, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `using (mem_max_iff b).1 hb`. Rewrite using `[Nat.sub_eq_zero_of_le h]`.

Simplify using the standard rewrite rules. Establish `h3` using `Ideal.mul_mem_mul h1 h2`. Rewrite `h3` using `[← pow_add]`. Conclude with `Ideal.pow_le_pow_right (by omega) h3`. Introduce `x y hx hy i`.

Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ (hx i) (hy i)`. Introduce `h`. Proceed by induction on `n generalizing f with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Rewrite using `[PowerSeries.eq_X_mul_shift_add_const f]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[pow_succ']`. Use `Ideal.mul_mem_mul ?_ ?_` and prove the remaining obligations.

Conclude with `(mem_max_iff X).2 (by simp)`. Apply `ih` to reduce the goal to its premises. Introduce `i`. Rewrite using `[PowerSeries.coeff_mk]`. Use `h (i + 1)` as an intermediate fact.

Simplify using `using this`. Apply `C_mem_pow` to reduce the goal to its premises. Use `h 0` as an intermediate fact. Simplify `this` using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`.
-/
theorem UpperTheory.V.abelian₂.mem_max_pow :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (f : O⟦X⟧) (n : ℕ),
      f ∈ maximalIdeal O⟦X⟧ ^ n ↔ ∀ i, coeff i f ∈ maximalIdeal O ^ (n - i) := by
  intro O _ _ f n
  constructor
  · intro hf
    induction n generalizing f with
    | zero => intro i; simp
    | succ n ih =>
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb i
        rw [PowerSeries.coeff_mul]
        refine Ideal.sum_mem _ ?_
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        have h1 := ih a ha p.1
        have h2 : coeff p.2 b ∈ maximalIdeal O ^ (1 - p.2) := by
          rcases Nat.eq_zero_or_pos p.2 with h | h
          · rw [h, PowerSeries.coeff_zero_eq_constantCoeff_apply]
            simpa using (mem_max_iff b).1 hb
          · rw [Nat.sub_eq_zero_of_le h]
            simp
        have h3 := Ideal.mul_mem_mul h1 h2
        rw [← pow_add] at h3
        exact Ideal.pow_le_pow_right (by omega) h3
      · intro x y hx hy i
        rw [map_add]
        exact Ideal.add_mem _ (hx i) (hy i)
  · intro h
    induction n generalizing f with
    | zero => simp
    | succ n ih =>
      rw [PowerSeries.eq_X_mul_shift_add_const f]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ']
        refine Ideal.mul_mem_mul ?_ ?_
        · exact (mem_max_iff X).2 (by simp)
        · apply ih
          intro i
          rw [PowerSeries.coeff_mk]
          have := h (i + 1)
          simpa using this
      · apply C_mem_pow
        have := h 0
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using this

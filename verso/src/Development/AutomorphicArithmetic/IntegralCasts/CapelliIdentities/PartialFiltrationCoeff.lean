import Mathlib

/- English proof (translation)
Introduce `O σ _ _ M`. Proceed by induction on `M with`. Consider the case `zero`. Introduce `f _ n`. Simplify using the standard rewrite rules.

Consider the case `succ M ih`. Introduce `f hf`. Rewrite `hf` using `[pow_succ]`. Use `Submodule.mul_induction_on hf ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb n`.

Rewrite using `[MvPowerSeries.coeff_mul]`. Use `Ideal.sum_mem _ ?_` and prove the remaining obligations. Introduce and unpack `⟨p, q⟩ hpq`. Establish `hsum : p + q = n` using `by simpa using hpq`. Establish `hdeg : Finsupp.degree p + Finsupp.degree q = Finsupp.degree n`.

Rewrite using `[← hsum, map_add]`. Establish `hp` using `ih a ha p`. Distinguish the cases in `hq : q = 0`. Substitute `hq` using the available equality. Establish `hb0 : MvPowerSeries.coeff (0 : σ →₀ ℕ) b ∈ IsLocalRing.maximalIdeal O`.

Rewrite `hb`, the goal using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Conclude with `hb (MvPowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hu))`. Establish `hmul` using `Ideal.mul_mem_mul hp hb0`. Rewrite `hmul` using `[← pow_succ]`.

Conclude with `Ideal.pow_le_pow_right (by omega) hmul`. Establish `hq' : Finsupp.degree q ≠ 0` using `fun h => hq ((Finsupp.degree_eq_zero_iff q).mp h)`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) hp)`. Introduce `x y hx hy n`. Rewrite using `[map_add]`.

Conclude with `Ideal.add_mem _ (hx n) (hy n)`.
-/
theorem UpperTheory.Reformulated.B.PartialFiltrationCoeff.part_filt_coeff :
    ∀ {O σ : Type} [inst : CommRing O]
    [inst_1 : IsLocalRing O] (M : ℕ),
    ∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ M,
      ∀ (n : σ →₀ ℕ),
        (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f ∈
          IsLocalRing.maximalIdeal O ^ (M - (Finsupp.degree : (σ →₀ ℕ) → ℕ) n) := by
  intro O σ _ _ M
  classical
  induction M with
  | zero =>
    intro f _ n
    simp
  | succ M ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb n
      rw [MvPowerSeries.coeff_mul]
      refine Ideal.sum_mem _ ?_
      rintro ⟨p, q⟩ hpq
      have hsum : p + q = n := by simpa using hpq
      have hdeg : Finsupp.degree p + Finsupp.degree q = Finsupp.degree n := by
        rw [← hsum, map_add]
      have hp := ih a ha p
      by_cases hq : q = 0
      · subst hq
        have hb0 : MvPowerSeries.coeff (0 : σ →₀ ℕ) b ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
          intro hu
          exact hb (MvPowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hu))
        have hmul := Ideal.mul_mem_mul hp hb0
        rw [← pow_succ] at hmul
        exact Ideal.pow_le_pow_right (by omega) hmul
      · have hq' : Finsupp.degree q ≠ 0 := fun h => hq ((Finsupp.degree_eq_zero_iff q).mp h)
        exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) hp)
    · intro x y hx hy n
      rw [map_add]
      exact Ideal.add_mem _ (hx n) (hy n)

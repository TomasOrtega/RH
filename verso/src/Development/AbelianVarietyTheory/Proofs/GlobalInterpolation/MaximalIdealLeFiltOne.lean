import Mathlib

namespace GlobalTheory.MaximalIdealFiltration

open MvPowerSeries

variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

def filt (N : ℕ) : Ideal (MvPowerSeries (Fin a) O) where
  carrier := {f | ∀ m : Fin a →₀ ℕ, coeff m f ∈ IsLocalRing.maximalIdeal O ^ (N - m.degree)}
  add_mem' := by
    intro f g hf hg m
    simp only [Set.mem_setOf_eq, map_add] at *
    exact Ideal.add_mem _ (hf m) (hg m)
  zero_mem' := by
    intro m
    simp
  smul_mem' := by
    intro c f hf m
    simp only [Set.mem_setOf_eq, smul_eq_mul, coeff_mul] at *
    refine Ideal.sum_mem _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    refine Ideal.mul_mem_left _ _ ?_
    refine Ideal.pow_le_pow_right ?_ (hf p.2)
    have : p.2.degree ≤ m.degree := by
      rw [← hp, map_add]; omega
    omega

/- English proof (translation)
Introduce `m`. Simplify using `only [coeff_mul]`. Use `Ideal.sum_mem _ fun p hp => ?_` and prove the remaining obligations. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `h1` using `hf p.1`.

Establish `h2` using `hg p.2`. Establish `hm` using `Ideal.mul_mem_mul h1 h2`. Rewrite `hm` using `[← pow_add]`. Use `Ideal.pow_le_pow_right ?_ hm` and prove the remaining obligations. Establish `: m.degree = p.1.degree + p.2.degree` using `by rw [← hp, map_add]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem mul_mem_filt {k l : ℕ} {f g : MvPowerSeries (Fin a) O}
    (hf : f ∈ filt (O := O) k) (hg : g ∈ filt (O := O) l) : f * g ∈ filt (O := O) (k + l) := by
  intro m
  simp only [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 := hf p.1
  have h2 := hg p.2
  have hm := Ideal.mul_mem_mul h1 h2
  rw [← pow_add] at hm
  refine Ideal.pow_le_pow_right ?_ hm
  have : m.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
  omega

/- English proof (translation)
Introduce `f hf m`. Distinguish the cases in `h0 : m = 0`. Substitute `h0` using the available equality. Simplify using `only [map_zero, Nat.sub_zero, pow_one]`. Rewrite `hf`, the goal using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Introduce `hu`. Apply `hf` to reduce the goal to its premises. Rewrite using `[MvPowerSeries.isUnit_iff_constantCoeff]`. Simplify `hu` using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Establish `: 1 ≤ m.degree`.

Rewrite using `[Nat.one_le_iff_ne_zero]`. Introduce `h`. Conclude with `h0 ((Finsupp.degree_eq_zero_iff m).1 h)`. Establish `: 1 - m.degree = 0` using `by omega`. Rewrite using `[this, pow_zero, Ideal.one_eq_top]`.

Conclude with `Submodule.mem_top`.
-/
theorem maximalIdeal_le_filt_one :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ≤ filt (O := O) 1 := by
  intro f hf m
  by_cases h0 : m = 0
  · subst h0
    simp only [map_zero, Nat.sub_zero, pow_one]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf ⊢
    intro hu
    apply hf
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hu
  · have : 1 ≤ m.degree := by
      rw [Nat.one_le_iff_ne_zero]
      intro h
      exact h0 ((Finsupp.degree_eq_zero_iff m).1 h)
    have : 1 - m.degree = 0 := by omega
    rw [this, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Introduce `f _ m`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Rewrite using `[pow_succ, Ideal.mul_le]`. Introduce `r hr s hs`. Conclude with `mul_mem_filt (ih hr) (maximalIdeal_le_filt_one hs)`.
-/
theorem maximalIdeal_pow_le_filt (N : ℕ) :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N ≤ filt (O := O) N := by
  induction N with
  | zero =>
    intro f _ m
    simp
  | succ n ih =>
    rw [pow_succ, Ideal.mul_le]
    intro r hr s hs
    exact mul_mem_filt (ih hr) (maximalIdeal_le_filt_one hs)

/- English proof (translation)
Introduce `O _ _ a N f hf m`. Conclude with `maximalIdeal_pow_le_filt N hf m`.
-/
theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ} (N : ℕ), ∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N, ∀ (m : Fin a →₀ ℕ), (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f ∈ IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m) := by
  intro O _ _ a N f hf m
  exact maximalIdeal_pow_le_filt N hf m

end GlobalTheory.MaximalIdealFiltration

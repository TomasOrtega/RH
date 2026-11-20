import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section ChartLoc

variable {Ω : Type*} [Field Ω] {τ : Type*} (x : τ → Ω) (i : τ)

/- English proof (translation)
The claim follows from `intCast_mem _ z`.
-/
theorem intCast_mem_chartRing (R : Type*) [CommRing R] [Algebra R Ω] (z : ℤ) :
    (z : Ω) ∈ chartRing R x i :=
  intCast_mem _ z

/- English proof (translation)
Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy => exact Algebra.subset_adjoin hy`. Consider the case `algebraMap z => simp [intCast_mem_chartRing x i R z]`. Consider the case `add y z _ _ hy hz => exact add_mem hy hz`. Consider the case `mul y z _ _ hy hz => exact mul_mem hy hz`.
-/
theorem mem_chartRing_of_int (R : Type*) [CommRing R] [Algebra R Ω] {y : Ω}
    (hy : y ∈ chartRing ℤ x i) : y ∈ chartRing R x i := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap z => simp [intCast_mem_chartRing x i R z]
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

variable (R : Type*) [CommRing R] [Algebra ℤ R] (T : Submonoid ℤ) [IsLocalization T R] [Algebra R Ω]

omit [IsLocalization T R] in
/- English proof (translation)
Rewrite using `[eq_intCast (algebraMap ℤ R), map_intCast]`.
-/
theorem algebraMap_algebraMap_int (z : ℤ) : algebraMap R Ω (algebraMap ℤ R z) = z := by
  rw [eq_intCast (algebraMap ℤ R), map_intCast]

/- English proof (translation)
Take `⟨u, hu⟩` from `IsLocalization.map_units R (⟨t, ht⟩ : T)`. Establish `h1 : algebraMap R Ω (↑u⁻¹ : R) * (t : Ω) = 1`. Rewrite using `[← algebraMap_algebraMap_int R t]`. Establish `: algebraMap ℤ R t = (u : R)` using `hu.symm`. Rewrite using `[this, ← map_mul, Units.inv_mul, map_one]`.

Establish `ht0 : (t : Ω) ≠ 0`. Introduce `h`. Rewrite `h1` using `[h, mul_zero]`. Conclude with `zero_ne_one h1`. Use `⟨ht0, ?_⟩` and prove the remaining obligations.

Rewrite using `[← eq_inv_of_mul_eq_one_left h1]`. Conclude with `Subalgebra.algebraMap_mem _ _`.
-/
theorem inv_mem_chartRing_loc {t : ℤ} (ht : t ∈ T) :
    (t : Ω) ≠ 0 ∧ (t : Ω)⁻¹ ∈ chartRing R x i := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units R (⟨t, ht⟩ : T)
  have h1 : algebraMap R Ω (↑u⁻¹ : R) * (t : Ω) = 1 := by
    rw [← algebraMap_algebraMap_int R t]
    have : algebraMap ℤ R t = (u : R) := hu.symm
    rw [this, ← map_mul, Units.inv_mul, map_one]
  have ht0 : (t : Ω) ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  refine ⟨ht0, ?_⟩
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact Subalgebra.algebraMap_mem _ _

/- English proof (translation)
Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy => exact ⟨1, one_mem T, by rw [Int.cast_one, one_mul]; exact Algebra.subset_adjoin hy⟩`. Consider the case `algebraMap r`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective T r`. Use `⟨s, s.2, ?_⟩` and prove the remaining obligations.

Establish `h` using `congrArg (algebraMap R Ω) (IsLocalization.mk'_spec R a s)`. Rewrite `h` using `[map_mul, algebraMap_algebraMap_int, algebraMap_algebraMap_int]`. Rewrite using `[mul_comm, h]`. Conclude with `intCast_mem_chartRing x i ℤ a`. Consider the case `add y z _ _ hy hz`.

Take `⟨t, ht, hty⟩` from `hy`. Take `⟨t', ht', htz⟩` from `hz`. Use `⟨t * t', mul_mem ht ht', ?_⟩` and prove the remaining obligations. Establish `: ((t * t' : ℤ) : Ω) * (y + z) = (t' : Ω) * ((t : Ω) * y) + (t : Ω) * ((t' : Ω) * z)` using `by push_cast; ring`. Rewrite using `[this]`.

Conclude with `add_mem (mul_mem (intCast_mem_chartRing x i ℤ _) hty) (mul_mem (intCast_mem_chartRing x i ℤ _) htz)`. Consider the case `mul y z _ _ hy hz`. Take `⟨t, ht, hty⟩` from `hy`. Take `⟨t', ht', htz⟩` from `hz`. Use `⟨t * t', mul_mem ht ht', ?_⟩` and prove the remaining obligations.

Establish `: ((t * t' : ℤ) : Ω) * (y * z) = ((t : Ω) * y) * ((t' : Ω) * z)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `mul_mem hty htz`.
-/
theorem exists_mul_mem_chartRing_int {y : Ω} (hy : y ∈ chartRing R x i) :
    ∃ t ∈ T, (t : Ω) * y ∈ chartRing ℤ x i := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact ⟨1, one_mem T, by rw [Int.cast_one, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap r =>
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective T r
    refine ⟨s, s.2, ?_⟩
    have h := congrArg (algebraMap R Ω) (IsLocalization.mk'_spec R a s)
    rw [map_mul, algebraMap_algebraMap_int, algebraMap_algebraMap_int] at h
    rw [mul_comm, h]
    exact intCast_mem_chartRing x i ℤ a
  | add y z _ _ hy hz =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨t', ht', htz⟩ := hz
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : ((t * t' : ℤ) : Ω) * (y + z) = (t' : Ω) * ((t : Ω) * y) + (t : Ω) * ((t' : Ω) * z) := by
      push_cast; ring
    rw [this]
    exact add_mem (mul_mem (intCast_mem_chartRing x i ℤ _) hty)
      (mul_mem (intCast_mem_chartRing x i ℤ _) htz)
  | mul y z _ _ hy hz =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨t', ht', htz⟩ := hz
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : ((t * t' : ℤ) : Ω) * (y * z) = ((t : Ω) * y) * ((t' : Ω) * z) := by
      push_cast; ring
    rw [this]
    exact mul_mem hty htz

/- English proof (translation)
Use `choose t ht hty using fun l => exists_mul_mem_chartRing_int x i R T (hy l)`. Use `⟨∏ l, t l, prod_mem fun l _ => ht l, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ l), Int.cast_mul, mul_comm (t l : Ω), mul_assoc]`. Conclude with `mul_mem (intCast_mem_chartRing x i ℤ _) (hty l)`.
-/
theorem exists_mul_mem_chartRing_int_fin {ι : Type*} [Fintype ι] (y : ι → Ω)
    (hy : ∀ l, y l ∈ chartRing R x i) :
    ∃ t ∈ T, ∀ l, (t : Ω) * y l ∈ chartRing ℤ x i := by
  classical
  choose t ht hty using fun l => exists_mul_mem_chartRing_int x i R T (hy l)
  refine ⟨∏ l, t l, prod_mem fun l _ => ht l, fun l => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ l), Int.cast_mul, mul_comm (t l : Ω),
    mul_assoc]
  exact mul_mem (intCast_mem_chartRing x i ℤ _) (hty l)

end ChartLoc

/- English proof (translation)
Introduce `hsQ`. Establish `hcop : IsCoprime (p : ℤ) s`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Establish `: ¬ p ∣ s.natAbs` using `fun h => hs (Int.natCast_dvd.mpr h)`. Simplify `(Nat.Prime.coprime_iff_not_dvd hp).mpr this` using `[Int.gcd]`.

Take `⟨u, v, huv⟩` from `hcop`. Establish `h1` using `congrArg (Int.cast : ℤ → A) huv`. Move the coercions through the operations in `at h1`. Apply `hQ` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← h1]`.

Conclude with `add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hsQ)`.
-/
theorem intCast_not_mem_of_not_dvd {A : Type*} [CommRing A] {Q : Ideal A} (hQ : Q ≠ ⊤) {p : ℕ}
    (hp : p.Prime) (hpQ : (p : A) ∈ Q) {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) : (s : A) ∉ Q := by
  intro hsQ
  have hcop : IsCoprime (p : ℤ) s := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : ¬ p ∣ s.natAbs := fun h => hs (Int.natCast_dvd.mpr h)
    simpa [Int.gcd] using (Nat.Prime.coprime_iff_not_dvd hp).mpr this
  obtain ⟨u, v, huv⟩ := hcop
  have h1 := congrArg (Int.cast : ℤ → A) huv
  push_cast at h1
  apply hQ
  rw [Ideal.eq_top_iff_one, ← h1]
  exact add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hsQ)

end GroundTheory.Heights₂.Heights.Model

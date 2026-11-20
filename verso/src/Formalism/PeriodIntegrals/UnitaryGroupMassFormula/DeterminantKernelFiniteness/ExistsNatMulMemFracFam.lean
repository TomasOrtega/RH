import Mathlib
import Formalism.PeriodIntegrals.KerIso

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerDetFinW

open PI.KerIso

/- English proof (translation)
Assemble the required witnesses or components as `⟨N, map_natCast _ _⟩`.
-/
lemma natCast_mem_int {K : Type} [Field K] [NumberField K] (N : ℕ) :
    (N : K) ∈ (algebraMap (𝓞 K) K).range :=
  ⟨N, map_natCast _ _⟩

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `(IsFractionRing.isAlgebraic_iff ℤ ℚ K |>.mpr (.of_finite ℚ x)).exists_integral_multiple`. Establish `h1 : (y : K) * x ∈ (algebraMap (𝓞 K) K).range`. Use `⟨⟨y • x, hy⟩, ?_⟩` and prove the remaining obligations. Use `show y • x = _`. Rewrite using `[zsmul_eq_mul]`.

Use `⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq y with h | h` into its components or cases. Establish `: ((y.natAbs : ℕ) : K) = (y : K)` using `by conv_rhs => rw [h]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `h1`. Establish `: ((y.natAbs : ℕ) : K) = -(y : K)` using `by conv_rhs => rw [h]`. Simplify using the standard rewrite rules. Rewrite using `[this, neg_mul]`. Conclude with `neg_mem h1`.
-/
lemma exists_nat_mul_mem_int {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ d : ℕ, 0 < d ∧ (d : K) * x ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨y, hy0, hy⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ K |>.mpr (.of_finite ℚ x)).exists_integral_multiple
  have h1 : (y : K) * x ∈ (algebraMap (𝓞 K) K).range := by
    refine ⟨⟨y • x, hy⟩, ?_⟩
    show y • x = _
    rw [zsmul_eq_mul]
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : K) = (y : K) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact h1
  · have : ((y.natAbs : ℕ) : K) = -(y : K) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact neg_mem h1

/- English proof (translation)
Use `choose d hd0 hd using fun i => exists_nat_mul_mem_int (f i)`. Use `⟨∏ i, d i, Finset.prod_pos fun i _ => hd0 i, fun i => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem d (Finset.mem_univ i)`. Rewrite using `[hc, Nat.cast_mul, mul_comm (d i : K), mul_assoc]`. Conclude with `mul_mem (natCast_mem_int c) (hd i)`.
-/
lemma exists_nat_mul_mem_int_fam {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    (f : ι → K) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : K) * f i ∈ (algebraMap (𝓞 K) K).range := by
  choose d hd0 hd using fun i => exists_nat_mul_mem_int (f i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd0 i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (d i : K), mul_assoc]
  exact mul_mem (natCast_mem_int c) (hd i)

/- English proof (translation)
Take `⟨z, rfl⟩` from `hk`. Establish `hz : IsIntegral ℤ (algebraMap K E (algebraMap (𝓞 K) K z))` using `(RingOfIntegers.isIntegral_coe z).map (algebraMap K E).toIntAlgHom`. Use `(I : Submodule (𝓞 E) E).smul_mem (⟨_, hz⟩ : 𝓞 E) hy` as an intermediate fact. Establish `e : ((⟨_, hz⟩ : 𝓞 E) • y) = algebraMap K E (algebraMap (𝓞 K) K z) * y` using `Algebra.smul_def _ _`. Rewrite using `[← FractionalIdeal.mem_coe]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Conclude with `e.symm`.
-/
lemma int_mul_mem {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {k : K} (hk : k ∈ (algebraMap (𝓞 K) K).range)
    {y : E} (hy : y ∈ I) : algebraMap K E k * y ∈ I := by
  obtain ⟨z, rfl⟩ := hk
  have hz : IsIntegral ℤ (algebraMap K E (algebraMap (𝓞 K) K z)) :=
    (RingOfIntegers.isIntegral_coe z).map (algebraMap K E).toIntAlgHom
  have := (I : Submodule (𝓞 E) E).smul_mem (⟨_, hz⟩ : 𝓞 E) hy
  have e : ((⟨_, hz⟩ : 𝓞 E) • y) = algebraMap K E (algebraMap (𝓞 K) K z) * y := Algebra.smul_def _ _
  rw [← FractionalIdeal.mem_coe]
  convert this using 1
  exact e.symm

/- English proof (translation)
Use `(I : Submodule (𝓞 E) E).smul_mem (c : 𝓞 E) hy` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def, map_natCast]`. Conclude with `this`.
-/
lemma nat_mul_mem {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (c : ℕ) {y : E} (hy : y ∈ I) :
    (c : E) * y ∈ I := by
  have := (I : Submodule (𝓞 E) E).smul_mem (c : 𝓞 E) hy
  rw [Algebra.smul_def, map_natCast] at this
  exact this

/- English proof (translation)
Establish `hbot : (I : Submodule (𝓞 E) E) ≠ ⊥` using `fun h => hI (FractionalIdeal.coeToSubmodule_eq_bot.1 h)`. Take `⟨a, haI, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`. Take `⟨d, hd0, z, hz⟩` from `exists_nat_mul_mem_int (y / a)`. Use `⟨d, hd0, ?_⟩` and prove the remaining obligations. Establish `hmem` using `(I : Submodule (𝓞 E) E).smul_mem z haI`.

Rewrite `hmem` using `[Algebra.smul_def, hz]`. Establish `: (d : E) * (y / a) * a = (d : E) * y` using `by field_simp`. Rewrite `hmem` using `[this]`. Conclude with `hmem`.
-/
lemma exists_nat_mul_mem_frac {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (y : E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) * y ∈ I := by
  have hbot : (I : Submodule (𝓞 E) E) ≠ ⊥ := fun h => hI (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨d, hd0, z, hz⟩ := exists_nat_mul_mem_int (y / a)
  refine ⟨d, hd0, ?_⟩
  have hmem := (I : Submodule (𝓞 E) E).smul_mem z haI
  rw [Algebra.smul_def, hz] at hmem
  have : (d : E) * (y / a) * a = (d : E) * y := by field_simp
  rw [this] at hmem
  exact hmem

/- English proof (translation)
Use `choose d hd0 hd using fun i => exists_nat_mul_mem_frac I hI (f i)`. Use `⟨∏ i, d i, Finset.prod_pos fun i _ => hd0 i, fun i => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem d (Finset.mem_univ i)`. Rewrite using `[hc, Nat.cast_mul, mul_comm (d i : E), mul_assoc]`. Conclude with `nat_mul_mem I c (hd i)`.
-/
lemma exists_nat_mul_mem_frac_fam {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) {ι : Type} [Fintype ι]
    (f : ι → E) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : E) * f i ∈ I := by
  choose d hd0 hd using fun i => exists_nat_mul_mem_frac I hI (f i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd0 i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (d i : E), mul_assoc]
  exact nat_mul_mem I c (hd i)

end PI.KerDetFinW

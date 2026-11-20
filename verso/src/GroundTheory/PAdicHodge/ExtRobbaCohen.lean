import Mathlib
import GroundTheory.PAdicHodge.PerfectoidField
import GroundTheory.PAdicHodge.WittLift
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open IsLocalRing WittVector Ideal

section Integers

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/- English proof (translation)
The claim follows from `mem_normInteger.1 x.2`.
-/
theorem norm_coe_integer_le_one (x : normInteger K) : ‖(x : K)‖ ≤ 1 := mem_normInteger.1 x.2

/- English proof (translation)
Rewrite using `[(normInteger_integers (K := K)).isUnit_iff_valuation_eq_one]`. Establish `hx : algebraMap (normInteger K) K x = (x : K)` using `rfl`. Simplify using `only [NormedField.valuation_apply, hx]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `congrArg NNReal.toReal h` as an intermediate fact. Simplify using `using this`. Introduce `h`. Use `ext`. Simplify using `using h`.
-/
theorem isUnit_integer_iff_norm_eq_one {x : normInteger K} : IsUnit x ↔ ‖(x : K)‖ = 1 := by
  rw [(normInteger_integers (K := K)).isUnit_iff_valuation_eq_one]
  have hx : algebraMap (normInteger K) K x = (x : K) := rfl
  simp only [NormedField.valuation_apply, hx]
  constructor
  · intro h
    have := congrArg NNReal.toReal h
    simpa using this
  · intro h
    ext
    simpa using h

variable [IsDiscreteValuationRing (normInteger K)]

/- English proof (translation)
Rewrite using `[residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_iff_norm_eq_one]`. Conclude with `⟨fun h => lt_of_le_of_ne (norm_coe_integer_le_one x) h, fun h => h.ne⟩`.
-/
theorem residue_eq_zero_iff_norm_lt_one {x : normInteger K} :
    residue (normInteger K) x = 0 ↔ ‖(x : K)‖ < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_iff_norm_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (norm_coe_integer_le_one x) h, fun h => h.ne⟩

variable {ϖ : normInteger K} (hϖ : Irreducible ϖ)
include hϖ

/- English proof (translation)
The claim follows from `lt_of_le_of_ne (norm_coe_integer_le_one ϖ) fun h => hϖ.not_isUnit (isUnit_integer_iff_norm_eq_one.2 h)`.
-/
theorem norm_unif_lt_one : ‖(ϖ : K)‖ < 1 :=
  lt_of_le_of_ne (norm_coe_integer_le_one ϖ) fun h =>
    hϖ.not_isUnit (isUnit_integer_iff_norm_eq_one.2 h)

/- English proof (translation)
Establish `: (ϖ : K) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Conclude with `norm_pos_iff.2 this`.
-/
theorem norm_unif_pos : 0 < ‖(ϖ : K)‖ := by
  have : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  exact norm_pos_iff.2 this

/- English proof (translation)
Establish `hm : x ∈ maximalIdeal (normInteger K)`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_iff_norm_eq_one]`. Conclude with `hx.ne`. Rewrite `hm` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, mem_span_singleton']`. Take `⟨y, rfl⟩` from `hm`.

Simplify using `only [Subring.coe_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_le_norm_unif_of_lt_one {x : normInteger K} (hx : ‖(x : K)‖ < 1) :
    ‖(x : K)‖ ≤ ‖(ϖ : K)‖ := by
  have hm : x ∈ maximalIdeal (normInteger K) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_iff_norm_eq_one]; exact hx.ne
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, mem_span_singleton'] at hm
  obtain ⟨y, rfl⟩ := hm
  simp only [Subring.coe_mul, norm_mul]
  calc ‖(y : K)‖ * ‖(ϖ : K)‖ ≤ 1 * ‖(ϖ : K)‖ := by
        gcongr; exact norm_coe_integer_le_one y
    _ = _ := one_mul _

/- English proof (translation)
Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hx hϖ`. Use `⟨n, ?_⟩` and prove the remaining obligations. Use `congrArg (fun z : normInteger K => ‖(z : K)‖) hu` as an intermediate fact. Simplify using `only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow] at this`. Rewrite `this` using `[isUnit_integer_iff_norm_eq_one.1 u.isUnit, mul_one]`. Then use the resulting hypothesis.
-/
theorem exists_norm_eq_pow {x : normInteger K} (hx : x ≠ 0) : ∃ n : ℕ, ‖(x : K)‖ = ‖(ϖ : K)‖ ^ n := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
  refine ⟨n, ?_⟩
  have := congrArg (fun z : normInteger K => ‖(z : K)‖) hu
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow] at this
  rwa [isUnit_integer_iff_norm_eq_one.1 u.isUnit, mul_one] at this

/- English proof (translation)
Rewrite using `[← span_singleton_pow, mem_span_singleton_pow_iff]`.
-/
theorem mem_span_unif_pow_iff {x : normInteger K} (n : ℕ) :
    x ∈ span {ϖ ^ n} ↔ ‖(x : K)‖ ≤ ‖(ϖ : K)‖ ^ n := by
  rw [← span_singleton_pow, mem_span_singleton_pow_iff]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Take `⟨m, hm⟩` from `exists_norm_eq_pow hϖ hx`. Rewrite `h`, the goal using `[hm]`. Establish `h1` using `norm_unif_lt_one hϖ`.

Establish `h0` using `norm_unif_pos hϖ`. Establish `: n < m`. Assume the negation of the conclusion as `hnm`. Use `replace hnm := not_lt.1 hnm`. Conclude with `absurd h (not_lt.2 (pow_le_pow_of_le_one h0.le h1.le hnm))`.

Conclude with `pow_le_pow_of_le_one h0.le h1.le this`.
-/
theorem norm_le_pow_succ_of_lt {x : normInteger K} {n : ℕ} (h : ‖(x : K)‖ < ‖(ϖ : K)‖ ^ n) :
    ‖(x : K)‖ ≤ ‖(ϖ : K)‖ ^ (n + 1) := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, hm⟩ := exists_norm_eq_pow hϖ hx
  rw [hm] at h ⊢
  have h1 := norm_unif_lt_one hϖ
  have h0 := norm_unif_pos hϖ
  have : n < m := by
    by_contra hnm
    replace hnm := not_lt.1 hnm
    exact absurd h (not_lt.2 (pow_le_pow_of_le_one h0.le h1.le hnm))
  exact pow_le_pow_of_le_one h0.le h1.le this

end Integers

section PowCongr

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/- English proof (translation)
Rewrite using `[← geom_sum₂_mul, norm_mul]`. Establish `hs : ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖ ≤ 1`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow, norm_pow]`. Conclude with `mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hx) (by positivity) (pow_le_one₀ (norm_nonneg _) hy)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_pow_sub_pow_le_of_le_one {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  have hs : ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hx) (by positivity)
      (pow_le_one₀ (norm_nonneg _) hy)
  calc _ ≤ 1 * ‖x - y‖ := by gcongr
    _ = _ := one_mul _

/- English proof (translation)
Rewrite using `[← geom_sum₂_mul, norm_mul]`. Establish `hxy : ‖x - y‖ ≤ c` using `h.trans (by simpa using pow_le_pow_of_le_one hc0 hc1 hj)`. Establish `hs : ‖∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)‖ ≤ c`. Establish `: ∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i) = ∑ i ∈ Finset.range p, (x ^ i - y ^ i) * y ^ (p - 1 - i) + (p : K) * y ^ (p - 1)`. Establish `h2 : ∀ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i) = (x ^ i - y ^ i) * y ^ (p - 1 - i) + y ^ (p - 1)`.

Introduce `i hi`. Establish `hi' : i ≤ p - 1` using `by rw [Finset.mem_range] at hi; omega`. Rewrite using `[sub_mul, ← pow_add, Nat.add_sub_cancel' hi']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl h2, Finset.sum_add_distrib]`.

Simplify using `[Finset.card_range, nsmul_eq_mul]`. Rewrite using `[this]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc0 fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(norm_pow_sub_pow_le_of_le_one hx hy i).trans hxy`. Conclude with `pow_le_one₀ (norm_nonneg _) hy`. Use `_ = c := mul_one c`. Rewrite using `[norm_mul, norm_pow]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_one₀ (norm_nonneg _) hy`. Use `_ = c := mul_one c`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_pow_prime_sub_le {p : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hp : ‖(p : K)‖ ≤ c) {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) {j : ℕ} (hj : 1 ≤ j) (h : ‖x - y‖ ≤ c ^ j) (hc1 : c ≤ 1) :
    ‖x ^ p - y ^ p‖ ≤ c ^ (j + 1) := by
  rw [← geom_sum₂_mul, norm_mul]
  have hxy : ‖x - y‖ ≤ c := h.trans (by simpa using pow_le_pow_of_le_one hc0 hc1 hj)
  have hs : ‖∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)‖ ≤ c := by
    have : ∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i) =
        ∑ i ∈ Finset.range p, (x ^ i - y ^ i) * y ^ (p - 1 - i) + (p : K) * y ^ (p - 1) := by
      have h2 : ∀ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i) =
          (x ^ i - y ^ i) * y ^ (p - 1 - i) + y ^ (p - 1) := by
        intro i hi
        have hi' : i ≤ p - 1 := by rw [Finset.mem_range] at hi; omega
        rw [sub_mul, ← pow_add, Nat.add_sub_cancel' hi']; ring
      rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
      simp [Finset.card_range, nsmul_eq_mul]
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc0 fun i _ => ?_
      rw [norm_mul, norm_pow]
      calc ‖x ^ i - y ^ i‖ * ‖y‖ ^ (p - 1 - i) ≤ c * 1 := by
            gcongr
            · exact (norm_pow_sub_pow_le_of_le_one hx hy i).trans hxy
            · exact pow_le_one₀ (norm_nonneg _) hy
        _ = c := mul_one c
    · rw [norm_mul, norm_pow]
      calc ‖(p : K)‖ * ‖y‖ ^ (p - 1) ≤ c * 1 := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) hy
        _ = c := mul_one c
  calc _ ≤ c * c ^ j := by gcongr
    _ = c ^ (j + 1) := by ring

end PowCongr

section Residue

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [IsDiscreteValuationRing (normInteger K)]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]

/- English proof (translation)
Rewrite using `[map_natCast]`. Conclude with `CharP.cast_eq_zero _ p`.
-/
theorem residue_natCast_prime : residue (normInteger K) (p : normInteger K) = 0 := by
  rw [map_natCast]; exact CharP.cast_eq_zero _ p

/- English proof (translation)
The claim follows from `residue_eq_zero_iff_norm_lt_one.1 (residue_natCast_prime p)`.
-/
theorem norm_natCast_prime_lt_one : ‖((p : normInteger K) : K)‖ < 1 :=
  residue_eq_zero_iff_norm_lt_one.1 (residue_natCast_prime p)

instance fact_not_isUnit_natCast_prime : Fact (¬ IsUnit (p : normInteger K)) :=
  ⟨fun h => (norm_natCast_prime_lt_one (K := K) p).ne (isUnit_integer_iff_norm_eq_one.1 h)⟩

instance isAdicComplete_natCast_prime [CompleteSpace K] :
    IsAdicComplete (span {(p : normInteger K)}) (normInteger K) :=
  isAdicComplete_span_singleton (norm_natCast_prime_lt_one p)

/- English proof (translation)
The claim follows from `norm_le_norm_unif_of_lt_one hϖ (norm_natCast_prime_lt_one p)`.
-/
theorem norm_natCast_prime_le_unif {ϖ : normInteger K} (hϖ : Irreducible ϖ) :
    ‖((p : normInteger K) : K)‖ ≤ ‖(ϖ : K)‖ :=
  norm_le_norm_unif_of_lt_one hϖ (norm_natCast_prime_lt_one p)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using h`. Consider the case `succ m ih`. Rewrite using `[pow_succ, pow_mul, pow_mul, ← add_assoc]`. Establish `hc` using `norm_natCast_prime_le_unif (K := K) p hϖ`.

Establish `hpK : ‖(p : K)‖ ≤ ‖(ϖ : K)‖` using `by simpa using hc`. Conclude with `norm_pow_prime_sub_le (norm_nonneg _) hpK (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy) (by omega) ih (norm_unif_lt_one hϖ).le`.
-/
theorem norm_pow_prime_pow_sub_le {ϖ : normInteger K} (hϖ : Irreducible ϖ) {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) {j : ℕ} (hj : 1 ≤ j) (h : ‖x - y‖ ≤ ‖(ϖ : K)‖ ^ j) (m : ℕ) :
    ‖x ^ p ^ m - y ^ p ^ m‖ ≤ ‖(ϖ : K)‖ ^ (j + m) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    rw [pow_succ, pow_mul, pow_mul, ← add_assoc]
    have hc := norm_natCast_prime_le_unif (K := K) p hϖ
    have hpK : ‖(p : K)‖ ≤ ‖(ϖ : K)‖ := by simpa using hc
    exact norm_pow_prime_sub_le (norm_nonneg _) hpK (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy) (by omega) ih
      (norm_unif_lt_one hϖ).le

/- English proof (translation)
Establish `: residue (normInteger K) (x - y) = 0` using `by rw [map_sub, h, sub_self]`. Use `norm_le_norm_unif_of_lt_one hϖ (residue_eq_zero_iff_norm_lt_one.1 this)` as an intermediate fact. Simplify using `using this`.
-/
theorem norm_sub_le_unif_of_residue_eq {ϖ : normInteger K} (hϖ : Irreducible ϖ)
    {x y : normInteger K} (h : residue (normInteger K) x = residue (normInteger K) y) :
    ‖(x : K) - y‖ ≤ ‖(ϖ : K)‖ := by
  have : residue (normInteger K) (x - y) = 0 := by rw [map_sub, h, sub_self]
  have := norm_le_norm_unif_of_lt_one hϖ (residue_eq_zero_iff_norm_lt_one.1 this)
  simpa using this

/- English proof (translation)
Use `(mem_span_singleton_pow_iff (a := (p : normInteger K)) (x := x) 1).2 (by simpa using h)` as an intermediate fact. Simplify using `using this`.
-/
theorem mem_span_natCast_prime_of_norm_le {x : normInteger K}
    (h : ‖(x : K)‖ ≤ ‖((p : normInteger K) : K)‖) : x ∈ span {(p : normInteger K)} := by
  have := (mem_span_singleton_pow_iff (a := (p : normInteger K)) (x := x) 1).2 (by simpa using h)
  simpa using this

variable [CharZero K]

/- English proof (translation)
Introduce `h`. Establish `h' : ((p : normInteger K) : K) = 0` using `by rw [h]; rfl`. Establish `: (p : K) = 0` using `by simpa using h'`. Conclude with `hp.out.ne_zero (by exact_mod_cast this)`.
-/
theorem natCast_prime_ne_zero : (p : normInteger K) ≠ 0 := by
  intro h
  have h' : ((p : normInteger K) : K) = 0 := by rw [h]; rfl
  have : (p : K) = 0 := by simpa using h'
  exact hp.out.ne_zero (by exact_mod_cast this)

variable {ϖ : normInteger K} (hϖ : Irreducible ϖ)

def ramIdx : ℕ :=
  (IsDiscreteValuationRing.associated_pow_irreducible (natCast_prime_ne_zero (K := K) p) hϖ).choose

/- English proof (translation)
The claim follows from `(IsDiscreteValuationRing.associated_pow_irreducible (natCast_prime_ne_zero (K := K) p) hϖ).choose_spec`.
-/
theorem associated_ramIdx : Associated (p : normInteger K) (ϖ ^ ramIdx p hϖ) :=
  (IsDiscreteValuationRing.associated_pow_irreducible (natCast_prime_ne_zero (K := K) p) hϖ).choose_spec

/- English proof (translation)
Take `⟨u, hu⟩` from `associated_ramIdx p hϖ`. Conclude with `⟨u⁻¹, by rw [← hu, mul_assoc, Units.mul_inv, mul_one]⟩`.
-/
theorem exists_unit_natCast_prime_eq : ∃ u : (normInteger K)ˣ, (p : normInteger K) = ϖ ^ ramIdx p hϖ * u := by
  obtain ⟨u, hu⟩ := associated_ramIdx p hϖ
  exact ⟨u⁻¹, by rw [← hu, mul_assoc, Units.mul_inv, mul_one]⟩

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_unit_natCast_prime_eq p hϖ`. Rewrite using `[hu]`. Simplify using `only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]`. Rewrite using `[isUnit_integer_iff_norm_eq_one.1 u.isUnit, mul_one]`.
-/
theorem norm_natCast_prime_eq : ‖((p : normInteger K) : K)‖ = ‖(ϖ : K)‖ ^ ramIdx p hϖ := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_prime_eq p hϖ
  rw [hu]
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
  rw [isUnit_integer_iff_norm_eq_one.1 u.isUnit, mul_one]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h0 : ramIdx p hϖ = 0` using `by omega`. Use `norm_natCast_prime_eq p hϖ` as an intermediate fact. Rewrite `this` using `[h0, pow_zero]`. Conclude with `(norm_natCast_prime_lt_one (K := K) p).ne this`.
-/
theorem ramIdx_pos : 0 < ramIdx p hϖ := by
  by_contra h
  have h0 : ramIdx p hϖ = 0 := by omega
  have := norm_natCast_prime_eq p hϖ
  rw [h0, pow_zero] at this
  exact (norm_natCast_prime_lt_one (K := K) p).ne this

end Residue

section Tilt

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [IsDiscreteValuationRing (normInteger K)]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]

variable (K) in

def tiltResidue : PreTilt (normInteger K) p →+* ResidueField (normInteger K) :=
  (Ideal.Quotient.lift (span {(p : normInteger K)}) (residue (normInteger K)) fun a ha => by
    obtain ⟨c, rfl⟩ := mem_span_singleton'.1 ha
    rw [map_mul, residue_natCast_prime, mul_zero]).comp (PreTilt.coeff 0)

/- English proof (translation)
Simplify using `[tiltResidue, ← hy]`.
-/
theorem tiltResidue_of_mk (x : PreTilt (normInteger K) p) (y : normInteger K)
    (hy : Ideal.Quotient.mk _ y = PreTilt.coeff 0 x) :
    tiltResidue K p x = residue (normInteger K) y := by
  simp [tiltResidue, ← hy]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ', pow_mul, ← add_assoc, PreTilt.coeff_pow_p, ih]`.
-/
theorem preTilt_coeff_pow (x : PreTilt (normInteger K) p) (n m : ℕ) :
    PreTilt.coeff (n + m) x ^ p ^ m = PreTilt.coeff n x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_mul, ← add_assoc, PreTilt.coeff_pow_p, ih]

variable [CharZero K]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (normInteger K)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `hsmall : ∀ n, ∀ y : normInteger K, Ideal.Quotient.mk _ y = PreTilt.coeff n x → ‖(y : K)‖ ≤ ‖(ϖ : K)‖`. Introduce `n y hy`.

Establish `h1 : tiltResidue K p x = residue _ (y ^ p ^ n)`. Apply `tiltResidue_of_mk` to reduce the goal to its premises. Rewrite using `[map_pow, hy, ← preTilt_coeff_pow p x 0 n, zero_add]`. Rewrite `h1` using `[hx, map_pow, eq_comm, pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)]`. Conclude with `norm_le_norm_unif_of_lt_one hϖ (residue_eq_zero_iff_norm_lt_one.1 h1)`.

Apply `Perfection.ext` to reduce the goal to its premises. Introduce `n`. Rewrite using `[← PreTilt.coeff_def, ← PreTilt.coeff_def, map_zero]`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (PreTilt.coeff (n + ramIdx p hϖ) x)`. Establish `hy1` using `hsmall _ y hy`.

Rewrite using `[← preTilt_coeff_pow p x n (ramIdx p hϖ), ← hy, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Apply `mem_span_natCast_prime_of_norm_le` to reduce the goal to its premises. Rewrite using `[norm_natCast_prime_eq p hϖ, SubmonoidClass.coe_pow, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tiltResidue_injective : Function.Injective (tiltResidue K p) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (normInteger K)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hsmall : ∀ n, ∀ y : normInteger K, Ideal.Quotient.mk _ y = PreTilt.coeff n x →
      ‖(y : K)‖ ≤ ‖(ϖ : K)‖ := by
    intro n y hy
    have h1 : tiltResidue K p x = residue _ (y ^ p ^ n) := by
      apply tiltResidue_of_mk
      rw [map_pow, hy, ← preTilt_coeff_pow p x 0 n, zero_add]
    rw [hx, map_pow, eq_comm, pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)] at h1
    exact norm_le_norm_unif_of_lt_one hϖ (residue_eq_zero_iff_norm_lt_one.1 h1)
  apply Perfection.ext
  intro n
  rw [← PreTilt.coeff_def, ← PreTilt.coeff_def, map_zero]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff (n + ramIdx p hϖ) x)
  have hy1 := hsmall _ y hy
  rw [← preTilt_coeff_pow p x n (ramIdx p hϖ), ← hy, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  apply mem_span_natCast_prime_of_norm_le
  rw [norm_natCast_prime_eq p hϖ, SubmonoidClass.coe_pow, norm_pow]
  calc ‖(y : K)‖ ^ p ^ ramIdx p hϖ ≤ ‖(ϖ : K)‖ ^ p ^ ramIdx p hϖ := by gcongr
    _ ≤ ‖(ϖ : K)‖ ^ ramIdx p hϖ :=
        pow_le_pow_of_le_one (norm_nonneg _) (norm_unif_lt_one hϖ).le
          (Nat.lt_pow_self hp.out.one_lt).le

variable [PerfectRing (ResidueField (normInteger K)) p]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (normInteger K)`. Use `set e := ramIdx p hϖ`. Introduce `a`. Use `set r : ℕ → ResidueField (normInteger K) := fun m => ((frobeniusEquiv (ResidueField (normInteger K)) p).symm^[m]) a with hr_def`. Establish `hr : ∀ m, r (m + 1) ^ p = r m`.

Introduce `m`. Simplify using `only [hr_def, Function.iterate_succ_apply']`. Conclude with `frobenius_apply_frobeniusEquiv_symm _ p _`. Establish `hr0 : ∀ m, r m ^ p ^ m = a`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => simp [hr_def]`. Consider the case `succ m ih => rw [pow_succ', pow_mul, hr, ih]`. Use `choose z hz using fun m => residue_surjective (R := normInteger K) (r m)`. Set `c : ℕ → ModP (normInteger K) p` to `fun n => Ideal.Quotient.mk _ (z (n + e) ^ p ^ e)`.

Establish `hc : ∀ n, c (n + 1) ^ p = c n`. Introduce `n`. Simplify using `only [c, ← map_pow]`. Rewrite using `[Ideal.Quotient.eq]`. Apply `mem_span_natCast_prime_of_norm_le` to reduce the goal to its premises.

Rewrite using `[norm_natCast_prime_eq p hϖ]`. Establish `hres : residue (normInteger K) (z (n + 1 + e) ^ p) = residue (normInteger K) (z (n + e))`. Rewrite using `[map_pow, hz, hz, show n + 1 + e = n + e + 1 by omega, hr]`. Establish `h1` using `norm_sub_le_unif_of_residue_eq hϖ hres`. Establish `h2` using `norm_pow_prime_pow_sub_le p hϖ (x := ((z (n + 1 + e) ^ p : normInteger K) : K)) (y := ((z (n + e) : normInteger K) : K)) (norm_coe_integer_le_one _) (norm_coe_integer_le_one _) le_rfl (by simpa using h1) e`.

Establish `h3 : ‖(ϖ : K)‖ ^ (1 + e) ≤ ‖(ϖ : K)‖ ^ e` using `pow_le_pow_of_le_one (norm_nonneg _) (norm_unif_lt_one hϖ).le (by omega)`. Rewrite using `[show ((z (n + 1 + e) ^ p ^ e) ^ p : normInteger K) = (z (n + 1 + e) ^ p) ^ p ^ e by`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm]]`. Establish `h4 : (((z (n + 1 + e) ^ p) ^ p ^ e - z (n + e) ^ p ^ e : normInteger K) : K) = ((z (n + 1 + e) ^ p : normInteger K) : K) ^ p ^ e - ((z (n + e) : normInteger K) : K) ^ p ^ e` using `by push_cast; ring`. Rewrite using `[h4]`.

Conclude with `h2.trans h3`. Set `x : PreTilt (normInteger K) p` to `⟨c, hc⟩`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[tiltResidue_of_mk p x (z (0 + e) ^ p ^ e) rfl, map_pow, hz, zero_add, hr0]`.
-/
theorem tiltResidue_surjective : Function.Surjective (tiltResidue K p) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (normInteger K)
  set e := ramIdx p hϖ
  intro a
  set r : ℕ → ResidueField (normInteger K) :=
    fun m => ((frobeniusEquiv (ResidueField (normInteger K)) p).symm^[m]) a with hr_def
  have hr : ∀ m, r (m + 1) ^ p = r m := by
    intro m
    simp only [hr_def, Function.iterate_succ_apply']
    exact frobenius_apply_frobeniusEquiv_symm _ p _
  have hr0 : ∀ m, r m ^ p ^ m = a := by
    intro m
    induction m with
    | zero => simp [hr_def]
    | succ m ih => rw [pow_succ', pow_mul, hr, ih]
  choose z hz using fun m => residue_surjective (R := normInteger K) (r m)
  let c : ℕ → ModP (normInteger K) p := fun n => Ideal.Quotient.mk _ (z (n + e) ^ p ^ e)
  have hc : ∀ n, c (n + 1) ^ p = c n := by
    intro n
    simp only [c, ← map_pow]
    rw [Ideal.Quotient.eq]
    apply mem_span_natCast_prime_of_norm_le
    rw [norm_natCast_prime_eq p hϖ]
    have hres : residue (normInteger K) (z (n + 1 + e) ^ p) = residue (normInteger K) (z (n + e)) := by
      rw [map_pow, hz, hz, show n + 1 + e = n + e + 1 by omega, hr]
    have h1 := norm_sub_le_unif_of_residue_eq hϖ hres
    have h2 := norm_pow_prime_pow_sub_le p hϖ (x := ((z (n + 1 + e) ^ p : normInteger K) : K))
      (y := ((z (n + e) : normInteger K) : K)) (norm_coe_integer_le_one _) (norm_coe_integer_le_one _)
      le_rfl (by simpa using h1) e
    have h3 : ‖(ϖ : K)‖ ^ (1 + e) ≤ ‖(ϖ : K)‖ ^ e :=
      pow_le_pow_of_le_one (norm_nonneg _) (norm_unif_lt_one hϖ).le (by omega)
    rw [show ((z (n + 1 + e) ^ p ^ e) ^ p : normInteger K) = (z (n + 1 + e) ^ p) ^ p ^ e by
      rw [← pow_mul, ← pow_mul, mul_comm]]
    have h4 : (((z (n + 1 + e) ^ p) ^ p ^ e - z (n + e) ^ p ^ e : normInteger K) : K) =
        ((z (n + 1 + e) ^ p : normInteger K) : K) ^ p ^ e - ((z (n + e) : normInteger K) : K) ^ p ^ e := by
      push_cast; ring
    rw [h4]
    exact h2.trans h3
  let x : PreTilt (normInteger K) p := ⟨c, hc⟩
  refine ⟨x, ?_⟩
  rw [tiltResidue_of_mk p x (z (0 + e) ^ p ^ e) rfl, map_pow, hz, zero_add, hr0]

def tiltResidueEquiv : PreTilt (normInteger K) p ≃+* ResidueField (normInteger K) :=
  RingEquiv.ofBijective (tiltResidue K p) ⟨tiltResidue_injective p, tiltResidue_surjective p⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tiltResidueEquiv_apply (x : PreTilt (normInteger K) p) :
    tiltResidueEquiv p x = tiltResidue K p x := rfl

end Tilt

section Cohen

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]
  [PerfectRing (ResidueField (normInteger K)) p]

omit [CompleteSpace K] [IsDiscreteValuationRing (normInteger K)] [CharZero K] in

/- English proof (translation)
Proceed by induction on `n generalizing a with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply, pow_succ, pow_mul, ih]`. Conclude with `frobenius_apply_frobeniusEquiv_symm R p a`.
-/
theorem frobeniusEquiv_symm_iterate_pow {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
    (a : R) (n : ℕ) : ((frobeniusEquiv R p).symm^[n] a) ^ p ^ n = a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih]
    exact frobenius_apply_frobeniusEquiv_symm R p a

omit [CompleteSpace K] [CharZero K] [PerfectRing (ResidueField (normInteger K)) p] in

/- English proof (translation)
Establish `hn : ∀ n : ℕ, ‖((x - y : normInteger K) : K)‖ ≤ ‖(a : K)‖ ^ n` using `fun n => (mem_span_singleton_pow_iff n).1 (by rw [span_singleton_pow]; exact h n)`. Establish `ht` using `tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha`. Establish `h0 : ‖((x - y : normInteger K) : K)‖ ≤ 0` using `ge_of_tendsto' ht hn`. Establish `: ((x - y : normInteger K) : K) = 0` using `norm_le_zero_iff.1 h0`. Conclude with `sub_eq_zero.1 (Subtype.ext this)`.
-/
theorem eq_of_forall_sub_mem_span_pow {a : normInteger K} (ha : ‖(a : K)‖ < 1)
    {x y : normInteger K} (h : ∀ n : ℕ, x - y ∈ span {a ^ n}) : x = y := by
  have hn : ∀ n : ℕ, ‖((x - y : normInteger K) : K)‖ ≤ ‖(a : K)‖ ^ n := fun n =>
    (mem_span_singleton_pow_iff n).1 (by rw [span_singleton_pow]; exact h n)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha
  have h0 : ‖((x - y : normInteger K) : K)‖ ≤ 0 := ge_of_tendsto' ht hn
  have : ((x - y : normInteger K) : K) = 0 := norm_le_zero_iff.1 h0
  exact sub_eq_zero.1 (Subtype.ext this)

variable (K) in

def cohenMap : WittVector p (ResidueField (normInteger K)) →+* normInteger K :=
  (fontaineTheta (normInteger K) p).comp
    (WittVector.map (tiltResidueEquiv (K := K) p).symm.toRingHom)

@[simp]
/- English proof (translation)
Establish `h` using `mk_fontaineTheta (WittVector.map (tiltResidueEquiv (K := K) p).symm.toRingHom w)`. Rewrite `h` using `[WittVector.map_coeff]`. Establish `h2 : tiltResidue K p ((tiltResidueEquiv (K` using `K) p).symm (w.coeff 0)) = w.coeff 0 := by`. Rewrite using `[← tiltResidueEquiv_apply, RingEquiv.apply_symm_apply]`. Rewrite using `[← h2]`.

Conclude with `(tiltResidue_of_mk p _ _ h).symm`.
-/
theorem residue_cohenMap (w : WittVector p (ResidueField (normInteger K))) :
    residue (normInteger K) (cohenMap K p w) = w.coeff 0 := by
  have h := mk_fontaineTheta (WittVector.map (tiltResidueEquiv (K := K) p).symm.toRingHom w)
  rw [WittVector.map_coeff] at h
  have h2 : tiltResidue K p ((tiltResidueEquiv (K := K) p).symm (w.coeff 0)) = w.coeff 0 := by
    rw [← tiltResidueEquiv_apply, RingEquiv.apply_symm_apply]
  rw [← h2]
  exact (tiltResidue_of_mk p _ _ h).symm

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (normInteger K)`. Establish `hT : ∀ a, f (teichmuller p a) = g (teichmuller p a)`. Introduce `a`. Establish `hn : ∀ n : ℕ, ‖((f (teichmuller p a) : normInteger K) : K) - g (teichmuller p a)‖ ≤ ‖(ϖ : K)‖ ^ n`. Introduce `n`.

Use `set b := (frobeniusEquiv (ResidueField (normInteger K)) p).symm^[n] a`. Establish `ht : teichmuller p a = teichmuller p b ^ p ^ n`. Rewrite using `[← map_pow, frobeniusEquiv_symm_iterate_pow]`. Rewrite using `[ht, map_pow, map_pow]`. Use `push_cast`.

Establish `h1` using `norm_sub_le_unif_of_residue_eq hϖ (h (teichmuller p b))`. Use `(norm_pow_prime_pow_sub_le p hϖ (norm_coe_integer_le_one _) (norm_coe_integer_le_one _) le_rfl (by simpa using h1) n).trans ?_` and prove the remaining obligations. Conclude with `pow_le_pow_of_le_one (norm_nonneg _) (norm_unif_lt_one hϖ).le (by omega)`. Establish `ht` using `tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_unif_lt_one hϖ)`. Establish `h0` using `ge_of_tendsto' ht hn`.

Conclude with `Subtype.ext (sub_eq_zero.1 (norm_le_zero_iff.1 h0))`. Establish `hmod : ∀ n : ℕ, (Ideal.Quotient.mk (span {(p : normInteger K) ^ n})).comp f = (Ideal.Quotient.mk (span {(p : normInteger K) ^ n})).comp g`. Introduce `n`. Apply `WittVector.eq_of_apply_teichmuller_eq` to reduce the goal to its premises. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_natCast (Ideal.Quotient.mk (span {(p : normInteger K) ^ n})), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `mem_span_singleton_self _`. Introduce `x`. Simplify using `[hT x]`. Use extensionality with `w`.

Use `eq_of_forall_sub_mem_span_pow (K := K) (a := (p : normInteger K)) (norm_natCast_prime_lt_one p) (x := f w) (y := g w) fun n => by` as an intermediate fact. Use `congrArg (fun φ => φ w) (hmod n)` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Conclude with `Ideal.Quotient.eq.1 this`. Rewrite using `[this]`.
-/
theorem ringHom_ext_of_residue (f g : WittVector p (ResidueField (normInteger K)) →+* normInteger K)
    (h : ∀ w, residue (normInteger K) (f w) = residue (normInteger K) (g w)) : f = g := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (normInteger K)
  have hT : ∀ a, f (teichmuller p a) = g (teichmuller p a) := by
    intro a
    have hn : ∀ n : ℕ, ‖((f (teichmuller p a) : normInteger K) : K) - g (teichmuller p a)‖ ≤
        ‖(ϖ : K)‖ ^ n := by
      intro n
      set b := (frobeniusEquiv (ResidueField (normInteger K)) p).symm^[n] a
      have ht : teichmuller p a = teichmuller p b ^ p ^ n := by
        rw [← map_pow, frobeniusEquiv_symm_iterate_pow]
      rw [ht, map_pow, map_pow]
      push_cast
      have h1 := norm_sub_le_unif_of_residue_eq hϖ (h (teichmuller p b))
      refine (norm_pow_prime_pow_sub_le p hϖ (norm_coe_integer_le_one _) (norm_coe_integer_le_one _)
        le_rfl (by simpa using h1) n).trans ?_
      exact pow_le_pow_of_le_one (norm_nonneg _) (norm_unif_lt_one hϖ).le (by omega)
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_unif_lt_one hϖ)
    have h0 := ge_of_tendsto' ht hn
    exact Subtype.ext (sub_eq_zero.1 (norm_le_zero_iff.1 h0))
  have hmod : ∀ n : ℕ, (Ideal.Quotient.mk (span {(p : normInteger K) ^ n})).comp f =
      (Ideal.Quotient.mk (span {(p : normInteger K) ^ n})).comp g := by
    intro n
    apply WittVector.eq_of_apply_teichmuller_eq
    · refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (span {(p : normInteger K) ^ n})), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact mem_span_singleton_self _
    · intro x
      simp [hT x]
  ext w
  have := eq_of_forall_sub_mem_span_pow (K := K) (a := (p : normInteger K))
    (norm_natCast_prime_lt_one p) (x := f w) (y := g w) fun n => by
      have := congrArg (fun φ => φ w) (hmod n)
      simp only [RingHom.comp_apply] at this
      exact Ideal.Quotient.eq.1 this
  rw [this]

/- English proof (translation)
Apply `ringHom_ext_of_residue` to reduce the goal to its premises. Introduce `w`. Simplify using `[hσ, iterateFrobenius_def]`.
-/
theorem comp_cohenMap_of_residue (σ : normInteger K →+* normInteger K) (a : ℕ)
    (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) :
    σ.comp (cohenMap K p) =
      (cohenMap K p).comp (WittVector.map (iterateFrobenius (ResidueField (normInteger K)) p a)) := by
  apply ringHom_ext_of_residue
  intro w
  simp [hσ, iterateFrobenius_def]

/- English proof (translation)
Use `le_antisymm (norm_coe_integer_le_one _) (not_lt.1 fun h => hw ?_)` and prove the remaining obligations. Rewrite using `[← residue_cohenMap, residue_eq_zero_iff_norm_lt_one]`. Conclude with `h`.
-/
theorem norm_cohenMap_of_coeff_ne_zero {w : WittVector p (ResidueField (normInteger K))}
    (hw : w.coeff 0 ≠ 0) : ‖(cohenMap K p w : K)‖ = 1 := by
  refine le_antisymm (norm_coe_integer_le_one _) (not_lt.1 fun h => hw ?_)
  rw [← residue_cohenMap, residue_eq_zero_iff_norm_lt_one]
  exact h

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `w hw`. Assume the negation of the conclusion as `h0`. Take `⟨m, b, hb, rfl⟩` from `WittVector.exists_eq_pow_p_mul w h0`. Rewrite `hw` using `[map_mul, map_pow, map_natCast]`.

Establish `hb' : cohenMap K p b ≠ 0` using `fun h => hb (by rw [← residue_cohenMap, h, map_zero])`. Conclude with `mul_ne_zero (pow_ne_zero _ (natCast_prime_ne_zero p)) hb' hw`.
-/
theorem cohenMap_injective : Function.Injective (cohenMap K p) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra h0
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  rw [map_mul, map_pow, map_natCast] at hw
  have hb' : cohenMap K p b ≠ 0 := fun h => hb (by rw [← residue_cohenMap, h, map_zero])
  exact mul_ne_zero (pow_ne_zero _ (natCast_prime_ne_zero p)) hb' hw

instance cohenAlgebra : Algebra (WittVector p (ResidueField (normInteger K))) (normInteger K) :=
  (cohenMap K p).toAlgebra

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_cohen :
    algebraMap (WittVector p (ResidueField (normInteger K))) (normInteger K) = cohenMap K p := rfl

/- English proof (translation)
The claim follows from `Algebra.smul_def w x`.
-/
theorem cohen_smul_def (w : WittVector p (ResidueField (normInteger K))) (x : normInteger K) :
    w • x = cohenMap K p w * x := Algebra.smul_def w x

variable {ϖ : normInteger K} (hϖ : Irreducible ϖ)

/- English proof (translation)
Take `⟨m, b, hb, rfl⟩` from `WittVector.exists_eq_pow_p_mul w hw`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_natCast]`. Simplify using `only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]`. Rewrite using `[norm_natCast_prime_eq p hϖ, norm_cohenMap_of_coeff_ne_zero p hb, mul_one, ← pow_mul]`.
-/
theorem exists_norm_cohenMap_eq {w : WittVector p (ResidueField (normInteger K))} (hw : w ≠ 0) :
    ∃ m : ℕ, ‖(cohenMap K p w : K)‖ = ‖(ϖ : K)‖ ^ (ramIdx p hϖ * m) := by
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w hw
  refine ⟨m, ?_⟩
  rw [map_mul, map_pow, map_natCast]
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
  rw [norm_natCast_prime_eq p hϖ, norm_cohenMap_of_coeff_ne_zero p hb, mul_one, ← pow_mul]

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨i₀, hi₀⟩` from `hne`.

Use `set S := Finset.univ.filter (fun i => g i ≠ 0) with hS_def`. Establish `hS : S.Nonempty` using `⟨i₀, by simp [hS_def, hi₀]⟩`. Use `set f : Fin (ramIdx p hϖ) → K := fun i => (cohenMap K p (g i) : K) * (ϖ : K) ^ (i : ℕ) with hf`. Establish `hsum : ∑ i ∈ S, f i = 0`. Establish `h1` using `congrArg (fun z : normInteger K => (z : K)) hg`.

Simplify using `only [cohen_smul_def] at h1`. Move the coercions through the operations in `at h1`. Rewrite using `[← h1, hS_def, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Both sides reduce to the same expression. Simplify using `[not_not.1 h]`. Establish `hnorm : ∀ i ∈ S, ∃ m : ℕ, ‖f i‖ = ‖(ϖ : K)‖ ^ ((i : ℕ) + ramIdx p hϖ * m)`. Introduce `i hi`. Establish `hgi : g i ≠ 0` using `by simpa [hS_def] using hi`.

Take `⟨m, hm⟩` from `exists_norm_cohenMap_eq p hϖ hgi`. Conclude with `⟨m, by rw [hf, norm_mul, norm_pow, hm, ← pow_add, add_comm]⟩`. Establish `h0` using `norm_unif_pos hϖ`. Establish `h1` using `norm_unif_lt_one hϖ`. Establish `hpair : Set.Pairwise (S : Set (Fin (ramIdx p hϖ))) (fun i j => ‖f i‖ ≠ ‖f j‖)`.

Introduce `i hi j hj hij heq`. Take `⟨m, hm⟩` from `hnorm i hi`. Take `⟨m', hm'⟩` from `hnorm j hj`. Rewrite `heq` using `[hm, hm']`. Use `pow_right_injective₀ h0 h1.ne heq` as an intermediate fact.

Establish `hmod` using `congrArg (· % ramIdx p hϖ) this`. Simplify using `only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hmod`. Conclude with `hij (Fin.ext hmod)`. Use `IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne hS hpair` as an intermediate fact. Rewrite `this` using `[hsum, norm_zero]`.

Take `⟨m, hm⟩` from `hnorm i₀ (by simp [hS_def, hi₀])`. Establish `hpos : 0 < ‖f i₀‖` using `by rw [hm]; positivity`. Establish `hle : ‖f i₀‖ ≤ S.sup' hS (fun i => ‖f i‖)` using `Finset.le_sup' (fun i => ‖f i‖) (by simp [hS_def, hi₀])`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem linearIndependent_unif_pow :
    LinearIndependent (WittVector p (ResidueField (normInteger K)))
      (fun j : Fin (ramIdx p hϖ) => ϖ ^ (j : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  set S := Finset.univ.filter (fun i => g i ≠ 0) with hS_def
  have hS : S.Nonempty := ⟨i₀, by simp [hS_def, hi₀]⟩
  set f : Fin (ramIdx p hϖ) → K := fun i => (cohenMap K p (g i) : K) * (ϖ : K) ^ (i : ℕ) with hf
  have hsum : ∑ i ∈ S, f i = 0 := by
    have h1 := congrArg (fun z : normInteger K => (z : K)) hg
    simp only [cohen_smul_def] at h1
    push_cast at h1
    rw [← h1, hS_def, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · simp [not_not.1 h]
  have hnorm : ∀ i ∈ S, ∃ m : ℕ, ‖f i‖ = ‖(ϖ : K)‖ ^ ((i : ℕ) + ramIdx p hϖ * m) := by
    intro i hi
    have hgi : g i ≠ 0 := by simpa [hS_def] using hi
    obtain ⟨m, hm⟩ := exists_norm_cohenMap_eq p hϖ hgi
    exact ⟨m, by rw [hf, norm_mul, norm_pow, hm, ← pow_add, add_comm]⟩
  have h0 := norm_unif_pos hϖ
  have h1 := norm_unif_lt_one hϖ
  have hpair : Set.Pairwise (S : Set (Fin (ramIdx p hϖ))) (fun i j => ‖f i‖ ≠ ‖f j‖) := by
    intro i hi j hj hij heq
    obtain ⟨m, hm⟩ := hnorm i hi
    obtain ⟨m', hm'⟩ := hnorm j hj
    rw [hm, hm'] at heq
    have := pow_right_injective₀ h0 h1.ne heq
    have hmod := congrArg (· % ramIdx p hϖ) this
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hmod
    exact hij (Fin.ext hmod)
  have := IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne hS hpair
  rw [hsum, norm_zero] at this
  obtain ⟨m, hm⟩ := hnorm i₀ (by simp [hS_def, hi₀])
  have hpos : 0 < ‖f i₀‖ := by rw [hm]; positivity
  have hle : ‖f i₀‖ ≤ S.sup' hS (fun i => ‖f i‖) :=
    Finset.le_sup' (fun i => ‖f i‖) (by simp [hS_def, hi₀])
  linarith

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∃ (d : ℕ → WittVector p (ResidueField (normInteger K))) (y : normInteger K), x = ∑ j ∈ Finset.range n, cohenMap K p (d j) * ϖ ^ j + ϖ ^ n * y`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, x, by simp⟩`. Consider the case `succ n ih`.

Take `⟨d, y, hy⟩` from `ih`. Use `set t := teichmuller p (residue (normInteger K) y)`. Establish `hres : residue (normInteger K) (y - cohenMap K p t) = 0`. Rewrite using `[map_sub, residue_cohenMap, teichmuller_coeff_zero, sub_self]`. Establish `hm : y - cohenMap K p t ∈ maximalIdeal (normInteger K)` using `(residue_eq_zero_iff _).1 hres`.

Rewrite `hm` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, mem_span_singleton']`. Take `⟨y', hy'⟩` from `hm`. Use `⟨fun j => if j = n then t else d j, y', ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_range_succ]`. Simplify using `only [if_true]`.

Establish `hs : ∑ j ∈ Finset.range n, cohenMap K p (if j = n then t else d j) * ϖ ^ j = ∑ j ∈ Finset.range n, cohenMap K p (d j) * ϖ ^ j` using `Finset.sum_congr rfl fun j hj => by`. Rewrite using `[if_neg (by rw [Finset.mem_range] at hj; omega)]`. Rewrite using `[hs, hy]`. Establish `: y = cohenMap K p t + y' * ϖ` using `by rw [hy']; ring`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨d, y, hy⟩` from `key (ramIdx p hϖ)`. Take `⟨u, hu⟩` from `exists_unit_natCast_prime_eq p hϖ`. Use `⟨fun j => d j, ↑u⁻¹ * y, ?_⟩` and prove the remaining obligations. Rewrite using `[hy, Fin.sum_univ_eq_sum_range (fun j => cohenMap K p (d j) * ϖ ^ j), hu]`.

Use `congr 1`. Rewrite using `[mul_assoc, ← mul_assoc (u : normInteger K), Units.mul_inv, one_mul]`.
-/
theorem exists_digits (x : normInteger K) :
    ∃ (d : Fin (ramIdx p hϖ) → WittVector p (ResidueField (normInteger K))) (y : normInteger K),
      x = ∑ j, cohenMap K p (d j) * ϖ ^ (j : ℕ) + p * y := by
  have key : ∀ n : ℕ, ∃ (d : ℕ → WittVector p (ResidueField (normInteger K))) (y : normInteger K),
      x = ∑ j ∈ Finset.range n, cohenMap K p (d j) * ϖ ^ j + ϖ ^ n * y := by
    intro n
    induction n with
    | zero => exact ⟨0, x, by simp⟩
    | succ n ih =>
      obtain ⟨d, y, hy⟩ := ih
      set t := teichmuller p (residue (normInteger K) y)
      have hres : residue (normInteger K) (y - cohenMap K p t) = 0 := by
        rw [map_sub, residue_cohenMap, teichmuller_coeff_zero, sub_self]
      have hm : y - cohenMap K p t ∈ maximalIdeal (normInteger K) := (residue_eq_zero_iff _).1 hres
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, mem_span_singleton'] at hm
      obtain ⟨y', hy'⟩ := hm
      refine ⟨fun j => if j = n then t else d j, y', ?_⟩
      rw [Finset.sum_range_succ]
      simp only [if_true]
      have hs : ∑ j ∈ Finset.range n, cohenMap K p (if j = n then t else d j) * ϖ ^ j =
          ∑ j ∈ Finset.range n, cohenMap K p (d j) * ϖ ^ j :=
        Finset.sum_congr rfl fun j hj => by
          rw [if_neg (by rw [Finset.mem_range] at hj; omega)]
      rw [hs, hy]
      have : y = cohenMap K p t + y' * ϖ := by rw [hy']; ring
      rw [this]
      ring
  obtain ⟨d, y, hy⟩ := key (ramIdx p hϖ)
  obtain ⟨u, hu⟩ := exists_unit_natCast_prime_eq p hϖ
  refine ⟨fun j => d j, ↑u⁻¹ * y, ?_⟩
  rw [hy, Fin.sum_univ_eq_sum_range (fun j => cohenMap K p (d j) * ϖ ^ j), hu]
  congr 1
  rw [mul_assoc, ← mul_assoc (u : normInteger K), Units.mul_inv, one_mul]

/- English proof (translation)
Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Use `choose D Y hDY using exists_digits p hϖ`. Use `set rem : ℕ → normInteger K := fun n => Y^[n] x with hrem`. Use `set A : ℕ → Fin (ramIdx p hϖ) → WittVector p (ResidueField (normInteger K)) := fun n j => ∑ i ∈ Finset.range n, (p : WittVector p (ResidueField (normInteger K))) ^ i * D (rem i) j with hA`. Establish `hinv : ∀ n, x = ∑ j, cohenMap K p (A n j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n * rem n`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [hA, hrem]`. Consider the case `succ n ih`. Establish `hr : rem (n + 1) = Y (rem n)`.

Simplify using `only [hrem]`. Rewrite using `[Function.iterate_succ_apply']`. Establish `hA1 : ∀ j, A (n + 1) j = A n j + (p : WittVector p (ResidueField (normInteger K))) ^ n * D (rem n) j`. Introduce `j`. Simplify using `only [hA, Finset.sum_range_succ]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hDY (rem n)]`. Use `_ = ∑ j, cohenMap K p (A (n + 1) j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ (n + 1) * rem (n + 1) := by`. Rewrite using `[hr]`. Simplify using `only [hA1, map_add, map_mul, map_pow, map_natCast, add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum, mul_assoc]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlim : ∀ j, ∃ W : WittVector p (ResidueField (normInteger K)), ∀ n, W - A n j ∈ span {(p : WittVector p (ResidueField (normInteger K))) ^ n}`. Introduce `j`. Use `WittLift.exists_limit (fun n => A n j) fun n => ?_` and prove the remaining obligations. Simplify using `only [hA, Finset.sum_range_succ, add_sub_cancel_left]`.

Conclude with `mem_span_singleton.2 (dvd_mul_right _ _)`. Use `choose W hW using hlim`. Establish `hx : x = ∑ j, cohenMap K p (W j) * ϖ ^ (j : ℕ)`. Apply `eq_of_forall_sub_mem_span_pow (K := K) (a := (p : normInteger K)) (norm_natCast_prime_lt_one p)` to reduce the goal to its premises. Introduce `n`.

Establish `hc : ∀ j, cohenMap K p (A n j) - cohenMap K p (W j) ∈ span {(p : normInteger K) ^ n}`. Introduce `j`. Take `⟨c, hc⟩` from `mem_span_singleton.1 (hW j n)`. Establish `: A n j - W j = -((p : WittVector p (ResidueField (normInteger K))) ^ n * c)`. Rewrite using `[← hc]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← map_sub, this, map_neg, map_mul, map_pow, map_natCast]`. Conclude with `neg_mem (mem_span_singleton.2 (dvd_mul_right _ _))`. Use `nth_rewrite 1 [hinv n]`. Establish `: ∑ j, cohenMap K p (A n j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n * rem n - ∑ j, cohenMap K p (W j) * ϖ ^ (j : ℕ) = ∑ j, (cohenMap K p (A n j) - cohenMap K p (W j)) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n * rem n`.

Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `add_mem (Submodule.sum_mem _ fun j _ => ?_) (mem_span_singleton.2 (dvd_mul_right _ _))` and prove the remaining obligations. Conclude with `Ideal.mul_mem_right _ _ (hc j)`.

Rewrite using `[hx]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← cohen_smul_def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem span_unif_pow_eq_top :
    Submodule.span (WittVector p (ResidueField (normInteger K)))
      (Set.range fun j : Fin (ramIdx p hϖ) => ϖ ^ (j : ℕ)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  choose D Y hDY using exists_digits p hϖ
  set rem : ℕ → normInteger K := fun n => Y^[n] x with hrem
  set A : ℕ → Fin (ramIdx p hϖ) → WittVector p (ResidueField (normInteger K)) :=
    fun n j => ∑ i ∈ Finset.range n, (p : WittVector p (ResidueField (normInteger K))) ^ i * D (rem i) j
    with hA
  have hinv : ∀ n, x = ∑ j, cohenMap K p (A n j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n * rem n := by
    intro n
    induction n with
    | zero => simp [hA, hrem]
    | succ n ih =>
      have hr : rem (n + 1) = Y (rem n) := by
        simp only [hrem]; rw [Function.iterate_succ_apply']
      have hA1 : ∀ j, A (n + 1) j = A n j + (p : WittVector p (ResidueField (normInteger K))) ^ n * D (rem n) j := by
        intro j; simp only [hA, Finset.sum_range_succ]
      calc x = ∑ j, cohenMap K p (A n j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n * rem n := ih
        _ = ∑ j, cohenMap K p (A n j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n *
              (∑ j, cohenMap K p (D (rem n) j) * ϖ ^ (j : ℕ) + p * Y (rem n)) := by
            rw [← hDY (rem n)]
        _ = ∑ j, cohenMap K p (A (n + 1) j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ (n + 1) * rem (n + 1) := by
            rw [hr]
            simp only [hA1, map_add, map_mul, map_pow, map_natCast, add_mul, Finset.sum_add_distrib,
              mul_add, Finset.mul_sum, mul_assoc]
            ring
  have hlim : ∀ j, ∃ W : WittVector p (ResidueField (normInteger K)),
      ∀ n, W - A n j ∈ span {(p : WittVector p (ResidueField (normInteger K))) ^ n} := by
    intro j
    refine WittLift.exists_limit (fun n => A n j) fun n => ?_
    simp only [hA, Finset.sum_range_succ, add_sub_cancel_left]
    exact mem_span_singleton.2 (dvd_mul_right _ _)
  choose W hW using hlim
  have hx : x = ∑ j, cohenMap K p (W j) * ϖ ^ (j : ℕ) := by
    apply eq_of_forall_sub_mem_span_pow (K := K) (a := (p : normInteger K)) (norm_natCast_prime_lt_one p)
    intro n
    have hc : ∀ j, cohenMap K p (A n j) - cohenMap K p (W j) ∈ span {(p : normInteger K) ^ n} := by
      intro j
      obtain ⟨c, hc⟩ := mem_span_singleton.1 (hW j n)
      have : A n j - W j = -((p : WittVector p (ResidueField (normInteger K))) ^ n * c) := by
        rw [← hc]; ring
      rw [← map_sub, this, map_neg, map_mul, map_pow, map_natCast]
      exact neg_mem (mem_span_singleton.2 (dvd_mul_right _ _))
    nth_rewrite 1 [hinv n]
    have : ∑ j, cohenMap K p (A n j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n * rem n -
        ∑ j, cohenMap K p (W j) * ϖ ^ (j : ℕ) =
        ∑ j, (cohenMap K p (A n j) - cohenMap K p (W j)) * ϖ ^ (j : ℕ) +
          (p : normInteger K) ^ n * rem n := by
      simp only [sub_mul, Finset.sum_sub_distrib]; ring
    rw [this]
    refine add_mem (Submodule.sum_mem _ fun j _ => ?_) (mem_span_singleton.2 (dvd_mul_right _ _))
    exact Ideal.mul_mem_right _ _ (hc j)
  rw [hx]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← cohen_smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

def cohenBasis : Module.Basis (Fin (ramIdx p hϖ)) (WittVector p (ResidueField (normInteger K)))
    (normInteger K) :=
  Module.Basis.mk (linearIndependent_unif_pow p hϖ) (span_unif_pow_eq_top p hϖ).ge

@[simp]
/- English proof (translation)
The claim follows from `Module.Basis.mk_apply _ _ _`.
-/
theorem cohenBasis_apply (j : Fin (ramIdx p hϖ)) : cohenBasis p hϖ j = ϖ ^ (j : ℕ) :=
  Module.Basis.mk_apply _ _ _

end Cohen

end GroundTheory.PAdicHodge

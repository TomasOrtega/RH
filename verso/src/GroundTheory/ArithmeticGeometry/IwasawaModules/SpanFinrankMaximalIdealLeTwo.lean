import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Arith.Iwasawa

open PowerSeries IsLocalRing
open scoped Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Lambda : Type := PowerSeries ℤ_[p]

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem isDomain : IsDomain (Lambda p) := inferInstance

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem isLocalRing : IsLocalRing (Lambda p) := inferInstance

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem isNoetherianRing : IsNoetherianRing (Lambda p) := inferInstance

/- English proof (translation)
Establish `hmem : (p : ℤ_[p]) ∈ maximalIdeal ℤ_[p]`. Rewrite using `[PadicInt.maximalIdeal_eq_span_p]`. Conclude with `Ideal.subset_span rfl`. Conclude with `(mem_maximalIdeal _).1 hmem`.
-/
theorem padic_p_not_isUnit : ¬ IsUnit (p : ℤ_[p]) := by
  have hmem : (p : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  exact (mem_maximalIdeal _).1 hmem

/- English proof (translation)
Rewrite using `[isUnit_iff_constantCoeff, constantCoeff_C]`. Conclude with `padic_p_not_isUnit p`.
-/
theorem p_not_isUnit : ¬ IsUnit (C (p : ℤ_[p]) : Lambda p) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_C]
  exact padic_p_not_isUnit p

/- English proof (translation)
Rewrite using `[isUnit_iff_constantCoeff, constantCoeff_X]`. Conclude with `not_isUnit_zero`.
-/
theorem X_not_isUnit : ¬ IsUnit (X : Lambda p) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_X]
  exact not_isUnit_zero

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Rewrite `hf` using `[mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]`. Establish `h0 : constantCoeff f ∈ maximalIdeal ℤ_[p]` using `hf`. Rewrite `h0` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`.

Take `⟨a, ha⟩` from `h0`. Rewrite using `[eq_X_mul_shift_add_const f, ha, map_mul]`. Use `Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))) (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `x (rfl | rfl)`.

Conclude with `(mem_maximalIdeal _).2 (p_not_isUnit p)`. Conclude with `(mem_maximalIdeal _).2 (X_not_isUnit p)`.
-/
theorem maximalIdeal_eq_span :
    maximalIdeal (Lambda p) = Ideal.span {C (p : ℤ_[p]), X} := by
  apply le_antisymm
  · intro f hf
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff] at hf
    have h0 : constantCoeff f ∈ maximalIdeal ℤ_[p] := hf
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h0
    obtain ⟨a, ha⟩ := h0
    rw [eq_X_mul_shift_add_const f, ha, map_mul]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact (mem_maximalIdeal _).2 (p_not_isUnit p)
    · exact (mem_maximalIdeal _).2 (X_not_isUnit p)

/- English proof (translation)
Rewrite using `[maximalIdeal_eq_span]`. Use `(Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_` and prove the remaining obligations. Conclude with `(Set.ncard_insert_le _ _).trans (by simp)`.
-/
theorem spanFinrank_maximalIdeal_le_two : (maximalIdeal (Lambda p)).spanFinrank ≤ 2 := by
  rw [maximalIdeal_eq_span]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
  exact (Set.ncard_insert_le _ _).trans (by simp)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `(ringKrullDim_le_spanFinrank_maximalIdeal (Lambda p)).trans ?_` and prove the remaining obligations. Conclude with `spanFinrank_maximalIdeal_le_two p` after adjusting the coercions. Establish `h1 : ringKrullDim ℤ_[p] = 1` using `IsDiscreteValuationRing.ringKrullDim_eq_one ℤ_[p]`. Establish `h2` using `ringKrullDim_succ_le_ringKrullDim_powerseries (R := ℤ_[p])`.

Rewrite `h2` using `[h1]`. Conclude with `le_of_eq_of_le (by rfl) h2`.
-/
theorem ringKrullDim_eq_two : ringKrullDim (Lambda p) = 2 := by
  apply le_antisymm
  · refine (ringKrullDim_le_spanFinrank_maximalIdeal (Lambda p)).trans ?_
    exact_mod_cast spanFinrank_maximalIdeal_le_two p
  · have h1 : ringKrullDim ℤ_[p] = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one ℤ_[p]
    have h2 := ringKrullDim_succ_le_ringKrullDim_powerseries (R := ℤ_[p])
    rw [h1] at h2
    exact le_of_eq_of_le (by rfl) h2

instance isRegularLocalRing : IsRegularLocalRing (Lambda p) :=
  IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by
    rw [ringKrullDim_eq_two]; exact_mod_cast spanFinrank_maximalIdeal_le_two p)

def IsDistinguished (P : ℤ_[p][X]) : Prop :=
  P.IsDistinguishedAt (maximalIdeal ℤ_[p])

variable {p}

/- English proof (translation)
The claim follows from `Polynomial.IsDistinguishedAt.monic hP`.
-/
theorem IsDistinguished.monic {P : ℤ_[p][X]} (hP : IsDistinguished p P) : P.Monic :=
  Polynomial.IsDistinguishedAt.monic hP

/- English proof (translation)
The claim follows from `Polynomial.IsDistinguishedAt.mul hP hQ`.
-/
theorem IsDistinguished.mul {P Q : ℤ_[p][X]} (hP : IsDistinguished p P)
    (hQ : IsDistinguished p Q) : IsDistinguished p (P * Q) :=
  Polynomial.IsDistinguishedAt.mul hP hQ

/- English proof (translation)
The claim follows from `hP.monic.ne_zero`.
-/
theorem IsDistinguished.ne_zero {P : ℤ_[p][X]} (hP : IsDistinguished p P) : P ≠ 0 :=
  hP.monic.ne_zero

/- English proof (translation)
Rewrite using `[← Polynomial.polynomial_map_coe, Polynomial.IsDistinguishedAt.map_eq_X_pow hP, Polynomial.coe_pow, Polynomial.coe_X]`.
-/
theorem IsDistinguished.map_mk {P : ℤ_[p][X]} (hP : IsDistinguished p P) :
    (P : Lambda p).map (Ideal.Quotient.mk (maximalIdeal ℤ_[p])) = X ^ P.natDegree := by
  rw [← Polynomial.polynomial_map_coe, Polynomial.IsDistinguishedAt.map_eq_X_pow hP,
    Polynomial.coe_pow, Polynomial.coe_X]

end GroundTheory.Arith.Iwasawa

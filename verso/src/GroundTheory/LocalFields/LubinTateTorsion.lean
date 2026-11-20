import Mathlib
import GroundTheory.LocalFields.LubinTatePoints
import GroundTheory.LocalFields.Eisenstein

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

namespace FormalGroup

section Poly

variable {K : Type*} [Field K] [ValuativeRel K]

/- English proof (translation)
Set `e : (Unit →₀ ℕ) ≃ ℕ` to `Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)`. Establish `hterm : ∀ d : Unit →₀ ℕ, psTerm (p : PowerSeries 𝒪[K]) (fun _ => x) d = algebraMap K M (p.coeff (e d)) * x ^ (e d)`. Introduce `d`. Establish `hd : d = Finsupp.single () (e d)`. Use `ext`.

Simplify using `[e]`. Rewrite using `[psTerm, hd]`. Simplify using `only [Finsupp.prod_single_index, pow_zero, e]`. Use `congr 2`. Simplify using `[Finsupp.equivFunOnFinite, Equiv.funUnique]`.

Rewrite using `[psEval, ← e.symm.tsum_eq]`. Simplify using `only [hterm, Equiv.apply_symm_apply]`. Rewrite using `[tsum_eq_sum (s := p.support) fun n hn => by simp [Polynomial.notMem_support_iff.mp hn]]`. Rewrite using `[aeval_def, eval₂_eq_sum, Polynomial.sum_def, support_map_of_injective _ (FaithfulSMul.algebraMap_injective 𝒪[K] K)]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Rewrite using `[coeff_map, ← IsScalarTower.algebraMap_apply]`. Both sides reduce to the same expression.
-/
theorem psEval_polynomial {M : Type*} [CommRing M] [Algebra K M] [TopologicalSpace M]
    [T2Space M] (p : 𝒪[K][X]) (x : M) :
    psEval (p : PowerSeries 𝒪[K]) (fun _ => x) = aeval x (p.map (algebraMap 𝒪[K] K)) := by
  classical
  let e : (Unit →₀ ℕ) ≃ ℕ := Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)
  have hterm : ∀ d : Unit →₀ ℕ, psTerm (p : PowerSeries 𝒪[K]) (fun _ => x) d =
      algebraMap K M (p.coeff (e d)) * x ^ (e d) := by
    intro d
    have hd : d = Finsupp.single () (e d) := by
      ext
      simp [e]
    rw [psTerm, hd]
    simp only [Finsupp.prod_single_index, pow_zero, e]
    congr 2
    simp [Finsupp.equivFunOnFinite, Equiv.funUnique]
  rw [psEval, ← e.symm.tsum_eq]
  simp only [hterm, Equiv.apply_symm_apply]
  rw [tsum_eq_sum (s := p.support) fun n hn => by simp [Polynomial.notMem_support_iff.mp hn]]
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def,
    support_map_of_injective _ (FaithfulSMul.algebraMap_injective 𝒪[K] K)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_map, ← IsScalarTower.algebraMap_apply]
  rfl

end Poly

section LTPoly

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in

/- English proof (translation)
The claim follows from `Finite.one_lt_card`.
-/
theorem one_lt_card_residueField' : 1 < Nat.card 𝓀[K] := Finite.one_lt_card

def ltPoly (π : 𝒪[K]) : 𝒪[K][X] := C π * X + X ^ Nat.card 𝓀[K]

def ltPolyIter (π : 𝒪[K]) : ℕ → 𝒪[K][X]
  | 0 => X
  | n + 1 => (ltPoly π).comp (ltPolyIter π n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ltPolyIter_zero (π : 𝒪[K]) : ltPolyIter π 0 = X := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ltPolyIter_succ (π : 𝒪[K]) (n : ℕ) :
    ltPolyIter π (n + 1) = (ltPoly π).comp (ltPolyIter π n) := rfl

/- English proof (translation)
Rewrite using `[ltPoly, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, add_sub_cancel_right, Polynomial.coeff_coe]`.
-/
theorem coeff_ltPoly_sub (π : 𝒪[K]) (n : ℕ) :
    PowerSeries.coeff n ((ltPoly π : PowerSeries 𝒪[K]) - PowerSeries.X ^ Nat.card 𝓀[K]) =
      (C π * X : 𝒪[K][X]).coeff n := by
  rw [ltPoly, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, add_sub_cancel_right,
    Polynomial.coeff_coe]

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' K`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, ltPoly]`. Simplify using `only [coeff_add, coeff_C_mul_X, coeff_X_pow]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Use `coeff_one := by`. Establish `hq` using `one_lt_card_residueField' K`. Rewrite using `[Polynomial.coeff_coe, ltPoly]`. Simplify using `only [coeff_add, coeff_C_mul_X, coeff_X_pow]`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Use `dvd_coeff_sub n := by`. Rewrite using `[coeff_ltPoly_sub, coeff_C_mul_X]`. Use `split_ifs`. Conclude with `dvd_rfl`.

Conclude with `dvd_zero π`.
-/
theorem isLubinTateSeries_ltPoly (π : 𝒪[K]) :
    IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K]) where
  constantCoeff_eq_zero := by
    have hq := one_lt_card_residueField' K
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, ltPoly]
    simp only [coeff_add, coeff_C_mul_X, coeff_X_pow]
    simp
    omega
  coeff_one := by
    have hq := one_lt_card_residueField' K
    rw [Polynomial.coeff_coe, ltPoly]
    simp only [coeff_add, coeff_C_mul_X, coeff_X_pow]
    simp
    omega
  dvd_coeff_sub n := by
    rw [coeff_ltPoly_sub, coeff_C_mul_X]
    split_ifs
    · exact dvd_rfl
    · exact dvd_zero π

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' K`. Rewrite using `[ltPoly, add_comm]`. Use `monic_X_pow_add ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ltPoly_monic (π : 𝒪[K]) : (ltPoly π).Monic := by
  have hq := one_lt_card_residueField' K
  rw [ltPoly, add_comm]
  refine monic_X_pow_add ?_
  calc degree (C π * X) ≤ 1 := degree_C_mul_X_le π
    _ < Nat.card 𝓀[K] := by exact_mod_cast hq

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' K`. Rewrite using `[ltPoly, add_comm, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]`. Rewrite using `[degree_X_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem natDegree_ltPoly (π : 𝒪[K]) : (ltPoly π).natDegree = Nat.card 𝓀[K] := by
  have hq := one_lt_card_residueField' K
  rw [ltPoly, add_comm, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  calc degree (C π * X) ≤ 1 := degree_C_mul_X_le π
    _ < Nat.card 𝓀[K] := by exact_mod_cast hq

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨monic_X, by simp [ltPolyIter_zero]⟩`. Consider the case `succ n ih`. Establish `hq` using `one_lt_card_residueField' K`. Establish `hd : (ltPolyIter π n).natDegree ≠ 0`.

Rewrite using `[ih.2]`. Conclude with `pow_ne_zero _ (by omega)`. Use `⟨(ltPoly_monic π).comp ih.1 hd, ?_⟩` and prove the remaining obligations. Rewrite using `[ltPolyIter_succ, natDegree_comp, natDegree_ltPoly, ih.2, pow_succ, mul_comm]`.
-/
theorem ltPolyIter_monic (π : 𝒪[K]) (n : ℕ) : (ltPolyIter π n).Monic ∧
    (ltPolyIter π n).natDegree = Nat.card 𝓀[K] ^ n := by
  induction n with
  | zero => exact ⟨monic_X, by simp [ltPolyIter_zero]⟩
  | succ n ih =>
    have hq := one_lt_card_residueField' K
    have hd : (ltPolyIter π n).natDegree ≠ 0 := by
      rw [ih.2]
      exact pow_ne_zero _ (by omega)
    refine ⟨(ltPoly_monic π).comp ih.1 hd, ?_⟩
    rw [ltPolyIter_succ, natDegree_comp, natDegree_ltPoly, ih.2, pow_succ, mul_comm]

end LTPoly

section Valuation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L]
variable {π : 𝒪[K]}

omit [ValuativeRel L] [ValuativeExtension K L] in
/- English proof (translation)
Simplify using `only [ltPoly, Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X, Polynomial.map_pow, map_add, map_mul, aeval_C, aeval_X, map_pow]`. Both sides reduce to the same expression.
-/
theorem aeval_ltPoly (z : L) :
    aeval z ((ltPoly π).map (algebraMap 𝒪[K] K)) =
      algebraMap K L (π : K) * z + z ^ Nat.card 𝓀[K] := by
  simp only [ltPoly, Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X,
    Polynomial.map_pow, map_add, map_mul, aeval_C, aeval_X, map_pow]
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/- English proof (translation)
The claim follows from `(Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) _).mpr c.2`.
-/
theorem valuation_algebraMap_integer_le_one (c : 𝒪[K]) :
    valuation L (algebraMap K L (c : K)) ≤ 1 :=
  (Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) _).mpr c.2

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/- English proof (translation)
The claim follows from `(Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) _).mpr (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hπ.not_isUnit)`.
-/
theorem valuation_algebraMap_lt_one_of_irreducible (hπ : Irreducible π) :
    valuation L (algebraMap K L (π : K)) < 1 :=
  (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) _).mpr
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hπ.not_isUnit)

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' K`. Rewrite using `[aeval_ltPoly]`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_algebraMap_integer_le_one π)) hz`.

Rewrite using `[map_pow]`. Conclude with `pow_lt_one₀ zero_le hz (by omega)`.
-/
theorem valuation_aeval_ltPoly_lt_one {z : L} (hz : valuation L z < 1) :
    valuation L (aeval z ((ltPoly π).map (algebraMap 𝒪[K] K))) < 1 := by
  have hq := one_lt_card_residueField' K
  rw [aeval_ltPoly]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_algebraMap_integer_le_one π)) hz
  · rw [map_pow]
    exact pow_lt_one₀ zero_le hz (by omega)

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' K`. Rewrite using `[aeval_ltPoly, Valuation.map_add_eq_of_lt_right, map_pow]`. Rewrite using `[map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem valuation_aeval_ltPoly_of_one_le (hπ : Irreducible π) {z : L} (hz : 1 ≤ valuation L z) :
    valuation L (aeval z ((ltPoly π).map (algebraMap 𝒪[K] K))) = valuation L z ^ Nat.card 𝓀[K] := by
  have hq := one_lt_card_residueField' K
  rw [aeval_ltPoly, Valuation.map_add_eq_of_lt_right, map_pow]
  rw [map_mul, map_pow]
  calc valuation L (algebraMap K L (π : K)) * valuation L z < valuation L z :=
        mul_lt_of_lt_one_left (lt_of_lt_of_le zero_lt_one hz)
          (valuation_algebraMap_lt_one_of_irreducible hπ)
    _ ≤ valuation L z ^ Nat.card 𝓀[K] := le_self_pow₀ hz (by omega)

omit [ValuativeRel L] [ValuativeExtension K L] in
/- English proof (translation)
Simplify using `only [ltPoly, Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X, Polynomial.map_pow, derivative_C_mul_X, derivative_X_pow, map_add, aeval_C, map_mul, map_pow, aeval_X, map_natCast]`. Both sides reduce to the same expression.
-/
theorem aeval_derivative_ltPoly (z : L) :
    aeval z (derivative ((ltPoly π).map (algebraMap 𝒪[K] K))) =
      algebraMap K L (π : K) + (Nat.card 𝓀[K] : L) * z ^ (Nat.card 𝓀[K] - 1) := by
  simp only [ltPoly, Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X,
    Polynomial.map_pow, derivative_C_mul_X, derivative_X_pow, map_add, aeval_C,
    map_mul, map_pow, aeval_X, map_natCast]
  rfl

/- English proof (translation)
Establish `h : (Nat.card 𝓀[K] : 𝒪[K]) ∈ IsLocalRing.maximalIdeal 𝒪[K]`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_natCast]`. Use `Fintype.ofFinite 𝓀[K]` as an intermediate fact. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `FiniteField.cast_card_eq_zero 𝓀[K]`.

Rewrite `h` using `[hπ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Conclude with `h`.
-/
theorem exists_card_residueField_eq (hπ : Irreducible π) :
    ∃ c : 𝒪[K], (Nat.card 𝓀[K] : 𝒪[K]) = π * c := by
  have h : (Nat.card 𝓀[K] : 𝒪[K]) ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[K]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero 𝓀[K]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at h
  exact h

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' K`. Take `⟨c, hc⟩` from `exists_card_residueField_eq hπ`. Establish `hcL : (Nat.card 𝓀[K] : L) = algebraMap K L (π : K) * algebraMap K L (c : K)`. Rewrite using `[← map_mul, ← Subring.coe_mul, ← hc]`. Simplify using the standard rewrite rules.

Rewrite using `[aeval_derivative_ltPoly, hcL, mul_assoc, ← mul_one_add]`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Rewrite using `[ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]`. Conclude with `fun h => hπ.ne_zero (Subtype.ext h)`. Use `(Valuation.ne_zero_iff (valuation L)).mp ?_` and prove the remaining obligations.

Rewrite using `[Valuation.map_one_add_of_lt]`. Conclude with `one_ne_zero`. Rewrite using `[map_mul, map_pow]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_algebraMap_integer_le_one c)) (pow_lt_one₀ zero_le hz (by omega))`.
-/
theorem aeval_derivative_ltPoly_ne_zero (hπ : Irreducible π) {z : L} (hz : valuation L z < 1) :
    aeval z (derivative ((ltPoly π).map (algebraMap 𝒪[K] K))) ≠ 0 := by
  have hq := one_lt_card_residueField' K
  obtain ⟨c, hc⟩ := exists_card_residueField_eq hπ
  have hcL : (Nat.card 𝓀[K] : L) = algebraMap K L (π : K) * algebraMap K L (c : K) := by
    rw [← map_mul, ← Subring.coe_mul, ← hc]
    simp
  rw [aeval_derivative_ltPoly, hcL, mul_assoc, ← mul_one_add]
  refine mul_ne_zero ?_ ?_
  · rw [ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  · refine (Valuation.ne_zero_iff (valuation L)).mp ?_
    rw [Valuation.map_one_add_of_lt]
    · exact one_ne_zero
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_algebraMap_integer_le_one c))
        (pow_lt_one₀ zero_le hz (by omega))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa [ltPolyIter_zero] using hz`. Consider the case `succ n ih`. Rewrite using `[ltPolyIter_succ, Polynomial.map_comp, aeval_comp]`. Conclude with `valuation_aeval_ltPoly_lt_one ih`.
-/
theorem valuation_aeval_ltPolyIter_lt_one (n : ℕ) {z : L}
    (hz : valuation L z < 1) :
    valuation L (aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K))) < 1 := by
  induction n with
  | zero => simpa [ltPolyIter_zero] using hz
  | succ n ih =>
    rw [ltPolyIter_succ, Polynomial.map_comp, aeval_comp]
    exact valuation_aeval_ltPoly_lt_one ih

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa [ltPolyIter_zero] using hz`. Consider the case `succ n ih`. Rewrite using `[ltPolyIter_succ, Polynomial.map_comp, aeval_comp, valuation_aeval_ltPoly_of_one_le hπ ih]`. Conclude with `one_le_pow₀ ih`.
-/
theorem one_le_valuation_aeval_ltPolyIter (hπ : Irreducible π) (n : ℕ) {z : L}
    (hz : 1 ≤ valuation L z) :
    1 ≤ valuation L (aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K))) := by
  induction n with
  | zero => simpa [ltPolyIter_zero] using hz
  | succ n ih =>
    rw [ltPolyIter_succ, Polynomial.map_comp, aeval_comp, valuation_aeval_ltPoly_of_one_le hπ ih]
    exact one_le_pow₀ ih

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `one_le_valuation_aeval_ltPolyIter hπ n (not_lt.mp h)` as an intermediate fact. Rewrite `this` using `[hz, map_zero]`. Conclude with `not_le.mpr zero_lt_one this`.
-/
theorem valuation_lt_one_of_aeval_ltPolyIter_eq_zero (hπ : Irreducible π) (n : ℕ) {z : L}
    (hz : aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0) : valuation L z < 1 := by
  by_contra h
  have := one_le_valuation_aeval_ltPolyIter hπ n (not_lt.mp h)
  rw [hz, map_zero] at this
  exact not_le.mpr zero_lt_one this

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [ltPolyIter_zero]`. Consider the case `succ n ih`. Rewrite using `[ltPolyIter_succ, Polynomial.map_comp, derivative_comp, map_mul, aeval_comp]`. Conclude with `mul_ne_zero ih (aeval_derivative_ltPoly_ne_zero hπ (valuation_aeval_ltPolyIter_lt_one n hz))`.
-/
theorem aeval_derivative_ltPolyIter_ne_zero (hπ : Irreducible π) (n : ℕ) {z : L}
    (hz : valuation L z < 1) :
    aeval z (derivative ((ltPolyIter π n).map (algebraMap 𝒪[K] K))) ≠ 0 := by
  induction n with
  | zero => simp [ltPolyIter_zero]
  | succ n ih =>
    rw [ltPolyIter_succ, Polynomial.map_comp, derivative_comp, map_mul, aeval_comp]
    exact mul_ne_zero ih
      (aeval_derivative_ltPoly_ne_zero hπ (valuation_aeval_ltPolyIter_lt_one n hz))

end Valuation

section Separable

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

/- English proof (translation)
Rewrite using `[separable_def]`. Set `_` to `algebraicValuativeRel K (AlgebraicClosure K)`. Establish `_` using `algebraicValuativeRel_valuativeExtension K (AlgebraicClosure K)`. Use `(isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).mpr fun a => ?_` and prove the remaining obligations. Distinguish the cases in `ha : valuation (AlgebraicClosure K) a < 1`.

Conclude with `Or.inr (aeval_derivative_ltPolyIter_ne_zero hπ n ha)`. Conclude with `Or.inl fun h => ha (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n h)`.
-/
theorem separable_ltPolyIter (hπ : Irreducible π) (n : ℕ) :
    ((ltPolyIter π n).map (algebraMap 𝒪[K] K)).Separable := by
  rw [separable_def]
  let _ := algebraicValuativeRel K (AlgebraicClosure K)
  have _ := algebraicValuativeRel_valuativeExtension K (AlgebraicClosure K)
  refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).mpr fun a => ?_
  by_cases ha : valuation (AlgebraicClosure K) a < 1
  · exact Or.inr (aeval_derivative_ltPolyIter_ne_zero hπ n ha)
  · exact Or.inl fun h => ha (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n h)

end Separable

section Module

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

/- English proof (translation)
Establish `h : Ideal.span {π ^ n} = IsLocalRing.maximalIdeal 𝒪[K] ^ n`. Rewrite using `[hπ.maximalIdeal_eq, Ideal.span_singleton_pow]`. Rewrite using `[h, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field 𝒪[K]), Submodule.cardQuot_apply]`. Both sides reduce to the same expression.
-/
theorem card_quotient_span_pow (hπ : Irreducible π) (n : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {π ^ n}) = Nat.card 𝓀[K] ^ n := by
  have h : Ideal.span {π ^ n} = IsLocalRing.maximalIdeal 𝒪[K] ^ n := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [h, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime
    (IsDiscreteValuationRing.not_a_field 𝒪[K]), Submodule.cardQuot_apply]
  rfl

variable {M : Type*} [AddCommGroup M] [Module 𝒪[K] M]

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Use `⟨0, Submodule.zero_mem _, fun a => by simp, fun m hm => ⟨0, ?_⟩⟩` and prove the remaining obligations. Rewrite `hm` using `[Submodule.mem_torsionBy_iff, pow_zero, one_smul]`. Rewrite using `[hm, smul_zero]`.

Consider the case `succ m`. Establish `hq` using `one_lt_card_residueField' K`. Use `set T := Submodule.torsionBy 𝒪[K] M (π ^ (m + 1))`. Establish `hle : Submodule.torsionBy 𝒪[K] M (π ^ m) ≤ T` using `Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow π m.le_succ)`. Establish `hfin : Finite T` using `Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)`.

Take `⟨l, hlT, hlm⟩ : ∃ l ∈ T, l ∉ Submodule.torsionBy 𝒪[K] M (π ^ m)` from `by by_contra! h`. Establish `heq : T = Submodule.torsionBy 𝒪[K] M (π ^ m)` using `le_antisymm h hle`. Use `hcard (m + 1)` as an intermediate fact. Express the relevant statement in the definitionally equal form `Nat.card T = _ at this`. Rewrite `this` using `[heq, hcard m]`.

Conclude with `absurd this (Nat.pow_lt_pow_right hq m.lt_succ_self).ne`. Establish `hann : ∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ (m + 1)}`. Introduce `a`. Prove the components needed by the constructor for the conclusion. Introduce `ha`.

Distinguish the cases in `ha0 : a = 0`. Rewrite using `[ha0]`. Conclude with `Ideal.zero_mem _`. Take `⟨k, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ`. Distinguish the cases in `hk : m + 1 ≤ k`.

Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow π hk) _`. It suffices to derive a contradiction. Use `hlm ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_torsionBy_iff]`.

Establish `hk' : π ^ k • l = 0`. Establish `: (↑u⁻¹ : 𝒪[K]) • ((↑u * π ^ k) • l) = 0` using `by rw [ha, smul_zero]`. Rewrite `this` using `[smul_smul, ← mul_assoc, Units.inv_mul, one_mul]`. Then use the resulting hypothesis. Establish `: π ^ m = π ^ (m - k) * π ^ k`. Rewrite using `[← pow_add]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, mul_smul, hk', smul_zero]`. Introduce `ha`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`.

Rewrite using `[mul_smul, (Submodule.mem_torsionBy_iff _ _).mp hlT, smul_zero]`. Use `⟨l, hlT, hann, fun x hx => ?_⟩` and prove the remaining obligations. Set `ψ : 𝒪[K] →ₗ[𝒪[K]] T` to `(LinearMap.toSpanSingleton 𝒪[K] M l).codRestrict T fun a => T.smul_mem a hlT`. Establish `hker : LinearMap.ker ψ = Ideal.span {π ^ (m + 1)}`. Use extensionality with `a`.

Rewrite using `[LinearMap.mem_ker, ← hann a]`. Conclude with `⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩`. Establish `hcardr : Nat.card (LinearMap.range ψ) = Nat.card T`. Rewrite using `[← Nat.card_congr (LinearMap.quotKerEquivRange ψ).toEquiv, hker, card_quotient_span_pow hπ, hcard]`. Establish `hbij` using `(Subtype.val_injective : Function.Injective (Subtype.val : LinearMap.range ψ → T)).bijective_of_nat_card_le hcardr.ge`.

Take `⟨⟨_, ⟨a, rfl⟩⟩, hr⟩` from `hbij.2 ⟨x, hx⟩`. Conclude with `⟨a, congrArg Subtype.val hr⟩`.
-/
theorem exists_generator_torsionBy (hπ : Irreducible π)
    (hcard : ∀ k, Nat.card (Submodule.torsionBy 𝒪[K] M (π ^ k)) = Nat.card 𝓀[K] ^ k) (n : ℕ) :
    ∃ l : M, l ∈ Submodule.torsionBy 𝒪[K] M (π ^ n) ∧
      (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      ∀ m ∈ Submodule.torsionBy 𝒪[K] M (π ^ n), ∃ a : 𝒪[K], a • l = m := by
  cases n with
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun a => by simp, fun m hm => ⟨0, ?_⟩⟩
    rw [Submodule.mem_torsionBy_iff, pow_zero, one_smul] at hm
    rw [hm, smul_zero]
  | succ m =>
    have hq := one_lt_card_residueField' K
    set T := Submodule.torsionBy 𝒪[K] M (π ^ (m + 1))
    have hle : Submodule.torsionBy 𝒪[K] M (π ^ m) ≤ T :=
      Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow π m.le_succ)
    have hfin : Finite T := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    obtain ⟨l, hlT, hlm⟩ : ∃ l ∈ T, l ∉ Submodule.torsionBy 𝒪[K] M (π ^ m) := by
      by_contra! h
      have heq : T = Submodule.torsionBy 𝒪[K] M (π ^ m) := le_antisymm h hle
      have := hcard (m + 1)
      change Nat.card T = _ at this
      rw [heq, hcard m] at this
      exact absurd this (Nat.pow_lt_pow_right hq m.lt_succ_self).ne
    have hann : ∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ (m + 1)} := by
      intro a
      constructor
      · intro ha
        by_cases ha0 : a = 0
        · rw [ha0]
          exact Ideal.zero_mem _
        obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
        by_cases hk : m + 1 ≤ k
        · rw [Ideal.mem_span_singleton]
          exact Dvd.dvd.mul_left (pow_dvd_pow π hk) _
        · exfalso
          refine hlm ?_
          rw [Submodule.mem_torsionBy_iff]
          have hk' : π ^ k • l = 0 := by
            have : (↑u⁻¹ : 𝒪[K]) • ((↑u * π ^ k) • l) = 0 := by rw [ha, smul_zero]
            rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
          have : π ^ m = π ^ (m - k) * π ^ k := by
            rw [← pow_add]
            congr 1
            omega
          rw [this, mul_smul, hk', smul_zero]
      · intro ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [mul_smul, (Submodule.mem_torsionBy_iff _ _).mp hlT, smul_zero]
    refine ⟨l, hlT, hann, fun x hx => ?_⟩
    let ψ : 𝒪[K] →ₗ[𝒪[K]] T :=
      (LinearMap.toSpanSingleton 𝒪[K] M l).codRestrict T fun a => T.smul_mem a hlT
    have hker : LinearMap.ker ψ = Ideal.span {π ^ (m + 1)} := by
      ext a
      rw [LinearMap.mem_ker, ← hann a]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hcardr : Nat.card (LinearMap.range ψ) = Nat.card T := by
      rw [← Nat.card_congr (LinearMap.quotKerEquivRange ψ).toEquiv, hker,
        card_quotient_span_pow hπ, hcard]
    have hbij := (Subtype.val_injective : Function.Injective
      (Subtype.val : LinearMap.range ψ → T)).bijective_of_nat_card_le hcardr.ge
    obtain ⟨⟨_, ⟨a, rfl⟩⟩, hr⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨a, congrArg Subtype.val hr⟩

end Module

section Torsion

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} {hπ : Irreducible π}

/- English proof (translation)
Use `t2Space_of_isValuativeTopology Ω` as an intermediate fact. Proceed by induction on `n with`. Consider the case `zero => simp [ltPolyIter_zero]`. Consider the case `succ n ih`. Rewrite using `[pow_succ', mul_smul, lubinTate_uniformizer_smul_val, psEval_polynomial, ih, ltPolyIter_succ, Polynomial.map_comp, aeval_comp]`.
-/
theorem ltPoly_pow_smul_val (n : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))) :
    (π ^ n • x).val = aeval x.val ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) := by
  have := t2Space_of_isValuativeTopology Ω
  induction n with
  | zero => simp [ltPolyIter_zero]
  | succ n ih =>
    rw [pow_succ', mul_smul, lubinTate_uniformizer_smul_val, psEval_polynomial, ih,
      ltPolyIter_succ, Polynomial.map_comp, aeval_comp]

/- English proof (translation)
Rewrite using `[mem_lubinTateTorsion, ← ltPoly_pow_smul_val]`. Conclude with `⟨fun h => by rw [h]; rfl, fun h => IdealPoint.ext h⟩`.
-/
theorem mem_lubinTateTorsion_ltPoly_iff (n : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))) :
    x ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n ↔
      aeval x.val ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0 := by
  rw [mem_lubinTateTorsion, ← ltPoly_pow_smul_val]
  exact ⟨fun h => by rw [h]; rfl, fun h => IdealPoint.ext h⟩

variable [IsSepClosed Ω]

/- English proof (translation)
Use `set p := (ltPolyIter π n).map (algebraMap 𝒪[K] K)`. Establish `hp0 : p ≠ 0` using `((ltPolyIter_monic π n).1.map _).ne_zero`. Establish `hsep : p.Separable` using `separable_ltPolyIter hπ n`. Establish `hcard : Fintype.card (p.rootSet Ω) = Nat.card 𝓀[K] ^ n`. Rewrite using `[card_rootSet_eq_natDegree hsep (IsSepClosed.splits_codomain p hsep), natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), (ltPolyIter_monic π n).2]`.

Rewrite using `[← hcard, ← Nat.card_eq_fintype_card]`. Use `Nat.card_congr (Equiv.ofBijective (fun x => ⟨x.1.val, ?_⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[mem_rootSet' (p := p)]`. Conclude with `⟨Polynomial.map_ne_zero hp0, (mem_lubinTateTorsion_ltPoly_iff n x.1).mp x.2⟩`. Introduce `x y h`.

Conclude with `Subtype.ext (IdealPoint.ext (by simpa using congrArg Subtype.val h))`. Introduce and unpack `⟨z, hz⟩`. Rewrite `hz` using `[mem_rootSet' (p := p)]`. Use `⟨⟨IdealPoint.mk z (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n hz.2), ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `(mem_lubinTateTorsion_ltPoly_iff n _).mpr hz.2`.
-/
theorem card_lubinTateTorsion_ltPoly (n : ℕ) :
    Nat.card (lubinTateTorsion Ω (hπ := hπ) (isLubinTateSeries_ltPoly π) n) =
      Nat.card 𝓀[K] ^ n := by
  classical
  set p := (ltPolyIter π n).map (algebraMap 𝒪[K] K)
  have hp0 : p ≠ 0 := ((ltPolyIter_monic π n).1.map _).ne_zero
  have hsep : p.Separable := separable_ltPolyIter hπ n
  have hcard : Fintype.card (p.rootSet Ω) = Nat.card 𝓀[K] ^ n := by
    rw [card_rootSet_eq_natDegree hsep (IsSepClosed.splits_codomain p hsep),
      natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K),
      (ltPolyIter_monic π n).2]
  rw [← hcard, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨x.1.val, ?_⟩) ⟨?_, ?_⟩)
  · rw [mem_rootSet' (p := p)]
    exact ⟨Polynomial.map_ne_zero hp0, (mem_lubinTateTorsion_ltPoly_iff n x.1).mp x.2⟩
  · intro x y h
    exact Subtype.ext (IdealPoint.ext (by simpa using congrArg Subtype.val h))
  · rintro ⟨z, hz⟩
    rw [mem_rootSet' (p := p)] at hz
    refine ⟨⟨IdealPoint.mk z (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n hz.2), ?_⟩, rfl⟩
    exact (mem_lubinTateTorsion_ltPoly_iff n _).mpr hz.2

variable {f : PowerSeries 𝒪[K]}

omit [IsSepClosed Ω] in

/- English proof (translation)
Rewrite using `[mem_lubinTateTorsion, mem_lubinTateTorsion, ← map_smul, LinearEquiv.map_eq_zero_iff]`.
-/
theorem lubinTatePointEquiv_mem_torsion_iff {g : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)
    (hg : IsLubinTateSeries π g) (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hg)) :
    lubinTatePointEquiv hf hg x ∈ lubinTateTorsion Ω hf n ↔ x ∈ lubinTateTorsion Ω hg n := by
  rw [mem_lubinTateTorsion, mem_lubinTateTorsion, ← map_smul,
    LinearEquiv.map_eq_zero_iff]

/- English proof (translation)
Rewrite using `[← card_lubinTateTorsion_ltPoly (Ω := Ω) (hπ := hπ) n]`. Conclude with `Nat.card_congr ((lubinTatePointEquiv hf (isLubinTateSeries_ltPoly π)).toEquiv.subtypeEquiv fun x => (lubinTatePointEquiv_mem_torsion_iff hf _ n x).symm).symm`.
-/
theorem card_lubinTateTorsion (hf : IsLubinTateSeries π f) (n : ℕ) :
    Nat.card (lubinTateTorsion Ω (hπ := hπ) hf n) = Nat.card 𝓀[K] ^ n := by
  rw [← card_lubinTateTorsion_ltPoly (Ω := Ω) (hπ := hπ) n]
  exact Nat.card_congr ((lubinTatePointEquiv hf (isLubinTateSeries_ltPoly π)).toEquiv.subtypeEquiv
    fun x => (lubinTatePointEquiv_mem_torsion_iff hf _ n x).symm).symm

/- English proof (translation)
The claim follows from `exists_generator_torsionBy hπ (card_lubinTateTorsion (hπ := hπ) hf) n`.
-/
theorem exists_generator_lubinTateTorsion (hf : IsLubinTateSeries π f) (n : ℕ) :
    ∃ l ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      ∀ m ∈ lubinTateTorsion Ω (hπ := hπ) hf n, ∃ a : 𝒪[K], a • l = m :=
  exists_generator_torsionBy hπ (card_lubinTateTorsion (hπ := hπ) hf) n

/- English proof (translation)
Take `⟨l, hl, hann, hgen⟩` from `exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n`. Set `ψ : 𝒪[K] →ₗ[𝒪[K]] lubinTateTorsion Ω (hπ` to `hπ) hf n := (LinearMap.toSpanSingleton 𝒪[K] _ l).codRestrict _ fun a => Submodule.smul_mem _ a hl`. Establish `hker : LinearMap.ker ψ = Ideal.span {π ^ n}`. Use extensionality with `a`. Rewrite using `[LinearMap.mem_ker, ← hann a]`.

Conclude with `⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩`. Establish `hsurj : Function.Surjective ψ` using `fun ⟨m, hm⟩ => by`. Take `⟨a, ha⟩` from `hgen m hm`. Conclude with `⟨a, Subtype.ext ha⟩`. Conclude with `⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj)⟩`.
-/
theorem nonempty_linearEquiv_lubinTateTorsion (hf : IsLubinTateSeries π f) (n : ℕ) :
    Nonempty ((𝒪[K] ⧸ Ideal.span {π ^ n}) ≃ₗ[𝒪[K]] lubinTateTorsion Ω (hπ := hπ) hf n) := by
  obtain ⟨l, hl, hann, hgen⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  let ψ : 𝒪[K] →ₗ[𝒪[K]] lubinTateTorsion Ω (hπ := hπ) hf n :=
    (LinearMap.toSpanSingleton 𝒪[K] _ l).codRestrict _ fun a => Submodule.smul_mem _ a hl
  have hker : LinearMap.ker ψ = Ideal.span {π ^ n} := by
    ext a
    rw [LinearMap.mem_ker, ← hann a]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hsurj : Function.Surjective ψ := fun ⟨m, hm⟩ => by
    obtain ⟨a, ha⟩ := hgen m hm
    exact ⟨a, Subtype.ext ha⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj)⟩

end Torsion

section Eisenstein

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

/- English proof (translation)
Establish `hres : IsLocalRing.residue 𝒪[K] π = 0` using `(IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)`. Proceed by induction on `n with`. Consider the case `zero => simp [ltPolyIter_zero]`. Consider the case `succ n ih`. Rewrite using `[ltPolyIter_succ, Polynomial.map_comp, ih, ltPoly]`.

Simplify using `[hres, ← pow_mul, pow_succ]`.
-/
theorem map_residue_ltPolyIter (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ) :
    (ltPolyIter π n).map (IsLocalRing.residue 𝒪[K]) = X ^ Nat.card 𝓀[K] ^ n := by
  have hres : IsLocalRing.residue 𝒪[K] π = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  induction n with
  | zero => simp [ltPolyIter_zero]
  | succ n ih =>
    rw [ltPolyIter_succ, Polynomial.map_comp, ih, ltPoly]
    simp [hres, ← pow_mul, pow_succ]

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' K`. Proceed by induction on `n with`. Consider the case `zero => simp [ltPolyIter_zero]`. Consider the case `succ n ih`. Rewrite using `[ltPolyIter_succ, coeff_zero_eq_eval_zero, eval_comp, ← coeff_zero_eq_eval_zero, ih, ltPoly]`.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_zero_ltPolyIter (π : 𝒪[K]) (n : ℕ) : (ltPolyIter π n).coeff 0 = 0 := by
  have hq := one_lt_card_residueField' K
  induction n with
  | zero => simp [ltPolyIter_zero]
  | succ n ih =>
    rw [ltPolyIter_succ, coeff_zero_eq_eval_zero, eval_comp, ← coeff_zero_eq_eval_zero, ih, ltPoly]
    simp
    omega

def ltEisenstein (π : 𝒪[K]) (n : ℕ) : 𝒪[K][X] :=
  C π + ltPolyIter π n ^ (Nat.card 𝓀[K] - 1)

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' K`. Establish `hm` using `(ltPolyIter_monic π n).1.pow (Nat.card 𝓀[K] - 1)`. Establish `hd : (ltPolyIter π n ^ (Nat.card 𝓀[K] - 1)).natDegree = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n`. Rewrite using `[natDegree_pow, (ltPolyIter_monic π n).2]`. Establish `hpos : 0 < (ltPolyIter π n ^ (Nat.card 𝓀[K] - 1)).natDegree`.

Rewrite using `[hd]`. Conclude with `Nat.mul_pos (by omega) (pow_pos (by omega) n)`. Establish `hlt : degree (C π) < degree (ltPolyIter π n ^ (Nat.card 𝓀[K] - 1))` using `lt_of_le_of_lt degree_C_le (by rw [degree_eq_natDegree hm.ne_zero]; exact_mod_cast hpos)`. Use `⟨hm.add_of_right hlt, ?_⟩` and prove the remaining obligations. Rewrite using `[ltEisenstein, natDegree_add_eq_right_of_degree_lt hlt, hd]`.
-/
theorem ltEisenstein_monic (π : 𝒪[K]) (n : ℕ) : (ltEisenstein π n).Monic ∧
    (ltEisenstein π n).natDegree = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  have hq := one_lt_card_residueField' K
  have hm := (ltPolyIter_monic π n).1.pow (Nat.card 𝓀[K] - 1)
  have hd : (ltPolyIter π n ^ (Nat.card 𝓀[K] - 1)).natDegree =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
    rw [natDegree_pow, (ltPolyIter_monic π n).2]
  have hpos : 0 < (ltPolyIter π n ^ (Nat.card 𝓀[K] - 1)).natDegree := by
    rw [hd]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) n)
  have hlt : degree (C π) < degree (ltPolyIter π n ^ (Nat.card 𝓀[K] - 1)) :=
    lt_of_le_of_lt degree_C_le (by rw [degree_eq_natDegree hm.ne_zero]; exact_mod_cast hpos)
  refine ⟨hm.add_of_right hlt, ?_⟩
  rw [ltEisenstein, natDegree_add_eq_right_of_degree_lt hlt, hd]

/- English proof (translation)
Establish `hres : IsLocalRing.residue 𝒪[K] π = 0` using `(IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)`. Rewrite using `[ltEisenstein, Polynomial.map_add, map_C, hres, C_0, zero_add, Polynomial.map_pow, map_residue_ltPolyIter π hπ, ← pow_mul, mul_comm]`.
-/
theorem map_residue_ltEisenstein (hπ : Irreducible π) (n : ℕ) :
    (ltEisenstein π n).map (IsLocalRing.residue 𝒪[K]) =
      X ^ ((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n) := by
  have hres : IsLocalRing.residue 𝒪[K] π = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  rw [ltEisenstein, Polynomial.map_add, map_C, hres, C_0, zero_add, Polynomial.map_pow,
    map_residue_ltPolyIter π hπ, ← pow_mul, mul_comm]

/- English proof (translation)
Rewrite using `[(ltEisenstein_monic π n).1.leadingCoeff]`. Conclude with `fun h => (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top ((Ideal.eq_top_iff_one _).mpr h)`. Use `mem {k} hk := by`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, ← coeff_map, map_residue_ltEisenstein hπ, coeff_X_pow]`. Rewrite `hk` using `[(ltEisenstein_monic π n).2]`.

Simplify using `[hk.ne]`. Use `notMem := by`. Establish `hq` using `one_lt_card_residueField' K`. Establish `h0 : (ltEisenstein π n).coeff 0 = π`. Rewrite using `[ltEisenstein, coeff_add, coeff_C_zero, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, coeff_zero_ltPolyIter, zero_pow (by omega), add_zero]`.

Rewrite using `[h0, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Introduce and unpack `⟨c, hc⟩`. Establish `: (1 : 𝒪[K]) = π * c`. Use `mul_left_cancel₀ hπ.ne_zero ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hπ.not_isUnit (Units.mkOfMulEqOne π c this.symm).isUnit`.
-/
theorem isEisensteinAt_ltEisenstein (hπ : Irreducible π) (n : ℕ) :
    (ltEisenstein π n).IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) where
  leading := by
    rw [(ltEisenstein_monic π n).1.leadingCoeff]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
      ((Ideal.eq_top_iff_one _).mpr h)
  mem {k} hk := by
    rw [← IsLocalRing.residue_eq_zero_iff, ← coeff_map, map_residue_ltEisenstein hπ, coeff_X_pow]
    rw [(ltEisenstein_monic π n).2] at hk
    simp [hk.ne]
  notMem := by
    have hq := one_lt_card_residueField' K
    have h0 : (ltEisenstein π n).coeff 0 = π := by
      rw [ltEisenstein, coeff_add, coeff_C_zero, coeff_zero_eq_eval_zero, eval_pow,
        ← coeff_zero_eq_eval_zero, coeff_zero_ltPolyIter, zero_pow (by omega), add_zero]
    rw [h0, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have : (1 : 𝒪[K]) = π * c := by
      refine mul_left_cancel₀ hπ.ne_zero ?_
      calc π * 1 = π := mul_one π
        _ = π ^ 2 * c := hc
        _ = π * (π * c) := by ring
    exact hπ.not_isUnit (Units.mkOfMulEqOne π c this.symm).isUnit

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' K`. Use `set μ := aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K))`. Rewrite `h1` using `[ltPolyIter_succ, Polynomial.map_comp, aeval_comp, aeval_ltPoly]`. Establish `h2 : μ * (algebraMap K L (π : K) + μ ^ (Nat.card 𝓀[K] - 1)) = 0`. Rewrite using `[mul_add, ← pow_succ', Nat.sub_add_cancel hq.le, mul_comm]`.

Conclude with `h1`. Establish `h3` using `(mul_eq_zero.mp h2).resolve_left h0`. Rewrite using `[ltEisenstein, Polynomial.map_add, map_C, Polynomial.map_pow, map_add, aeval_C, map_pow]`. Conclude with `h3`.
-/
theorem aeval_ltEisenstein_eq_zero {L : Type*} [Field L] [Algebra K L] {n : ℕ} {z : L}
    (h1 : aeval z ((ltPolyIter π (n + 1)).map (algebraMap 𝒪[K] K)) = 0)
    (h0 : aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) ≠ 0) :
    aeval z ((ltEisenstein π n).map (algebraMap 𝒪[K] K)) = 0 := by
  have hq := one_lt_card_residueField' K
  set μ := aeval z ((ltPolyIter π n).map (algebraMap 𝒪[K] K))
  rw [ltPolyIter_succ, Polynomial.map_comp, aeval_comp, aeval_ltPoly] at h1
  have h2 : μ * (algebraMap K L (π : K) + μ ^ (Nat.card 𝓀[K] - 1)) = 0 := by
    rw [mul_add, ← pow_succ', Nat.sub_add_cancel hq.le, mul_comm]
    exact h1
  have h3 := (mul_eq_zero.mp h2).resolve_left h0
  rw [ltEisenstein, Polynomial.map_add, map_C, Polynomial.map_pow, map_add, aeval_C, map_pow]
  exact h3

end Eisenstein

end FormalGroup

end GroundTheory.LocalField

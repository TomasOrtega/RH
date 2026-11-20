import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum]`. Rewrite using `[Finset.prod_comm, Finsupp.prod]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single v.1]`. Simplify using `[blockWeight]`.

Introduce `k _ hk`. Simplify using `[blockWeight, Pi.single_eq_of_ne hk]`. Simplify using the standard rewrite rules.
-/
theorem prod_pow_blockWeight {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {M : Type*}
    [CommMonoid M] (w : K → M) (e : (Σ k, ι k) →₀ ℕ) :
    ∏ k, w k ^ (Finsupp.weight (blockWeight ι) e k) = e.prod fun v n => w v.1 ^ n := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_eq_single v.1]
  · simp [blockWeight]
  · intro k _ hk
    simp [blockWeight, Pi.single_eq_of_ne hk]
  · simp

/- English proof (translation)
Introduce `F _ K _ _ ι P _ u hu f b hf`. Use `set L := FractionRing (MRing ι F ⧸ P)`. Set `φ : MRing ι F →+* L` to `(algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)`. Set `w : K → L` to `fun k => φ (X ⟨k, u k⟩)`. Establish `hw : ∀ k, w k ≠ 0` using `fun k => by`.

Simplify using `only [w, φ, RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hu k`. Establish `hD : φ (chartMonomial u b) = ∏ k, w k ^ b k`. Simplify using `[chartMonomial, w, map_prod, map_pow]`. Establish `hC : ∀ c : F, φ (C c) = algebraMap F L c` using `fun c => by`.

Simplify using `only [φ, RingHom.comp_apply]`. Rewrite using `[← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk F, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]`. Establish `hmono : ∀ e ∈ f.support, chartMap P u (monomial e (coeff e f)) * ∏ k, w k ^ b k = φ (monomial e (coeff e f))`. Introduce `e he`. Establish `hwe : Finsupp.weight (blockWeight ι) e = b` using `hf (mem_support_iff.mp he)`.

Rewrite using `[← hwe, prod_pow_blockWeight, chartMap, aeval_monomial, mul_assoc, ← Finsupp.prod_mul, monomial_eq, map_mul, hC, Finsupp.prod, Finsupp.prod, map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(φ (X v) / w v.1) ^ e v * w v.1 ^ e v = φ (X v ^ e v)`. Rewrite using `[← mul_pow, div_mul_cancel₀ _ (hw v.1), map_pow]`.

Express the relevant statement in the definitionally equal form `chartMap P u f = φ f / φ (chartMonomial u b)`. Rewrite using `[hD, eq_div_iff (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hw k))]`. Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl hmono`.
-/
theorem MChartDehomog.proof : MChartDehomog.Statement := by
  intro F _ K _ _ ι P _ u hu f b hf
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  let w : K → L := fun k => φ (X ⟨k, u k⟩)
  have hw : ∀ k, w k ≠ 0 := fun k => by
    simp only [w, φ, RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  have hD : φ (chartMonomial u b) = ∏ k, w k ^ b k := by
    simp [chartMonomial, w, map_prod, map_pow]
  have hC : ∀ c : F, φ (C c) = algebraMap F L c := fun c => by
    simp only [φ, RingHom.comp_apply]
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk F, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hmono : ∀ e ∈ f.support, chartMap P u (monomial e (coeff e f)) * ∏ k, w k ^ b k =
      φ (monomial e (coeff e f)) := by
    intro e he
    have hwe : Finsupp.weight (blockWeight ι) e = b := hf (mem_support_iff.mp he)
    rw [← hwe, prod_pow_blockWeight, chartMap, aeval_monomial, mul_assoc, ← Finsupp.prod_mul,
      monomial_eq, map_mul, hC, Finsupp.prod, Finsupp.prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    change (φ (X v) / w v.1) ^ e v * w v.1 ^ e v = φ (X v ^ e v)
    rw [← mul_pow, div_mul_cancel₀ _ (hw v.1), map_pow]
  change chartMap P u f = φ f / φ (chartMonomial u b)
  rw [hD, eq_div_iff (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hw k))]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl hmono

end

end GroundTheory.Heights₂.Heights.FieldNumbers

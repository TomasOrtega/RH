import Mathlib

noncomputable section
open Module

namespace PI.LocDualGen.EpC

variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]

/- English proof (translation)
Break down `subsingleton_or_nontrivial L with h | h` into its components or cases. Rewrite `hr` using `[Module.finrank_zero_of_subsingleton]`. Conclude with `absurd hr (by norm_num)`. Conclude with `h`.
-/
private theorem nontrivial_of_finrank_eq_two (hr : finrank K L = 2) : Nontrivial L := by
  rcases subsingleton_or_nontrivial L with h | h
  · rw [Module.finrank_zero_of_subsingleton] at hr
    exact absurd hr (by norm_num)
  · exact h

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hsurj : LinearMap.range (Algebra.linearMap K L) = ⊤`. Rewrite using `[LinearMap.range_eq_top]`. Introduce `y`.

Take `⟨a, ha⟩` from `h y`. Conclude with `⟨a, ha⟩`. Establish `h1` using `LinearMap.finrank_range_le (Algebra.linearMap K L)`. Rewrite `h1` using `[hsurj, finrank_top, Module.finrank_self, hr]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_not_mem_range_algebraMap_of_finrank_eq_two (hr : finrank K L = 2) :
    ∃ x : L, x ∉ Set.range (algebraMap K L) := by
  by_contra h
  push Not at h
  have hsurj : LinearMap.range (Algebra.linearMap K L) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨a, ha⟩ := h y
    exact ⟨a, ha⟩
  have h1 := LinearMap.finrank_range_le (Algebra.linearMap K L)
  rw [hsurj, finrank_top, Module.finrank_self, hr] at h1
  omega

/- English proof (translation)
Use `nontrivial_of_finrank_eq_two hr` as an intermediate fact. Establish `hli : LinearIndependent K ![(1 : L), x]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Distinguish the cases in `ht : t = 0`.

Substitute `ht` using the available equality. Simplify using `only [zero_smul, add_zero] at hst`. Use `⟨?_, rfl⟩` and prove the remaining obligations. Establish `h0 : algebraMap K L s = 0`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`.

Conclude with `hst`. Conclude with `(algebraMap K L).injective (by rw [h0, map_zero])`. It suffices to derive a contradiction. Apply `hx` to reduce the goal to its premises. Use `⟨-(s / t), ?_⟩` and prove the remaining obligations.

Establish `h2 : t • x = -(s • (1 : L))`. Rewrite using `[← sub_eq_zero, sub_neg_eq_add, add_comm]`. Conclude with `hst`. Establish `h3 : x = t⁻¹ • (t • x)`. Rewrite using `[smul_smul, inv_mul_cancel₀ ht, one_smul]`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, h3, h2, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]`. Establish `hcard : Fintype.card (Fin 2) = finrank K L`. Rewrite using `[hr, Fintype.card_fin]`. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hb0 : b 0 = 1` using `by simp [b]`.

Establish `hb1 : b 1 = x` using `by simp [b]`. Establish `hy` using `b.sum_repr y`. Rewrite `hy` using `[Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]`. Conclude with `⟨b.repr y 0, b.repr y 1, hy⟩`.
-/
private theorem exists_eq_add_mul_of_finrank_eq_two' (hr : finrank K L = 2) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) (y : L) :
    ∃ a c : K, algebraMap K L a + algebraMap K L c * x = y := by
  have := nontrivial_of_finrank_eq_two hr
  have hli : LinearIndependent K ![(1 : L), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      refine ⟨?_, rfl⟩
      have h0 : algebraMap K L s = 0 := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact hst
      exact (algebraMap K L).injective (by rw [h0, map_zero])
    · exfalso
      apply hx
      refine ⟨-(s / t), ?_⟩
      have h2 : t • x = -(s • (1 : L)) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact hst
      have h3 : x = t⁻¹ • (t • x) := by
        rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [Algebra.algebraMap_eq_smul_one, h3, h2, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hcard : Fintype.card (Fin 2) = finrank K L := by
    rw [hr, Fintype.card_fin]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  have hy := b.sum_repr y
  rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one] at hy
  exact ⟨b.repr y 0, b.repr y 1, hy⟩

/- English proof (translation)
Use `nontrivial_of_finrank_eq_two hr` as an intermediate fact. Take `⟨x, hx⟩` from `exists_not_mem_range_algebraMap_of_finrank_eq_two hr`. Establish `hrep` using `exists_eq_add_mul_of_finrank_eq_two' hr hx`. Take `⟨p, q, hpq0⟩` from `hrep (x ^ 2)`. Establish `hpq : x ^ 2 = algebraMap K L p + algebraMap K L q * x` using `hpq0.symm`.

Distinguish the cases in `hroot : ∃ r : K, r ^ 2 = p + q * r`. Take `⟨r, hr2⟩` from `hroot`. Establish `hfac : (x - algebraMap K L r) * (x - algebraMap K L (q - r)) = 0`. Establish `h' : algebraMap K L (r ^ 2) = algebraMap K L (p + q * r)` using `by rw [hr2]`. Simplify using `only [map_add, map_mul, map_pow, map_sub] at h' ⊢`.

Take the linear combination `hpq - h'`. Distinguish the cases in `hrs : r = q - r`. It suffices to derive a contradiction. Establish `hsq : (x - algebraMap K L r) ^ 2 = 0`. Establish `h'` using `hfac`.

Rewrite `h'` using `[← hrs]`. Rewrite using `[sq]`. Conclude with `h'`. Establish `hz : x - algebraMap K L r = 0` using `hred.eq_zero _ ⟨2, hsq⟩`. Conclude with `hx ⟨r, (sub_eq_zero.mp hz).symm⟩`.

Use `right`. Establish `hd : q - r - r ≠ 0` using `sub_ne_zero.mpr (Ne.symm hrs)`. Establish `hsq : (x - algebraMap K L r) * (x - algebraMap K L r) = algebraMap K L (q - r - r) * (x - algebraMap K L r)`. Establish `h'` using `hfac`. Simplify using `only [map_sub] at h' ⊢`.

Take the linear combination `h'`. Establish `hu : algebraMap K L (q - r - r)⁻¹ * algebraMap K L (q - r - r) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hd, map_one]`. Establish `hback : x - algebraMap K L r = algebraMap K L (q - r - r) * (algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r))`. Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ hd, map_one, one_mul]`.

Use `⟨algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show _ * _ = _`. Take the linear combination `(algebraMap K L (q - r - r)⁻¹) ^ 2 * hsq + algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r) * hu`. Introduce `he`. Rewrite `hback` using `[he, mul_zero, sub_eq_zero]`.

Conclude with `hx ⟨r, hback.symm⟩`. Introduce `he`. Rewrite `hback` using `[he, mul_one]`. Apply `hx` to reduce the goal to its premises. Use `⟨q - r, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_sub] at hback ⊢`. Take the linear combination `-hback`. Use `push Not at hroot left`. Use `⟨⟨0, 1, zero_ne_one⟩, fun a b => mul_comm a b, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Take `⟨a, c, rfl⟩` from `hrep y`. Establish `hN : a * a + a * c * q - c ^ 2 * p ≠ 0`. Introduce `h0`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality.

Apply `hy` to reduce the goal to its premises. Establish `ha : a = 0` using `by simpa using h0`. Simplify using `[ha]`. Apply `hroot (-a / c)` to reduce the goal to its premises. Establish `hci : c * c⁻¹ = 1` using `mul_inv_cancel₀ hc`.

Take the linear combination `(c⁻¹) ^ 2 * h0 + (p * (1 + c * c⁻¹) - q * a * c⁻¹) * hci`. Establish `hprod : (algebraMap K L a + algebraMap K L c * x) * (algebraMap K L (a + c * q) - algebraMap K L c * x) = algebraMap K L (a * a + a * c * q - c ^ 2 * p)`. Simplify using `only [map_add, map_mul, map_sub, map_pow]`. Take the linear combination `(-(algebraMap K L c) ^ 2) * hpq`. Use `⟨algebraMap K L (a * a + a * c * q - c ^ 2 * p)⁻¹ * (algebraMap K L (a + c * q) - algebraMap K L c * x), ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_left_comm, hprod, ← map_mul, inv_mul_cancel₀ hN, map_one]`.
-/
theorem dichotomy (hr : finrank K L = 2) (hred : IsReduced L) :
    IsField L ∨ ∃ e : L, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  have := nontrivial_of_finrank_eq_two hr
  obtain ⟨x, hx⟩ := exists_not_mem_range_algebraMap_of_finrank_eq_two hr
  have hrep := exists_eq_add_mul_of_finrank_eq_two' hr hx
  obtain ⟨p, q, hpq0⟩ := hrep (x ^ 2)
  have hpq : x ^ 2 = algebraMap K L p + algebraMap K L q * x := hpq0.symm
  by_cases hroot : ∃ r : K, r ^ 2 = p + q * r
  · obtain ⟨r, hr2⟩ := hroot
    have hfac : (x - algebraMap K L r) * (x - algebraMap K L (q - r)) = 0 := by
      have h' : algebraMap K L (r ^ 2) = algebraMap K L (p + q * r) := by rw [hr2]
      simp only [map_add, map_mul, map_pow, map_sub] at h' ⊢
      linear_combination hpq - h'
    by_cases hrs : r = q - r
    · exfalso
      have hsq : (x - algebraMap K L r) ^ 2 = 0 := by
        have h' := hfac
        rw [← hrs] at h'
        rw [sq]
        exact h'
      have hz : x - algebraMap K L r = 0 := hred.eq_zero _ ⟨2, hsq⟩
      exact hx ⟨r, (sub_eq_zero.mp hz).symm⟩
    · right
      have hd : q - r - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
      have hsq : (x - algebraMap K L r) * (x - algebraMap K L r) =
          algebraMap K L (q - r - r) * (x - algebraMap K L r) := by
        have h' := hfac
        simp only [map_sub] at h' ⊢
        linear_combination h'
      have hu : algebraMap K L (q - r - r)⁻¹ * algebraMap K L (q - r - r) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hd, map_one]
      have hback : x - algebraMap K L r = algebraMap K L (q - r - r) *
          (algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r)) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd, map_one, one_mul]
      refine ⟨algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r), ?_, ?_, ?_⟩
      · show _ * _ = _
        linear_combination (algebraMap K L (q - r - r)⁻¹) ^ 2 * hsq +
          algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r) * hu
      · intro he
        rw [he, mul_zero, sub_eq_zero] at hback
        exact hx ⟨r, hback.symm⟩
      · intro he
        rw [he, mul_one] at hback
        apply hx
        refine ⟨q - r, ?_⟩
        simp only [map_sub] at hback ⊢
        linear_combination -hback
  · push Not at hroot
    left
    refine ⟨⟨0, 1, zero_ne_one⟩, fun a b => mul_comm a b, ?_⟩
    intro y hy
    obtain ⟨a, c, rfl⟩ := hrep y
    have hN : a * a + a * c * q - c ^ 2 * p ≠ 0 := by
      intro h0
      by_cases hc : c = 0
      · subst hc
        apply hy
        have ha : a = 0 := by simpa using h0
        simp [ha]
      · apply hroot (-a / c)
        have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
        linear_combination (c⁻¹) ^ 2 * h0 + (p * (1 + c * c⁻¹) - q * a * c⁻¹) * hci
    have hprod : (algebraMap K L a + algebraMap K L c * x) *
        (algebraMap K L (a + c * q) - algebraMap K L c * x) =
        algebraMap K L (a * a + a * c * q - c ^ 2 * p) := by
      simp only [map_add, map_mul, map_sub, map_pow]
      linear_combination (-(algebraMap K L c) ^ 2) * hpq
    refine ⟨algebraMap K L (a * a + a * c * q - c ^ 2 * p)⁻¹ *
      (algebraMap K L (a + c * q) - algebraMap K L c * x), ?_⟩
    rw [mul_left_comm, hprod, ← map_mul, inv_mul_cancel₀ hN, map_one]

end PI.LocDualGen.EpC

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowEquationDvdAllPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdOfVanishingAtPerfectValuationPointsStatement
open scoped NNReal

namespace GlobalTheory.PointsKey

def oneSubMul {R : Type} [CommRing R] (u : R) : Submonoid R where
  carrier := {x | ∃ r, x = 1 - u * r}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b - u * a * b, by ring⟩
  one_mem' := ⟨0, by simp⟩

/- English proof (translation)
Establish `hg : (1 - u * r) * (∑ i ∈ Finset.range m, (u * r) ^ i) = 1 - (u * r) ^ m`. Rewrite using `[mul_comm, geom_sum_mul_neg]`. Use `⟨a * ∑ i ∈ Finset.range m, (u * r) ^ i + r ^ m * D, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hg]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [h]; ring`.
-/
theorem dvd_of_one_sub_mul {R : Type} [CommRing R] (u r D a : R) (m : ℕ)
    (h : (1 - u * r) * D = u ^ m * a) : u ^ m ∣ D := by
  have hg : (1 - u * r) * (∑ i ∈ Finset.range m, (u * r) ^ i) = 1 - (u * r) ^ m := by
    rw [mul_comm, geom_sum_mul_neg]
  refine ⟨a * ∑ i ∈ Finset.range m, (u * r) ^ i + r ^ m * D, ?_⟩
  calc D = (1 - (u * r) ^ m) * D + (u * r) ^ m * D := by ring
    _ = (∑ i ∈ Finset.range m, (u * r) ^ i) * ((1 - u * r) * D) + (u * r) ^ m * D := by
        rw [← hg]; ring
    _ = _ := by rw [h]; ring

/- English proof (translation)
Introduce `l _ R _ u hl hu κ _ D c h heq hpts m j`. Use `set S := oneSubMul u with hS`. Set `R'` to `Localization S`. Set `φ : R →+* R'` to `algebraMap R R'`. Establish `hl' : ((l : ℕ) : R') = 0` using `by rw [← map_natCast φ, hl, map_zero]`.

Establish `hu' : φ u ∈ nonZeroDivisors R'`. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `x hx`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective S x`. Establish `hx' : φ u * IsLocalization.mk' R' a s = 0` using `by rw [mul_comm]; exact hx`.

Rewrite `hx'` using `[IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff]`. Take `⟨t, ht⟩` from `hx'`. Establish `hta : (t : R) * a = 0`. Rewrite `hu` using `[mem_nonZeroDivisors_iff_right]`. Conclude with `hu _ (by rw [← ht]; ring)`.

Conclude with `(IsLocalization.mk'_eq_zero_iff a s).2 ⟨t, hta⟩`. Establish `hunit : ∀ r', IsUnit (1 - φ u * r')`. Introduce `r'`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective S r'`. Take `⟨b, hb⟩` from `s.2`.

Establish `hmem : (s : R) - u * a ∈ S` using `⟨b + a, by rw [hb]; ring⟩`. Establish `hsp` using `IsLocalization.mk'_spec R' a s`. Establish `: (1 - φ u * IsLocalization.mk' R' a s) * φ s = φ ((s : R) - u * a)`. Rewrite using `[map_sub, map_mul, sub_mul, one_mul, mul_assoc, hsp]`. Conclude with `isUnit_of_mul_isUnit_left (this ▸ IsLocalization.map_units R' ⟨_, hmem⟩)`.

Establish `heq' : ∀ j, φ u ^ h * φ (D j) = ∑ i, φ (D i) ^ l * φ (c i j)`. Introduce `j`. Simplify `congrArg φ (heq j)` using `[map_sum, map_mul, map_pow]`. Establish `hpts' : ∀ j, ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R' →+* O), f (φ u) ≠ 0 → ¬ IsUnit (f (φ u)) → IsAdicComplete (Ideal.span {f (φ u)}) O → f (φ (D j)) = 0`. Introduce `j O _ _ _ _ _ f h1 h2 h3`.

Conclude with `hpts O (f.comp φ) h1 h2 h3 j`. Establish `hb : ∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, φ u ^ (M * n) ∣ φ u ^ c * φ (D j) ^ n` using `fun j M => GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points l R' (φ u) (φ (D j)) hl' hu' hunit (hpts' j) M`. Take `⟨y, hy⟩` from `GlobalTheory.T.frobeniusPowEquation_dvd_all_pow l R' (φ u) hl' hu' κ (fun i => φ (D i)) (fun i j => φ (c i j)) h heq' hb m j`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective S y`. Establish `h2 : φ (D j * s) = φ (u ^ m * a)`.

Rewrite using `[map_mul, hy, map_mul, map_pow, mul_assoc, IsLocalization.mk'_spec]`. Take `⟨t, ht⟩` from `(IsLocalization.eq_iff_exists S R').1 h2`. Take `⟨r, hr⟩` from `(t * s).2`. Use `dvd_of_one_sub_mul u r (D j) (t * a) m ?_` and prove the remaining obligations. Rewrite using `[← hr]`.

Simplify using `only [Submonoid.coe_mul]`. Take the linear combination `ht`.
-/
theorem key : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → ∀ j, f (D j) = 0) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  intro l _ R _ u hl hu κ _ D c h heq hpts m j
  set S := oneSubMul u with hS
  let R' := Localization S
  let φ : R →+* R' := algebraMap R R'
  have hl' : ((l : ℕ) : R') = 0 := by rw [← map_natCast φ, hl, map_zero]
  have hu' : φ u ∈ nonZeroDivisors R' := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
    have hx' : φ u * IsLocalization.mk' R' a s = 0 := by rw [mul_comm]; exact hx
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hx'
    obtain ⟨t, ht⟩ := hx'
    have hta : (t : R) * a = 0 := by
      rw [mem_nonZeroDivisors_iff_right] at hu
      exact hu _ (by rw [← ht]; ring)
    exact (IsLocalization.mk'_eq_zero_iff a s).2 ⟨t, hta⟩
  have hunit : ∀ r', IsUnit (1 - φ u * r') := by
    intro r'
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S r'
    obtain ⟨b, hb⟩ := s.2
    have hmem : (s : R) - u * a ∈ S := ⟨b + a, by rw [hb]; ring⟩
    have hsp := IsLocalization.mk'_spec R' a s
    have : (1 - φ u * IsLocalization.mk' R' a s) * φ s = φ ((s : R) - u * a) := by
      rw [map_sub, map_mul, sub_mul, one_mul, mul_assoc, hsp]
    exact isUnit_of_mul_isUnit_left (this ▸ IsLocalization.map_units R' ⟨_, hmem⟩)
  have heq' : ∀ j, φ u ^ h * φ (D j) = ∑ i, φ (D i) ^ l * φ (c i j) := by
    intro j; simpa [map_sum, map_mul, map_pow] using congrArg φ (heq j)
  have hpts' : ∀ j, ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R' →+* O), f (φ u) ≠ 0 → ¬ IsUnit (f (φ u)) → IsAdicComplete (Ideal.span {f (φ u)}) O → f (φ (D j)) = 0 := by
    intro j O _ _ _ _ _ f h1 h2 h3
    exact hpts O (f.comp φ) h1 h2 h3 j
  have hb : ∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, φ u ^ (M * n) ∣ φ u ^ c * φ (D j) ^ n := fun j M =>
    GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points l R' (φ u) (φ (D j)) hl' hu' hunit (hpts' j) M
  obtain ⟨y, hy⟩ := GlobalTheory.T.frobeniusPowEquation_dvd_all_pow l R' (φ u) hl' hu' κ (fun i => φ (D i)) (fun i j => φ (c i j)) h heq' hb m j
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S y
  have h2 : φ (D j * s) = φ (u ^ m * a) := by
    rw [map_mul, hy, map_mul, map_pow, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists S R').1 h2
  obtain ⟨r, hr⟩ := (t * s).2
  refine dvd_of_one_sub_mul u r (D j) (t * a) m ?_
  rw [← hr]
  simp only [Submonoid.coe_mul]
  linear_combination ht

end GlobalTheory.PointsKey

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.RegDivide

/- English proof (translation)
Establish `hex : ∃ n : ℕ, ¬ ξ ^ (n + 1) ∣ y`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hy` to reduce the goal to its premises. Apply `IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ξ}) R)` to reduce the goal to its premises.

Introduce `n`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `(pow_dvd_pow ξ (Nat.le_succ n)).trans (h n)`. Establish `h1 : ξ ^ (Nat.find hex) ∣ y`. Break down `h : Nat.find hex with _ | k` into its components or cases.

Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hk`. Conclude with `Nat.find_min hex (by omega : k < Nat.find hex) hk`. Take `⟨z, hz⟩` from `h1`. Use `⟨Nat.find hex, z, hz, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨w, rfl⟩`. Apply `Nat.find_spec hex` to reduce the goal to its premises. Conclude with `⟨w, by rw [pow_succ, mul_assoc]; exact hz⟩`.
-/
theorem exists_pow_mul_not_dvd {R : Type*} [CommRing R] (ξ : R) [IsHausdorff (Ideal.span {ξ}) R]
    {y : R} (hy : y ≠ 0) : ∃ (n : ℕ) (z : R), y = ξ ^ n * z ∧ ¬ ξ ∣ z := by
  classical
  have hex : ∃ n : ℕ, ¬ ξ ^ (n + 1) ∣ y := by
    by_contra h
    push Not at h
    apply hy
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ξ}) R)
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow ξ (Nat.le_succ n)).trans (h n)
  have h1 : ξ ^ (Nat.find hex) ∣ y := by
    rcases h : Nat.find hex with _ | k
    · simp
    · by_contra hk
      exact Nat.find_min hex (by omega : k < Nat.find hex) hk
  obtain ⟨z, hz⟩ := h1
  refine ⟨Nat.find hex, z, hz, ?_⟩
  rintro ⟨w, rfl⟩
  apply Nat.find_spec hex
  exact ⟨w, by rw [pow_succ, mul_assoc]; exact hz⟩

/- English proof (translation)
Take `⟨m, y₀, h0⟩` from `hD (ι b)`. Take `⟨s, hs⟩` from `ht.exists_right_inv`. Take `⟨w, hw⟩` from `hv.exists_right_inv`. Establish `h1 : ι (b * t ^ m) = a (y₀ * v ^ m)`. Rewrite using `[map_mul, map_pow, hιt, map_mul, map_mul, ← h0, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hne : y₀ * v ^ m ≠ 0`. Introduce `h`. Rewrite `h1` using `[h, map_zero, ← map_zero ι]`. Conclude with `hb ((ht.pow m).mul_left_eq_zero.1 (hι h1))`.

Take `⟨n, z, hz, hnd⟩` from `exists_pow_mul_not_dvd ξ hne`. Use `⟨m, n, b * t ^ m * s ^ n, z * w ^ n, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : a ξ * a v * ι s = 1` using `by rw [← map_mul a, ← hιt, ← map_mul, hs, map_one]`. Establish `h3 : a v * a w = 1` using `by rw [← map_mul, hw, map_one]`.

Rewrite using `[map_mul, h1, hz, map_mul, map_mul, map_pow, map_pow, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3, one_pow, mul_one]`. Use `_ = a z * a w ^ n * (a ξ * a v * ι s) ^ n := by ring`. Use `_ = _ := by rw [h2, one_pow, mul_one]`.

Introduce `h`. Apply `hnd` to reduce the goal to its premises. Establish `: z = z * w ^ n * v ^ n`. Rewrite using `[mul_assoc, ← mul_pow, mul_comm w v, hw, one_pow, mul_one]`. Rewrite using `[this]`.

Conclude with `h.mul_right _`.
-/
theorem abstract {B R D : Type*} [CommRing B] [CommRing R] [CommRing D] (ι : B →+* D) (a : R →+* D)
    (hι : Function.Injective ι) (ξ v : R) [IsHausdorff (Ideal.span {ξ}) R] (hv : IsUnit v)
    (t : B) (ht : IsUnit t) (hιt : ι t = a (ξ * v))
    (hD : ∀ x : D, ∃ (n : ℕ) (y : R), x * a ξ ^ n = a y) (b : B) (hb : b ≠ 0) :
    ∃ (m n : ℕ) (b' : B) (y : R), b * t ^ m = t ^ n * b' ∧ ι b' = a y ∧ ¬ ξ ∣ y := by
  obtain ⟨m, y₀, h0⟩ := hD (ι b)
  obtain ⟨s, hs⟩ := ht.exists_right_inv
  obtain ⟨w, hw⟩ := hv.exists_right_inv
  have h1 : ι (b * t ^ m) = a (y₀ * v ^ m) := by
    rw [map_mul, map_pow, hιt, map_mul, map_mul, ← h0, map_pow]
    ring
  have hne : y₀ * v ^ m ≠ 0 := by
    intro h
    rw [h, map_zero, ← map_zero ι] at h1
    exact hb ((ht.pow m).mul_left_eq_zero.1 (hι h1))
  obtain ⟨n, z, hz, hnd⟩ := exists_pow_mul_not_dvd ξ hne
  refine ⟨m, n, b * t ^ m * s ^ n, z * w ^ n, ?_, ?_, ?_⟩
  · calc b * t ^ m = b * t ^ m * (t * s) ^ n := by rw [hs, one_pow, mul_one]
      _ = _ := by ring
  · have h2 : a ξ * a v * ι s = 1 := by rw [← map_mul a, ← hιt, ← map_mul, hs, map_one]
    have h3 : a v * a w = 1 := by rw [← map_mul, hw, map_one]
    rw [map_mul, h1, hz, map_mul, map_mul, map_pow, map_pow, map_pow]
    calc a ξ ^ n * a z * ι s ^ n = a ξ ^ n * a z * ι s ^ n * (a v * a w) ^ n := by
          rw [h3, one_pow, mul_one]
      _ = a z * a w ^ n * (a ξ * a v * ι s) ^ n := by ring
      _ = _ := by rw [h2, one_pow, mul_one]
  · intro h
    apply hnd
    have : z = z * w ^ n * v ^ n := by
      rw [mul_assoc, ← mul_pow, mul_comm w v, hw, one_pow, mul_one]
    rw [this]
    exact h.mul_right _

/- English proof (translation)
Introduce `l _ C b hb`. Establish `he` using `core_isEps l C`. Take `⟨hF, -, hc, -⟩` from `filtration_eq_xi_pow l C.ε he`. Take `⟨ht, h1, h2, -⟩` from `core_t_unit_fil l C`. Take `⟨-, hk, hu, -⟩` from `thetaD_props l`.

Establish `hinj` using `(ULaws.u_laws l C).2.2.2.1`. Establish `hD` using `(BdRField.bdR_isField l).2.2.2 C.ε he`. Establish `hθ : ∀ y : Per.BdRp l, ¬ aDp l (xi C.ε) ∣ y → Per.θD l y ≠ 0` using `fun y hy h => hy (by simpa only [pow_one] using (hF 1 y).1 ((hk y).1 h))`. Take `⟨v, hv⟩` from `(hF 1 _).1 h1`. Rewrite `hv` using `[pow_one]`.

Establish `hvu : IsUnit v`. Apply `hu` to reduce the goal to its premises. Apply `hθ` to reduce the goal to its premises. Introduce and unpack `⟨w, hw⟩`. Apply `h2` to reduce the goal to its premises.

Use `(hF 2 _).2 ⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[hv, hw, pow_two, mul_assoc]`. Use `haveI := hc.toIsHausdorff`. Take `⟨m, n, b', y, e1, e2, e3⟩` from `abstract C.ι (algebraMap (Per.BdRp l) (Per.BdR l)) hinj (aDp l (xi C.ε)) v hvu C.tB ht (by rw [← hv]; exact C.ι_j C.t) hD b hb`. Conclude with `⟨m, n, b', y, e1, e2, hθ y e3⟩`.
-/
theorem exists_divide : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l), b ≠ 0 →
    ∃ (m n : ℕ) (b' : Per.Bcris l) (y : Per.BdRp l), b * C.tB ^ m = C.tB ^ n * b' ∧
      C.ι b' = algebraMap (Per.BdRp l) (Per.BdR l) y ∧ Per.θD l y ≠ 0 := by
  intro l _ C b hb
  have he := core_isEps l C
  obtain ⟨hF, -, hc, -⟩ := filtration_eq_xi_pow l C.ε he
  obtain ⟨ht, h1, h2, -⟩ := core_t_unit_fil l C
  obtain ⟨-, hk, hu, -⟩ := thetaD_props l
  have hinj := (ULaws.u_laws l C).2.2.2.1
  have hD := (BdRField.bdR_isField l).2.2.2 C.ε he
  have hθ : ∀ y : Per.BdRp l, ¬ aDp l (xi C.ε) ∣ y → Per.θD l y ≠ 0 := fun y hy h =>
    hy (by simpa only [pow_one] using (hF 1 y).1 ((hk y).1 h))
  obtain ⟨v, hv⟩ := (hF 1 _).1 h1
  rw [pow_one] at hv
  have hvu : IsUnit v := by
    apply hu
    apply hθ
    rintro ⟨w, hw⟩
    apply h2
    refine (hF 2 _).2 ⟨w, ?_⟩
    rw [hv, hw, pow_two, mul_assoc]
  haveI := hc.toIsHausdorff
  obtain ⟨m, n, b', y, e1, e2, e3⟩ := abstract C.ι (algebraMap (Per.BdRp l) (Per.BdR l)) hinj
    (aDp l (xi C.ε)) v hvu C.tB ht (by rw [← hv]; exact C.ι_j C.t) hD b hb
  exact ⟨m, n, b', y, e1, e2, hθ y e3⟩

end GlobalTheory.MemLoc.RegDivide

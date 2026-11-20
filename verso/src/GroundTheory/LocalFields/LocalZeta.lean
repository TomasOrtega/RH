import Mathlib
import GroundTheory.LocalFields.LocalZetaGauss

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Identity

omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Establish `hFa : AnalyticOnNhd ℂ F Set.univ` using `fun z _ => hF.analyticAt z`. Establish `hGa : AnalyticOnNhd ℂ G Set.univ` using `fun z _ => hG.analyticAt z`. Establish `hopen : IsOpen {s : ℂ | a < s.re ∧ s.re < b}` using `(isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)`. Establish `hmem : (((a + b) / 2 : ℝ) : ℂ) ∈ {s : ℂ | a < s.re ∧ s.re < b}`. Simplify using `only [Set.mem_setOf_eq, Complex.ofReal_re]`.

Apply the tactic sequence `constructor <;> linarith`. Use `hFa.eq_of_eventuallyEq hGa (z₀ := (((a + b) / 2 : ℝ) : ℂ)) ?_` and prove the remaining obligations. Use `filter_upwards [hopen.mem_nhds hmem] with s hs using h s hs.1 hs.2`.
-/
theorem eq_of_eqOn_reStrip {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {a b : ℝ} (hab : a < b) (h : ∀ s : ℂ, a < s.re → s.re < b → F s = G s) : F = G := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hGa : AnalyticOnNhd ℂ G Set.univ := fun z _ => hG.analyticAt z
  have hopen : IsOpen {s : ℂ | a < s.re ∧ s.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : (((a + b) / 2 : ℝ) : ℂ) ∈ {s : ℂ | a < s.re ∧ s.re < b} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]
    constructor <;> linarith
  refine hFa.eq_of_eventuallyEq hGa (z₀ := (((a + b) / 2 : ℝ) : ℂ)) ?_
  filter_upwards [hopen.mem_nhds hmem] with s hs using h s hs.1 hs.2

end Identity

section Helpers

/- English proof (translation)
Simplify using `[ord, Valuation.map_neg]`.
-/
theorem ord_neg_eq (x : K) : ord (-x) = ord x := by
  simp [ord, Valuation.map_neg]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Rewrite using `[modulus_of_ne_zero (neg_ne_zero.mpr hx), modulus_of_ne_zero hx, ord_neg_eq]`.
-/
theorem modulus_neg_eq (x : K) : modulus (-x) = modulus x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [modulus_of_ne_zero (neg_ne_zero.mpr hx), modulus_of_ne_zero hx, ord_neg_eq]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[quasiCharExt, hx]`. Distinguish the cases in `hy : y = 0`. Simplify using `[quasiCharExt, hy]`. Establish `: Units.mk0 (x * y) (mul_ne_zero hx hy) = Units.mk0 x hx * Units.mk0 y hy`.

Use `ext`. Simplify using the standard rewrite rules. Simplify using `only [quasiCharExt, mul_ne_zero hx hy, hx, hy, dif_neg, not_false_eq_true, this, map_mul, Units.val_mul]`.
-/
theorem quasiCharExt_mul (χ : Kˣ →* ℂˣ) (x y : K) :
    quasiCharExt χ (x * y) = quasiCharExt χ x * quasiCharExt χ y := by
  by_cases hx : x = 0
  · simp [quasiCharExt, hx]
  by_cases hy : y = 0
  · simp [quasiCharExt, hy]
  have : Units.mk0 (x * y) (mul_ne_zero hx hy) = Units.mk0 x hx * Units.mk0 y hy := by
    ext
    simp
  simp only [quasiCharExt, mul_ne_zero hx hy, hx, hy, dif_neg, not_false_eq_true, this, map_mul,
    Units.val_mul]

/- English proof (translation)
Simplify using `only [Set.mem_sdiff, SetLike.mem_coe, mem_valBall_iff_le_ord hx]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_shellSet_iff {x : K} (hx : x ≠ 0) {j : ℤ} :
    x ∈ (valBall K j : Set K) \ valBall K (j + 1) ↔ ord x = j := by
  simp only [Set.mem_sdiff, SetLike.mem_coe, mem_valBall_iff_le_ord hx]
  omega

/- English proof (translation)
Introduce `h` and use `h.2 (zero_mem _)`.
-/
theorem zero_notMem_shellSet (j : ℤ) : (0 : K) ∉ (valBall K j : Set K) \ valBall K (j + 1) :=
  fun h => h.2 (zero_mem _)

/- English proof (translation)
Rewrite using `[modulus_of_ne_zero a.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast, ← zpow_neg, neg_neg, ofReal_qzpow]`.
-/
theorem ofReal_modulus_inv_eq (a : Kˣ) :
    ((((modulus (a : K) : ℝ))⁻¹ : ℝ) : ℂ) = (residueCard K : ℂ) ^ ((ord (a : K) : ℤ) : ℂ) := by
  rw [modulus_of_ne_zero a.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast, ← zpow_neg, neg_neg,
    ofReal_qzpow]

end Helpers

variable [MeasurableSpace K] [BorelSpace K]

section Epsilon

variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}

/- English proof (translation)
Distinguish the cases in `hu : IsUnramifiedChar χ`. Use `⟨((χ (unifUnit K) : ℂˣ) : ℂ) ^ (-addCharConductor ψ) * (residueCard K : ℂ) ^ (-(addCharConductor ψ : ℂ) / 2), -addCharConductor ψ, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[localEpsilon_of_isUnramified hu, qcpow_zpow, mul_assoc, qcpow_mul_qcpow]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨(((residueCard K : ℝ) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ) : ℂ) * ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \ valBall K (addCharConductor ψ - quasiCharConductor χ + 1), quasiCharExt χ⁻¹ x * (ψ x : ℂ) ∂haarIntegers K, -(addCharConductor ψ - quasiChar …` and prove the remaining obligations. Rewrite using `[localEpsilon_of_not_isUnramified_eq hu, qcpow_zpow]`. Rewrite using `[show ((-(addCharConductor ψ - (quasiCharConductor χ : ℤ)) : ℤ) : ℂ) * -s = (((addCharConductor ψ - quasiCharConductor χ : ℤ)) : ℂ) * s by push_cast; ring]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_localEpsilon_eq_mul_zpow :
    ∃ a : ℂ, ∃ k : ℤ, ∀ s : ℂ, localEpsilon χ ψ s = a * ((residueCard K : ℂ) ^ (-s)) ^ k := by
  by_cases hu : IsUnramifiedChar χ
  · refine ⟨((χ (unifUnit K) : ℂˣ) : ℂ) ^ (-addCharConductor ψ) *
      (residueCard K : ℂ) ^ (-(addCharConductor ψ : ℂ) / 2), -addCharConductor ψ, fun s => ?_⟩
    rw [localEpsilon_of_isUnramified hu, qcpow_zpow, mul_assoc, qcpow_mul_qcpow]
    congr 2
    push_cast
    ring
  · refine ⟨(((residueCard K : ℝ) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ) : ℂ) *
      ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \
          valBall K (addCharConductor ψ - quasiCharConductor χ + 1),
        quasiCharExt χ⁻¹ x * (ψ x : ℂ) ∂haarIntegers K,
      -(addCharConductor ψ - quasiCharConductor χ), fun s => ?_⟩
    rw [localEpsilon_of_not_isUnramified_eq hu, qcpow_zpow]
    rw [show ((-(addCharConductor ψ - (quasiCharConductor χ : ℤ)) : ℤ) : ℂ) * -s =
      (((addCharConductor ψ - quasiCharConductor χ : ℤ)) : ℂ) * s by push_cast; ring]
    ring

/- English proof (translation)
Take `⟨a, k, h⟩` from `exists_localEpsilon_eq_mul_zpow (χ := χ) (ψ := ψ)`. Rewrite using `[show localEpsilon χ ψ = fun s => a * ((residueCard K : ℂ) ^ (-s)) ^ k from funext h]`. Conclude with `(differentiable_qpow.zpow (Or.inl fun s => qpow_ne_zero s)).const_mul a`.
-/
theorem differentiable_localEpsilon : Differentiable ℂ (localEpsilon χ ψ) := by
  obtain ⟨a, k, h⟩ := exists_localEpsilon_eq_mul_zpow (χ := χ) (ψ := ψ)
  rw [show localEpsilon χ ψ = fun s => a * ((residueCard K : ℂ) ^ (-s)) ^ k from funext h]
  exact (differentiable_qpow.zpow (Or.inl fun s => qpow_ne_zero s)).const_mul a

/- English proof (translation)
Establish `hn` using `addCharConductor_mulShift hψ hψ1 a.ne_zero`. Use `set k := ord (a : K)`. Use `set n := addCharConductor ψ`. Distinguish the cases in `hu : IsUnramifiedChar χ`. Use `set α := ((χ (unifUnit K) : ℂˣ) : ℂ)`.

Establish `hα : α ≠ 0` using `(χ _).ne_zero`. Establish `hχa : ((χ a : ℂˣ) : ℂ) = α ^ k`. Rewrite using `[quasiChar_apply_of_isUnramified hu a, Units.val_zpow_eq_zpow_val]`. Rewrite using `[localEpsilon_of_isUnramified hu, localEpsilon_of_isUnramified hu, hn, hχa, modulus_cpow_eq_qcpow a.ne_zero, show -(n - k) = k + -n by ring, zpow_add₀ hα]`. Establish `e : (residueCard K : ℂ) ^ (((n - k : ℤ) : ℂ) * (s - 1 / 2)) = (residueCard K : ℂ) ^ (-(k : ℂ) * (s - 1 / 2)) * (residueCard K : ℂ) ^ ((n : ℂ) * (s - 1 / 2))`.

Rewrite using `[qcpow_mul_qcpow]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Use `set c := quasiCharConductor χ set A := ∫ x in (valBall K (n - c) : Set K) \ valBall K (n - c + 1), quasiCharExt χ⁻¹ x * (ψ x : ℂ) ∂haarIntegers K`. Establish `hA : ∫ x in (valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1), quasiCharExt χ⁻¹ x * ((ψ.mulShift (a : K)) x : ℂ) ∂haarIntegers K = ((((modulus (a : K) : ℝ))⁻¹ : ℝ) : ℂ) * (((χ a : ℂˣ) : ℂ) * A)`. Establish `hS` using `(measurableSet_valBall (K := K) (n - k - c)).diff (measurableSet_valBall (n - k - c + 1))`. Establish `hS'` using `(measurableSet_valBall (K := K) (n - c)).diff (measurableSet_valBall (n - c + 1))`.

Set `H : K → ℂ` to `((valBall K (n - c) : Set K) \ valBall K (n - c + 1)).indicator fun y => ((χ a : ℂˣ) : ℂ) * (quasiCharExt χ⁻¹ y * (ψ y : ℂ))`. Establish `hχa : quasiCharExt χ⁻¹ (a : K) * ((χ a : ℂˣ) : ℂ) = 1`. Rewrite using `[quasiCharExt_units, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (χ a).ne_zero]`. Establish `hpt : ∀ x : K, ((valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1)).indicator (fun x => quasiCharExt χ⁻¹ x * ((ψ.mulShift (a : K)) x : ℂ)) x = H ((a : K) * x)`. Introduce `x`.

Simplify using `only [H]`. Distinguish the cases in `hx : x = 0`. Rewrite using `[hx, mul_zero, Set.indicator_of_notMem (zero_notMem_shellSet _), Set.indicator_of_notMem (zero_notMem_shellSet _)]`. Establish `hax : (a : K) * x ≠ 0` using `mul_ne_zero a.ne_zero hx`. Establish `hiff : x ∈ (valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1) ↔ (a : K) * x ∈ (valBall K (n - c) : Set K) \ valBall K (n - c + 1)`.

Rewrite using `[mem_shellSet_iff hx, mem_shellSet_iff hax, ord_mul a.ne_zero hx]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hm : x ∈ (valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1)`. Rewrite using `[Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.mp hm), quasiCharExt_mul, AddChar.mulShift_apply]`. Take the linear combination `(quasiCharExt χ⁻¹ x * (ψ ((a : K) * x) : ℂ)) * hχa.symm`.

Rewrite using `[Set.indicator_of_notMem hm, Set.indicator_of_notMem (mt hiff.mpr hm)]`. Rewrite using `[← integral_indicator hS, show (fun x => ((valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1)).indicator (fun x => quasiCharExt χ⁻¹ x * ((ψ.mulShift (a : K)) x : ℂ)) x) = fun x => H ((a : K) * x) from funext hpt, integral_comp_mul_left (haarIntegers K) a.ne_zero H, Comple …`. Rewrite using `[localEpsilon_of_not_isUnramified_eq hu, localEpsilon_of_not_isUnramified_eq hu, hn, hA, ofReal_modulus_inv_eq, modulus_cpow_eq_qcpow a.ne_zero, ofReal_qrpow, ofReal_qrpow]`. Establish `e : (residueCard K : ℂ) ^ (((n - k - c : ℤ) : ℂ) * s) * (residueCard K : ℂ) ^ ((((n - k : ℤ) : ℝ) / 2 : ℝ) : ℂ) * (residueCard K : ℂ) ^ ((k : ℤ) : ℂ) = (residueCard K : ℂ) ^ (-(k : ℂ) * (s - 1 / 2)) * ((residueCard K : ℂ) ^ (((n - c : ℤ) : ℂ) * s) * (residueCard K : ℂ) ^ ((((n : …`. Simplify using `only [qcpow_mul_qcpow]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(((χ a : ℂˣ) : ℂ) * A) * e`.
-/
theorem localEpsilon_mulShift (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (a : Kˣ) (s : ℂ) :
    localEpsilon χ (ψ.mulShift (a : K)) s =
      ((χ a : ℂˣ) : ℂ) * ((modulus (a : K) : ℝ) : ℂ) ^ (s - 1 / 2) * localEpsilon χ ψ s := by
  have hn := addCharConductor_mulShift hψ hψ1 a.ne_zero
  set k := ord (a : K)
  set n := addCharConductor ψ
  by_cases hu : IsUnramifiedChar χ
  · set α := ((χ (unifUnit K) : ℂˣ) : ℂ)
    have hα : α ≠ 0 := (χ _).ne_zero
    have hχa : ((χ a : ℂˣ) : ℂ) = α ^ k := by
      rw [quasiChar_apply_of_isUnramified hu a, Units.val_zpow_eq_zpow_val]
    rw [localEpsilon_of_isUnramified hu, localEpsilon_of_isUnramified hu, hn, hχa,
      modulus_cpow_eq_qcpow a.ne_zero,
      show -(n - k) = k + -n by ring, zpow_add₀ hα]
    have e : (residueCard K : ℂ) ^ (((n - k : ℤ) : ℂ) * (s - 1 / 2)) =
        (residueCard K : ℂ) ^ (-(k : ℂ) * (s - 1 / 2)) *
          (residueCard K : ℂ) ^ ((n : ℂ) * (s - 1 / 2)) := by
      rw [qcpow_mul_qcpow]
      congr 1
      push_cast
      ring
    rw [e]
    ring
  · set c := quasiCharConductor χ
    set A := ∫ x in (valBall K (n - c) : Set K) \ valBall K (n - c + 1),
      quasiCharExt χ⁻¹ x * (ψ x : ℂ) ∂haarIntegers K

    have hA : ∫ x in (valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1),
        quasiCharExt χ⁻¹ x * ((ψ.mulShift (a : K)) x : ℂ) ∂haarIntegers K =
        ((((modulus (a : K) : ℝ))⁻¹ : ℝ) : ℂ) * (((χ a : ℂˣ) : ℂ) * A) := by
      have hS := (measurableSet_valBall (K := K) (n - k - c)).diff
        (measurableSet_valBall (n - k - c + 1))
      have hS' := (measurableSet_valBall (K := K) (n - c)).diff (measurableSet_valBall (n - c + 1))
      let H : K → ℂ := ((valBall K (n - c) : Set K) \ valBall K (n - c + 1)).indicator
        fun y => ((χ a : ℂˣ) : ℂ) * (quasiCharExt χ⁻¹ y * (ψ y : ℂ))
      have hχa : quasiCharExt χ⁻¹ (a : K) * ((χ a : ℂˣ) : ℂ) = 1 := by
        rw [quasiCharExt_units, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
          inv_mul_cancel₀ (χ a).ne_zero]
      have hpt : ∀ x : K, ((valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1)).indicator
          (fun x => quasiCharExt χ⁻¹ x * ((ψ.mulShift (a : K)) x : ℂ)) x = H ((a : K) * x) := by
        intro x
        simp only [H]
        by_cases hx : x = 0
        · rw [hx, mul_zero, Set.indicator_of_notMem (zero_notMem_shellSet _),
            Set.indicator_of_notMem (zero_notMem_shellSet _)]
        have hax : (a : K) * x ≠ 0 := mul_ne_zero a.ne_zero hx
        have hiff : x ∈ (valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1) ↔
            (a : K) * x ∈ (valBall K (n - c) : Set K) \ valBall K (n - c + 1) := by
          rw [mem_shellSet_iff hx, mem_shellSet_iff hax, ord_mul a.ne_zero hx]
          omega
        by_cases hm : x ∈ (valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1)
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.mp hm), quasiCharExt_mul,
            AddChar.mulShift_apply]
          linear_combination (quasiCharExt χ⁻¹ x * (ψ ((a : K) * x) : ℂ)) * hχa.symm
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (mt hiff.mpr hm)]
      rw [← integral_indicator hS, show (fun x => ((valBall K (n - k - c) : Set K) \
          valBall K (n - k - c + 1)).indicator
          (fun x => quasiCharExt χ⁻¹ x * ((ψ.mulShift (a : K)) x : ℂ)) x) =
          fun x => H ((a : K) * x) from funext hpt,
        integral_comp_mul_left (haarIntegers K) a.ne_zero H, Complex.real_smul,
        integral_indicator hS', integral_const_mul]
    rw [localEpsilon_of_not_isUnramified_eq hu, localEpsilon_of_not_isUnramified_eq hu, hn, hA,
      ofReal_modulus_inv_eq, modulus_cpow_eq_qcpow a.ne_zero, ofReal_qrpow, ofReal_qrpow]
    have e : (residueCard K : ℂ) ^ (((n - k - c : ℤ) : ℂ) * s) *
        (residueCard K : ℂ) ^ ((((n - k : ℤ) : ℝ) / 2 : ℝ) : ℂ) *
          (residueCard K : ℂ) ^ ((k : ℤ) : ℂ) =
        (residueCard K : ℂ) ^ (-(k : ℂ) * (s - 1 / 2)) *
          ((residueCard K : ℂ) ^ (((n - c : ℤ) : ℂ) * s) *
            (residueCard K : ℂ) ^ ((((n : ℤ) : ℝ) / 2 : ℝ) : ℂ)) := by
      simp only [qcpow_mul_qcpow]
      congr 1
      push_cast
      ring
    linear_combination (((χ a : ℂˣ) : ℂ) * A) * e

/- English proof (translation)
Unfold `localZeta`. Rewrite using `[← integral_const_mul]`. Use `conv_lhs => rw [← integral_mul_left_eq_self _ (-1 : Kˣ)]`. Use `congr 1`. Use function extensionality and compare the values at `u`.

Rewrite using `[map_mul, Units.val_mul (χ (-1)) (χ u)]`. Simplify using `only [Units.val_neg, neg_one_mul, neg_neg, modulus_neg_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem localZeta_comp_neg (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) :
    localZeta (fun x => f (-x)) χ s = ((χ (-1 : Kˣ) : ℂˣ) : ℂ) * localZeta f χ s := by
  unfold localZeta
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_mul_left_eq_self _ (-1 : Kˣ)]
  congr 1
  funext u
  rw [map_mul, Units.val_mul (χ (-1)) (χ u)]
  simp only [Units.val_neg, neg_one_mul, neg_neg, modulus_neg_eq]
  ring

end Epsilon

section Uniqueness

variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}

end Uniqueness

section FunctionalEquation

variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ

/- English proof (translation)
Take `⟨g, hg, hZg, -⟩` from `exists_localZeta_test hψ hψ1 hχ hs1 hs2`. Establish `hL1` using `localLFactor_ne_zero hχ hs1`. Establish `hχ'` using `continuous_quasiChar_inv hχ`. Establish `hs1' : -quasiCharExponent χ⁻¹ < (1 - s).re`. Rewrite using `[quasiCharExponent_inv, Complex.sub_re, Complex.one_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs2' : (1 - s).re < 1 - quasiCharExponent χ⁻¹`. Rewrite using `[quasiCharExponent_inv, Complex.sub_re, Complex.one_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hĝ` using `localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hψ hψ1 hg`.

Establish `h1` using `localZeta_functionalEquation hψ hψ1 hχ hg hs1 hs2`. Establish `h2` using `localZeta_functionalEquation hψ hψ1 hχ' hĝ hs1' hs2'`. Establish `hχχ : (χ⁻¹)⁻¹ = χ`. Use extensionality with `u`. Simplify using the standard rewrite rules.

Rewrite `h2` using `[hχχ, sub_sub_cancel]`. Establish `hinv : localFourier (selfDualMeasure ψ) ψ (localFourier (selfDualMeasure ψ) ψ g) = fun x => g (-x)` using `funext fun x => localFourier_localFourier_selfDual hψ hψ1 hg x`. Rewrite `h2` using `[hinv, localZeta_comp_neg, h1]`. Establish `hne : localZeta g χ s / localLFactor χ s ≠ 0` using `div_ne_zero hZg hL1`. Establish `: ((χ (-1 : Kˣ) : ℂˣ) : ℂ) * (localZeta g χ s / localLFactor χ s) = (localEpsilon χ⁻¹ ψ (1 - s) * localEpsilon χ ψ s) * (localZeta g χ s / localLFactor χ s)`.

Rewrite `h2` using `[mul_div_assoc]`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Use `mul_right_cancel₀ hne this` as an intermediate fact. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem localEpsilon_mul_localEpsilon_inv_eq_of_strip {s : ℂ} (hs1 : -quasiCharExponent χ < s.re)
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localEpsilon χ ψ s * localEpsilon χ⁻¹ ψ (1 - s) = ((χ (-1 : Kˣ) : ℂˣ) : ℂ) := by
  obtain ⟨g, hg, hZg, -⟩ := exists_localZeta_test hψ hψ1 hχ hs1 hs2
  have hL1 := localLFactor_ne_zero hχ hs1
  have hχ' := continuous_quasiChar_inv hχ
  have hs1' : -quasiCharExponent χ⁻¹ < (1 - s).re := by
    rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]
    linarith
  have hs2' : (1 - s).re < 1 - quasiCharExponent χ⁻¹ := by
    rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]
    linarith
  have hĝ := localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hψ hψ1 hg
  have h1 := localZeta_functionalEquation hψ hψ1 hχ hg hs1 hs2
  have h2 := localZeta_functionalEquation hψ hψ1 hχ' hĝ hs1' hs2'
  have hχχ : (χ⁻¹)⁻¹ = χ := by
    ext u
    simp
  rw [hχχ, sub_sub_cancel] at h2
  have hinv : localFourier (selfDualMeasure ψ) ψ (localFourier (selfDualMeasure ψ) ψ g) =
      fun x => g (-x) := funext fun x => localFourier_localFourier_selfDual hψ hψ1 hg x
  rw [hinv, localZeta_comp_neg, h1] at h2
  have hne : localZeta g χ s / localLFactor χ s ≠ 0 := div_ne_zero hZg hL1
  have : ((χ (-1 : Kˣ) : ℂˣ) : ℂ) * (localZeta g χ s / localLFactor χ s) =
      (localEpsilon χ⁻¹ ψ (1 - s) * localEpsilon χ ψ s) * (localZeta g χ s / localLFactor χ s) := by
    rw [mul_div_assoc] at h2
    rw [h2]
    ring
  have := mul_right_cancel₀ hne this
  rw [this]
  ring

/- English proof (translation)
Establish `hF : Differentiable ℂ fun s => localEpsilon χ ψ s * localEpsilon χ⁻¹ (ψ.mulShift (-1)) (1 - s)` using `differentiable_localEpsilon.mul (differentiable_localEpsilon.comp (differentiable_const 1 |>.sub differentiable_id))`. Establish `key` using `eq_of_eqOn_reStrip hF (differentiable_const (1 : ℂ)) (a := -quasiCharExponent χ) (b := 1 - quasiCharExponent χ) (by linarith) fun s hs1 hs2 => by`. Establish `hm` using `localEpsilon_mulShift (χ := χ⁻¹) hψ hψ1 (-1 : Kˣ) (1 - s)`. Rewrite `hm` using `[Units.val_neg, Units.val_one]`. Rewrite using `[hm, modulus_neg_eq, modulus_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]`.

Use `localEpsilon_mul_localEpsilon_inv_eq_of_strip hψ hψ1 hχ hs1 hs2` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = 1 := by rw [this, inv_mul_cancel₀ (χ _).ne_zero]`. Conclude with `congrFun key s`.
-/
theorem localEpsilon_mul_localEpsilon_inv (s : ℂ) :
    localEpsilon χ ψ s * localEpsilon χ⁻¹ (ψ.mulShift (-1)) (1 - s) = 1 := by
  have hF : Differentiable ℂ fun s => localEpsilon χ ψ s *
      localEpsilon χ⁻¹ (ψ.mulShift (-1)) (1 - s) :=
    differentiable_localEpsilon.mul
      (differentiable_localEpsilon.comp (differentiable_const 1 |>.sub differentiable_id))
  have key := eq_of_eqOn_reStrip hF (differentiable_const (1 : ℂ))
    (a := -quasiCharExponent χ) (b := 1 - quasiCharExponent χ) (by linarith) fun s hs1 hs2 => by
      have hm := localEpsilon_mulShift (χ := χ⁻¹) hψ hψ1 (-1 : Kˣ) (1 - s)
      rw [Units.val_neg, Units.val_one] at hm
      rw [hm, modulus_neg_eq, modulus_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow,
        mul_one, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      have := localEpsilon_mul_localEpsilon_inv_eq_of_strip hψ hψ1 hχ hs1 hs2
      calc localEpsilon χ ψ s * (((χ (-1 : Kˣ) : ℂˣ) : ℂ)⁻¹ * localEpsilon χ⁻¹ ψ (1 - s))
          = ((χ (-1 : Kˣ) : ℂˣ) : ℂ)⁻¹ * (localEpsilon χ ψ s * localEpsilon χ⁻¹ ψ (1 - s)) := by
            ring
        _ = 1 := by rw [this, inv_mul_cancel₀ (χ _).ne_zero]
  exact congrFun key s

/- English proof (translation)
Take `⟨a, k, h⟩` from `exists_localEpsilon_eq_mul_zpow (χ := χ) (ψ := ψ)`. Use `⟨a, fun ha => ?_, k, h⟩` and prove the remaining obligations. Use `localEpsilon_mul_localEpsilon_inv hψ hψ1 hχ 0` as an intermediate fact. Rewrite `this` using `[h, ha, zero_mul, zero_mul]`. Conclude with `zero_ne_one this`.
-/
theorem exists_localEpsilon_eq_monomial :
    ∃ a : ℂ, a ≠ 0 ∧ ∃ k : ℤ, ∀ s : ℂ,
      localEpsilon χ ψ s = a * ((residueCard K : ℂ) ^ (-s)) ^ k := by
  obtain ⟨a, k, h⟩ := exists_localEpsilon_eq_mul_zpow (χ := χ) (ψ := ψ)
  refine ⟨a, fun ha => ?_, k, h⟩
  have := localEpsilon_mul_localEpsilon_inv hψ hψ1 hχ 0
  rw [h, ha, zero_mul, zero_mul] at this
  exact zero_ne_one this

end FunctionalEquation

end GroundTheory.LocalField

import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.PhiInfIso

noncomputable def gauss2 : SchwartzMap ℂ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℂ (Real.sqrt 2)
      (Real.sqrt_ne_zero'.mpr (by norm_num))).toContinuousLinearEquiv
    (gaussianSchwartz ℂ)

/- English proof (translation)
Establish `h2 : Real.sqrt 2 ^ 2 = 2` using `Real.sq_sqrt (by norm_num)`. Establish `hn : ‖(Real.sqrt 2 : ℝ) • z‖ ^ 2 = 2 * Complex.normSq z`. Rewrite using `[norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, h2, Complex.normSq_eq_norm_sq]`. Simplify using `only [gauss2, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply, gaussianSchwartz_apply]`. Rewrite using `[hn, Complex.ofReal_exp]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss2_apply (z : ℂ) :
    gauss2 z = Complex.exp (-2 * Real.pi * ((Complex.normSq z : ℝ) : ℂ)) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : ‖(Real.sqrt 2 : ℝ) • z‖ ^ 2 = 2 * Complex.normSq z := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, h2, Complex.normSq_eq_norm_sq]
  simp only [gauss2, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
    gaussianSchwartz_apply]
  rw [hn, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/- English proof (translation)
The claim follows from `(Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth).pow m`.
-/
theorem hasTemperateGrowth_conj_pow (m : ℕ) :
    Function.HasTemperateGrowth (fun z : ℂ => conj z ^ m) :=
  (Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth).pow m

/- English proof (translation)
The claim follows from `((ContinuousLinearMap.id ℝ ℂ).hasTemperateGrowth).pow m`.
-/
theorem hasTemperateGrowth_pow (m : ℕ) :
    Function.HasTemperateGrowth (fun z : ℂ => z ^ m) :=
  ((ContinuousLinearMap.id ℝ ℂ).hasTemperateGrowth).pow m

/- English proof (translation)
Distinguish the cases in `hn : 0 ≤ n`. Use `⟨SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => conj z ^ n.natAbs) gauss2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_conj_pow _), gauss2_apply, smul_eq_mul, PhiInf, if_pos hn]`. Use `⟨SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => z ^ n.natAbs) gauss2, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `z`. Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_pow _), gauss2_apply, smul_eq_mul, PhiInf, if_neg hn]`.
-/
theorem phiInf_mem (n : ℤ) : PhiInf n ∈ SchC := by
  by_cases hn : 0 ≤ n
  · refine ⟨SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => conj z ^ n.natAbs) gauss2, ?_⟩
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_conj_pow _), gauss2_apply,
      smul_eq_mul, PhiInf, if_pos hn]
  · refine ⟨SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => z ^ n.natAbs) gauss2, ?_⟩
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_pow _), gauss2_apply,
      smul_eq_mul, PhiInf, if_neg hn]

/- English proof (translation)
Establish `hN : Complex.normSq (z * u) = Complex.normSq z`. Rewrite using `[map_mul, Complex.normSq_eq_norm_sq u, hu]`. Simplify using the standard rewrite rules. Establish `hc : conj u = u⁻¹`. Apply `eq_inv_of_mul_eq_one_right` to reduce the goal to its premises.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]`. Simplify using the standard rewrite rules. Distinguish the cases in `hn : 0 ≤ n`. Use `lift n to ℕ using hn`. Simplify using `only [PhiInf, if_pos (Int.natCast_nonneg n), Int.natAbs_natCast, hN, map_mul, mul_pow, hc, inv_pow, _root_.zpow_neg, zpow_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hneg : 0 ≤ -n` using `by omega`. Take `⟨m, hm⟩` from `Int.eq_ofNat_of_zero_le hneg`. Establish `hab : n.natAbs = m` using `by omega`. Simplify using `only [PhiInf, if_neg hn, hab, hN, mul_pow, hm, zpow_natCast]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem phiInf_circle (n : ℤ) (z u : ℂ) (hu : ‖u‖ = 1) :
    PhiInf n (z * u) = u ^ (-n) * PhiInf n z := by
  have hN : Complex.normSq (z * u) = Complex.normSq z := by
    rw [map_mul, Complex.normSq_eq_norm_sq u, hu]
    simp
  have hc : conj u = u⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    simp only [PhiInf, if_pos (Int.natCast_nonneg n), Int.natAbs_natCast, hN, map_mul, mul_pow,
      hc, inv_pow, _root_.zpow_neg, zpow_natCast]
    ring
  · have hneg : 0 ≤ -n := by omega
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hneg
    have hab : n.natAbs = m := by omega
    simp only [PhiInf, if_neg hn, hab, hN, mul_pow, hm, zpow_natCast]
    ring

/- English proof (translation)
Introduce `n` and use `⟨phiInf_mem n, fun z u hu => phiInf_circle n z u hu⟩`.
-/
theorem phiIso : PHIISO := fun n => ⟨phiInf_mem n, fun z u hu => phiInf_circle n z u hu⟩

end GlobalTheory.CompanionTheory.PhiInfIso

import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.TateThesis.FiniteAdeleScaling
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import GroundTheory.GlobalFields.LocalFieldAtPlace

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def uniformizerAt (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletionIntegers K :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem irreducible_uniformizerAt (v : HeightOneSpectrum (𝓞 K)) :
    Irreducible (uniformizerAt v) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem uniformizerAt_ne_zero (v : HeightOneSpectrum (𝓞 K)) :
    (uniformizerAt v : v.adicCompletion K) ≠ 0 := fun h ↦
  (irreducible_uniformizerAt v).ne_zero (Subtype.ext h)

def uniformizerUnit (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
  Units.mk0 _ (uniformizerAt_ne_zero v)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem valued_uniformizerUnit_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    Valued.v (((uniformizerUnit v ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
      exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, uniformizerUnit, Units.val_mk0,
    valued_of_irreducible v (irreducible_uniformizerAt v), ← exp_zsmul, smul_neg, zsmul_one,
    Int.cast_id]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem norm_uniformizerUnit_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    ‖((uniformizerUnit v ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-n) := by
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, uniformizerUnit, Units.val_mk0, ← normalizedAbv_apply,
    normalizedAbv_of_irreducible v (irreducible_uniformizerAt v), inv_zpow', zpow_neg]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Chain the equalities or inequalities of the calculation. Fix the arbitrary inputs or assume the hypotheses. Chain the equalities or inequalities of the calculation.
-/
theorem inv_mul_le_one_iff_withZero {b c : ℤᵐ⁰} (hc : c ≠ 0) : c⁻¹ * b ≤ 1 ↔ b ≤ c := by
  constructor
  · intro h
    calc b = c * (c⁻¹ * b) := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      _ ≤ c * 1 := by gcongr
      _ = c := mul_one c
  · intro h
    calc c⁻¹ * b ≤ c⁻¹ * c := by gcongr
      _ = 1 := inv_mul_cancel₀ hc

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem inv_uniformizerUnit_zpow_mul_mem_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℤ)
    (y : v.adicCompletion K) :
    ((uniformizerUnit v ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ * y ∈
        v.adicCompletionIntegers K ↔ Valued.v y ≤ exp (-n) := by
  rw [mem_adicCompletionIntegers, map_mul, map_inv₀, valued_uniformizerUnit_zpow]
  exact inv_mul_le_one_iff_withZero exp_ne_zero

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem mem_units_smul_integralFiniteAdeles_iff (u : (𝔸ᶠ[K])ˣ) (y : 𝔸ᶠ[K]) :
    y ∈ u • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), ((u : 𝔸ᶠ[K]) v)⁻¹ * y v ∈ v.adicCompletionIntegers K := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, SetLike.mem_coe,
    mem_integralFiniteAdeles]
  refine forall_congr' fun v ↦ ?_
  rw [← eq_inv_of_mul_eq_one_right (units_mul_inv_apply u v)]
  rfl

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

def idealFiniteAdeles : AddSubgroup 𝔸ᶠ[K] where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 K),
    Valued.v (x v) ≤ exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K))}
  zero_mem' v := by
    change Valued.v (0 : v.adicCompletion K) ≤ _
    rw [map_zero]
    exact zero_le
  add_mem' {a b} ha hb v :=
    (Valuation.map_add _ (a v) (b v)).trans (max_le (ha v) (hb v))
  neg_mem' {a} ha v := by
    change Valued.v (-(a v)) ≤ _
    rw [Valuation.map_neg]
    exact ha v

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_idealFiniteAdeles {x : 𝔸ᶠ[K]} :
    x ∈ idealFiniteAdeles I ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (x v) ≤ exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) :=
  Iff.rfl

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem idealFiniteAdeles_one :
    (idealFiniteAdeles (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set 𝔸ᶠ[K]) =
      integralFiniteAdeles (𝓞 K) K := by
  ext x
  simp only [SetLike.mem_coe, mem_idealFiniteAdeles, Units.val_one, FractionalIdeal.count_one,
    neg_zero, exp_zero, mem_integralFiniteAdeles, mem_adicCompletionIntegers]

def idealSupport : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Filter.eventually_cofinite.1
    (FractionalIdeal.finite_factors (I : FractionalIdeal (𝓞 K)⁰ K))).toFinset

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem count_eq_zero_of_not_mem_idealSupport {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ idealSupport I) : FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  simpa [idealSupport] using hv

def idealIdele : (𝔸ᶠ[K])ˣ :=
  ∏ v ∈ idealSupport I, finiteSingleUnits v
    (uniformizerUnit v ^ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem idealIdele_apply (x : HeightOneSpectrum (𝓞 K)) :
    ((idealIdele I : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) x =
      ((uniformizerUnit x ^ FractionalIdeal.count K x (I : FractionalIdeal (𝓞 K)⁰ K) :
        (x.adicCompletion K)ˣ) : x.adicCompletion K) := by
  classical
  rw [idealIdele, coe_prod_finiteSingleUnits_apply]
  split_ifs with hx
  · rfl
  · rw [count_eq_zero_of_not_mem_idealSupport I hx, zpow_zero, Units.val_one]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem idealFiniteAdeles_eq_smul :
    (idealFiniteAdeles I : Set 𝔸ᶠ[K]) =
      idealIdele I • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) := by
  ext y
  rw [mem_units_smul_integralFiniteAdeles_iff, SetLike.mem_coe, mem_idealFiniteAdeles]
  refine forall_congr' fun v ↦ ?_
  rw [idealIdele_apply, inv_uniformizerUnit_zpow_mul_mem_iff]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem absNorm_eq_finprod :
    ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (Ideal.absNorm v.asIdeal : ℝ) ^ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)).Finite := by
    refine (Filter.eventually_cofinite.1
      (FractionalIdeal.finite_factors (I : FractionalIdeal (𝓞 K)⁰ K))).subset fun v hv h ↦ hv ?_
    simp [h]
  have h := ((Rat.castHom ℝ : ℚ →* ℝ).comp
    (FractionalIdeal.absNorm : FractionalIdeal (𝓞 K)⁰ K →*₀ ℚ).toMonoidHom).map_finprod hfin
  rw [FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) I.ne_zero] at h
  refine h.trans (finprod_congr fun v ↦ ?_)
  simp [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem coe_finprod_nnnorm_idealIdele :
    ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((idealIdele I : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ) =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)⁻¹ := by
  rw [coe_finprod_nnnorm, absNorm_eq_finprod, ← finprod_inv_distrib]
  refine finprod_congr fun v ↦ ?_
  rw [idealIdele_apply, norm_uniformizerUnit_zpow, zpow_neg]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finiteAdeleMeasure_idealFiniteAdeles :
    finiteAdeleMeasure K (idealFiniteAdeles I) =
      ENNReal.ofReal ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ))⁻¹ *
        ((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) := by
  rw [idealFiniteAdeles_eq_smul, finiteAdeleMeasure_smul, finiteAdeleMeasure_integralFiniteAdeles,
    ← ENNReal.ofReal_coe_nnreal, coe_finprod_nnnorm_idealIdele]

end

end GroundTheory.Global

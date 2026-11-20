import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.L2PairingPolar

/- English proof (translation)
Rewrite using `[MeasureTheory.L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy`. Rewrite using `[hx, hy]`. Simplify using `[mul_comm]`.
-/
theorem integral_mul_conj_eq_inner {X : Type} [MeasurableSpace X] {μ : Measure X} {u v : X → ℂ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ∫ x, u x * starRingEnd ℂ (v x) ∂μ = inner ℂ hv.toLp hu.toLp := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp [mul_comm]

/- English proof (translation)
Establish `h2 : (2 : ENNReal) ≠ 0` using `by norm_num`. Rewrite using `[eLpNorm_eq_lintegral_rpow_enorm h2 ENNReal.ofNat_ne_top, eLpNorm_eq_lintegral_rpow_enorm h2 ENNReal.ofNat_ne_top]`. Simplify using `only [ENNReal.toReal_ofNat, ENNReal.rpow_two]`. Rewrite using `[h]`.
-/
theorem eLpNorm_two_eq {X : Type} [MeasurableSpace X] {μ : Measure X} {u v : X → ℂ}
    (h : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ) : eLpNorm u 2 μ = eLpNorm v 2 μ := by
  have h2 : (2 : ENNReal) ≠ 0 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm h2 ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm h2 ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [h]

/- English proof (translation)
Introduce `F _ _ κ _ T hpres hiso`. Use `letI : MeasurableSpace (κ → AF F) := borel _`. Introduce `μ hμ f hf g hg`. Establish `hmem : ∀ φ ∈ schA F κ, MemLp φ 2 μ` using `fun φ hφ => GlobalTheory.WeilM.schA_memLp_two F κ μ hμ φ hφ`. Establish `hf2` using `hmem f hf`.

Establish `hg2` using `hmem g hg`. Establish `hTf2` using `hmem (T f) (hpres f hf)`. Establish `hTg2` using `hmem (T g) (hpres g hg)`. Rewrite using `[integral_mul_conj_eq_inner hTf2 hTg2, integral_mul_conj_eq_inner hf2 hg2]`. Establish `hN : ∀ c : ℂ, ‖hTg2.toLp + c • hTf2.toLp‖ = ‖hg2.toLp + c • hf2.toLp‖`.

Introduce `c`. Establish `hw : g + c • f ∈ schA F κ` using `(schA F κ).add_mem hg ((schA F κ).smul_mem c hf)`. Establish `h` using `eLpNorm_two_eq (hiso μ hμ _ hw)`. Rewrite `h` using `[map_add, map_smul]`. Rewrite using `[← MemLp.toLp_const_smul, ← MemLp.toLp_add, ← MemLp.toLp_const_smul, ← MemLp.toLp_add, Lp.norm_toLp, Lp.norm_toLp, h]`.

Establish `e1 : ‖hTg2.toLp + hTf2.toLp‖ = ‖hg2.toLp + hf2.toLp‖` using `by simpa using hN 1`. Establish `e2 : ‖hTg2.toLp - hTf2.toLp‖ = ‖hg2.toLp - hf2.toLp‖`. Simplify `hN (-1)` using `[sub_eq_add_neg]`. Establish `e3 : ‖hTg2.toLp + (RCLike.I : ℂ) • hTf2.toLp‖ = ‖hg2.toLp + (RCLike.I : ℂ) • hf2.toLp‖` using `hN _`. Establish `e4 : ‖hTg2.toLp - (RCLike.I : ℂ) • hTf2.toLp‖ = ‖hg2.toLp - (RCLike.I : ℂ) • hf2.toLp‖`.

Use `hN (-(RCLike.I : ℂ))` as an intermediate fact. Simplify `this` using `only [neg_smul, ← sub_eq_add_neg]`. Rewrite using `[inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, e1, e2, e3, e4]`.
-/
theorem pairing_eq : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ φ ∈ schA F κ, T φ ∈ schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ φ ∈ schA F κ,
      ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f ∈ schA F κ, ∀ g ∈ schA F κ,
      ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  intro F _ _ κ _ T hpres hiso
  letI : MeasurableSpace (κ → AF F) := borel _
  intro μ hμ f hf g hg
  have hmem : ∀ φ ∈ schA F κ, MemLp φ 2 μ := fun φ hφ => GlobalTheory.WeilM.schA_memLp_two F κ μ hμ φ hφ
  have hf2 := hmem f hf
  have hg2 := hmem g hg
  have hTf2 := hmem (T f) (hpres f hf)
  have hTg2 := hmem (T g) (hpres g hg)
  rw [integral_mul_conj_eq_inner hTf2 hTg2, integral_mul_conj_eq_inner hf2 hg2]
  have hN : ∀ c : ℂ, ‖hTg2.toLp + c • hTf2.toLp‖ = ‖hg2.toLp + c • hf2.toLp‖ := by
    intro c
    have hw : g + c • f ∈ schA F κ := (schA F κ).add_mem hg ((schA F κ).smul_mem c hf)
    have h := eLpNorm_two_eq (hiso μ hμ _ hw)
    rw [map_add, map_smul] at h
    rw [← MemLp.toLp_const_smul, ← MemLp.toLp_add, ← MemLp.toLp_const_smul, ← MemLp.toLp_add,
      Lp.norm_toLp, Lp.norm_toLp, h]
  have e1 : ‖hTg2.toLp + hTf2.toLp‖ = ‖hg2.toLp + hf2.toLp‖ := by simpa using hN 1
  have e2 : ‖hTg2.toLp - hTf2.toLp‖ = ‖hg2.toLp - hf2.toLp‖ := by
    simpa [sub_eq_add_neg] using hN (-1)
  have e3 : ‖hTg2.toLp + (RCLike.I : ℂ) • hTf2.toLp‖ = ‖hg2.toLp + (RCLike.I : ℂ) • hf2.toLp‖ := hN _
  have e4 : ‖hTg2.toLp - (RCLike.I : ℂ) • hTf2.toLp‖ = ‖hg2.toLp - (RCLike.I : ℂ) • hf2.toLp‖ := by
    have := hN (-(RCLike.I : ℂ))
    simpa only [neg_smul, ← sub_eq_add_neg] using this
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, e1, e2, e3, e4]

end GlobalTheory.L2PairingPolar

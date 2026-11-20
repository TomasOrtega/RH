import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualMeasuresAndAbsKScale
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped NNReal

noncomputable section

namespace GlobalTheory.JR.WeilQuad

/- English proof (translation)
Introduce `F E _ _ _ _ U A ψ x μ ω hH s φ _ y`. Use `U.charZero` as an intermediate fact. Use `U.ultraF` as an intermediate fact. Use `U.lcF` as an intermediate fact. Use `EtMeas.finite_L A` as an intermediate fact.

Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A.L`. Establish `: IsTopologicalRing A.L` using `IsModuleTopology.isTopologicalRing F A.L`. Establish `hN : distribHaarChar A.L (MeasScale.unitL A s) = distribHaarChar A.K s ^ 2`. Take `⟨⟨b⟩, -, -, -, -⟩` from `GlobalTheory.JR.Et.quadratic_structure F E A`. Take `⟨_, _, _, _, -⟩` from `EtMeas.top_facts F A.K`.

Establish `: ContinuousStar A.L` using `⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩`. Rewrite using `[← map_pow]`. Use `GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F)) (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_` and prove the remaining obligations. Simplify using `[MeasScale.unitL, A.star_K, pow_two]`. Establish `hμ : μ.IsAddHaarMeasure` using `hH.2.2.2.1.1`.

Establish `hinv : algebraMap A.K A.L (s : A.K) * algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `key : ∀ y', φ ((s : A.K) • y') * A.kerL ψ x y' y = (fun u => φ u * A.kerL ψ x u (((s⁻¹ : A.Kˣ) : A.K) • y)) (MeasScale.unitL A s • y')`. Introduce `y'`. Simplify using `only [MeasScale.unitL_smul, Et.kerL]`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def, star_mul', A.star_K]`. Use `congr 4`. Take the linear combination `(star y' * y) * hinv.symm`. Simplify using `only [fOp, fourB]`. Rewrite using `[integral_congr_ae (Eventually.of_forall key), MeasScale.integral_units_smul μ (MeasScale.unitL A s) (fun u => φ u * A.kerL ψ x u (((s⁻¹ : A.Kˣ) : A.K) • y)), hN, EtMeas.absK_unit]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem fOp_comp_smul : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (φ : A.L → ℂ), IsTest φ → ∀ y,
      fOp A ψ x μ (fun y' => φ ((s : A.K) • y')) y =
        ((A.absK s : ℂ) ^ 2)⁻¹ * fOp A ψ x μ φ (((s⁻¹ : A.Kˣ) : A.K) • y) := by
  intro F E _ _ _ _ U A ψ x μ ω hH s φ _ y
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hN : distribHaarChar A.L (MeasScale.unitL A s) = distribHaarChar A.K s ^ 2 := by
    obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
    obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
    have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
    rw [← map_pow]
    refine GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_
    simp [MeasScale.unitL, A.star_K, pow_two]
  have hμ : μ.IsAddHaarMeasure := hH.2.2.2.1.1
  have hinv : algebraMap A.K A.L (s : A.K) * algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have key : ∀ y', φ ((s : A.K) • y') * A.kerL ψ x y' y =
      (fun u => φ u * A.kerL ψ x u (((s⁻¹ : A.Kˣ) : A.K) • y)) (MeasScale.unitL A s • y') := by
    intro y'
    simp only [MeasScale.unitL_smul, Et.kerL]
    rw [Algebra.smul_def, Algebra.smul_def, star_mul', A.star_K]
    congr 4
    linear_combination (star y' * y) * hinv.symm
  simp only [fOp, fourB]
  rw [integral_congr_ae (Eventually.of_forall key),
    MeasScale.integral_units_smul μ (MeasScale.unitL A s)
      (fun u => φ u * A.kerL ψ x u (((s⁻¹ : A.Kˣ) : A.K) • y)), hN, EtMeas.absK_unit]
  push_cast
  rfl

end GlobalTheory.JR.WeilQuad

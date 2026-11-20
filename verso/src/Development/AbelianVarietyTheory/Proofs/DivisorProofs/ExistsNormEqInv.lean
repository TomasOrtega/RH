import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellInt
import GroundTheory.GlobalFields.LocalAtPlace
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open GlobalTheory.PoleFactor

namespace GlobalTheory.NormFvFacts

/- English proof (translation)
Establish `h1 : Ideal.absNorm v.asIdeal ≠ 1` using `fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)`. Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0` using `fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Conclude with `(by omega : 1 < Ideal.absNorm v.asIdeal)` after adjusting the coercions.
-/
theorem absNorm_gt_one (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    1 < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast (by omega : 1 < Ideal.absNorm v.asIdeal)

/- English proof (translation)
Establish `hv : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Use `⟨Multiplicative.toAdd (WithZero.unzero hv), ?_⟩` and prove the remaining obligations. Rewrite using `[FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow]`. Both sides reduce to the same expression.
-/
theorem norm_eq_zpow (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : Fv F v) (hx : x ≠ 0) : ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow]
  rfl

/- English proof (translation)
Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `Valued.toNormedField.norm_le_one_iff`.
-/
theorem norm_le_one_iff (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : Fv F v) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Establish `h : Valued.v ((π : F) : v.adicCompletion F) = WithZero.exp (-1)`. Rewrite using `[v.valuedAdicCompletion_eq_valuation']`. Conclude with `hπ`. Use `⟨((π : F) : v.adicCompletion F), ?_⟩` and prove the remaining obligations.

Rewrite using `[FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]`. Establish `key : ∀ (a : ℤ) (h : WithZero.exp a ≠ 0), Multiplicative.toAdd (WithZero.unzero h) = a` using `fun a h => rfl`. Rewrite using `[key, zpow_neg_one]`. Both sides reduce to the same expression.
-/
theorem exists_norm_eq_inv (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : Fv F v, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h : Valued.v ((π : F) : v.adicCompletion F) = WithZero.exp (-1) := by
    rw [v.valuedAdicCompletion_eq_valuation']; exact hπ
  refine ⟨((π : F) : v.adicCompletion F), ?_⟩
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  have key : ∀ (a : ℤ) (h : WithZero.exp a ≠ 0), Multiplicative.toAdd (WithZero.unzero h) = a := fun a h => rfl
  rw [key, zpow_neg_one]
  rfl

/- English proof (translation)
Establish `: Countable F` using `(Module.finBasis ℚ F).equivFun.injective.countable`. Establish `: TopologicalSpace.SeparableSpace (Fv F v)` using `⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _, IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩`. Establish `: SecondCountableTopology (Fv F v)` using `UniformSpace.secondCountable_of_separable (Fv F v)`. Establish `: LocallyCompactSpace (Fv F v)` using `inferInstance`. Use `infer_instance`.
-/
theorem sigmaFinite_haar (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fv F v)) (hμ : μ.IsAddHaarMeasure) : SigmaFinite μ := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (Fv F v) :=
    ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
  have : SecondCountableTopology (Fv F v) := UniformSpace.secondCountable_of_separable (Fv F v)
  have : LocallyCompactSpace (Fv F v) := inferInstance
  infer_instance

end GlobalTheory.NormFvFacts

open GlobalTheory.NormFvFacts in

/- English proof (translation)
Introduce `F _ _ v` and use `⟨absNorm_gt_one F v, norm_eq_zpow F v, norm_le_one_iff F v, exists_norm_eq_inv F v, fun μ hμ => sigmaFinite_haar F v μ hμ⟩`.
-/
theorem GlobalTheory.NormFvFacts.main : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), 1 < (Ideal.absNorm v.asIdeal : ℝ) ∧ (∀ x : Fv F v, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k) ∧ (∀ x : Fv F v, ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F) ∧ (∃ ϖ : Fv F v, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) ∧ ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure → SigmaFinite μ :=
  fun F _ _ v => ⟨absNorm_gt_one F v, norm_eq_zpow F v, norm_le_one_iff F v, exists_norm_eq_inv F v,
    fun μ hμ => sigmaFinite_haar F v μ hμ⟩

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi.BallVol

/- English proof (translation)
Introduce `F _ _ v lam hlam k a`. Take `⟨hHaar, h1⟩` from `hlam`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Use `haveI : ProperSpace (Fv F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v`. Use `haveI : lam.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure lam`.

Establish `htr : (fun z => z - a) ⁻¹' ballV v k = (fun z => z + -a) ⁻¹' ballV v k`. Simplify using `only [sub_eq_add_neg]`. Rewrite using `[htr, measure_preimage_add_right]`. Take `⟨π, hπ⟩` from `HeightOneSpectrum.valuation_exists_uniformizer F v`. Set `ϖ : Fv F v` to `((π : v.adicCompletion F) : Fv F v)`.

Establish `hvϖ : Valued.v ϖ = WithZero.exp (-1)`. Rewrite using `[← hπ]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h`.

Rewrite `hvϖ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hvϖ.symm`. Use `open Pointwise in`. Establish `hball : ballV v k = (ϖ ^ k) • (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `z`.

Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero k hϖ0)]`. Simplify using `only [ballV, Set.mem_ofPred_eq, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, smul_eq_mul, map_mul, map_inv₀, map_pow, hvϖ]`. Establish `hk : (WithZero.exp (-1 : ℤ)) ^ k = WithZero.exp (-(k : ℤ))`. Rewrite using `[← WithZero.exp_nsmul]`. Simplify using the standard rewrite rules.

Rewrite using `[hk, inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]`. Rewrite using `[hball]`. Establish `hu : IsUnit (ϖ ^ k)` using `(pow_ne_zero k hϖ0).isUnit`. Use `open Pointwise in`. Establish `key` using `distribHaarChar_mul lam hu.unit (v.adicCompletionIntegers F : Set (Fv F v))`.

Rewrite `key` using `[Units.smul_def, IsUnit.unit_spec, h1, mul_one]`. Rewrite using `[← key]`. Establish `hm` using `GlobalTheory.GaugeProdFormula.modu_finite F v (ϖ ^ k) (pow_ne_zero k hϖ0)`. Rewrite `hm` using `[GlobalTheory.GaugeEx.modu, dif_pos hu]`. Establish `hn : ‖ϖ‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹`.

Rewrite using `[NumberField.FinitePlace.norm_def, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π, hπ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]`. Use `show (((Ideal.absNorm v.asIdeal : NNReal) ^ (-1 : ℤ) : NNReal) : ℝ) = _`. Rewrite using `[zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]`. Rewrite `hm` using `[norm_pow, hn, inv_pow]`. Rewrite using `[← hm, ENNReal.ofReal_coe_nnreal]`.
-/
theorem measure_translate_ballV : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (k : ℕ) (a : Fv F v), lam ((fun z => z - a) ⁻¹' ballV v k) = ENNReal.ofReal (((Ideal.absNorm v.asIdeal : ℝ) ^ k)⁻¹) := by
  intro F _ _ v lam hlam k a
  obtain ⟨hHaar, h1⟩ := hlam
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : ProperSpace (Fv F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : lam.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure lam
  have htr : (fun z => z - a) ⁻¹' ballV v k = (fun z => z + -a) ⁻¹' ballV v k := by
    simp only [sub_eq_add_neg]
  rw [htr, measure_preimage_add_right]
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  let ϖ : Fv F v := ((π : v.adicCompletion F) : Fv F v)
  have hvϖ : Valued.v ϖ = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hvϖ
    exact WithZero.exp_ne_zero hvϖ.symm
  open Pointwise in
  have hball : ballV v k = (ϖ ^ k) • (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero k hϖ0)]
    simp only [ballV, Set.mem_ofPred_eq, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      smul_eq_mul, map_mul, map_inv₀, map_pow, hvϖ]
    have hk : (WithZero.exp (-1 : ℤ)) ^ k = WithZero.exp (-(k : ℤ)) := by
      rw [← WithZero.exp_nsmul]; simp
    rw [hk, inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]
  rw [hball]
  have hu : IsUnit (ϖ ^ k) := (pow_ne_zero k hϖ0).isUnit
  open Pointwise in
  have key := distribHaarChar_mul lam hu.unit (v.adicCompletionIntegers F : Set (Fv F v))
  rw [Units.smul_def, IsUnit.unit_spec, h1, mul_one] at key
  rw [← key]
  have hm := GlobalTheory.GaugeProdFormula.modu_finite F v (ϖ ^ k) (pow_ne_zero k hϖ0)
  rw [GlobalTheory.GaugeEx.modu, dif_pos hu] at hm
  have hn : ‖ϖ‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := by
    rw [NumberField.FinitePlace.norm_def, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π, hπ,
      WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    show (((Ideal.absNorm v.asIdeal : NNReal) ^ (-1 : ℤ) : NNReal) : ℝ) = _
    rw [zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]
  rw [norm_pow, hn, inv_pow] at hm
  rw [← hm, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.CompanionTheory.Equi.BallVol

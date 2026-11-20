import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiserStatement

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.BlockVal

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.
-/
theorem normV_eq_absNorm {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

open NumberField IsDedekindDomain Polynomial in
/- English proof (translation)
Establish `hval : (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) = (((μ * η⁻¹).val v : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ)` using `_root_.GlobalTheory.GalChar.block_val μ η r v`. Establish `hN : (_root_.Formalism.ConjugateSelfDual.normV v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ)`. Unfold `_root_.Formalism.ConjugateSelfDual.normV`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hne : Ideal.absNorm v.asIdeal ≠ 0`.

Use `_root_.GlobalTheory.GalChar.absNorm_ne_zero v` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)` using `Nat.cast_pos.mpr (Nat.pos_of_ne_zero hne)`. Use `set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hNdef`. Establish `hpow : (N : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N ^ r : ℝ) : ℂ)`.

Rewrite using `[← Complex.ofReal_cpow hpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : Real.sqrt N ≠ 0` using `(Real.sqrt_pos.mpr hpos).ne'`. Rewrite using `[hval, hN]`.

Establish `hcast : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (N : ℂ)` using `by simp [hNdef]`. Rewrite using `[hcast, hpow, zpow_neg, zpow_natCast, Complex.ofReal_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hs)), mul_one]`.
-/
private theorem block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv {E : Type} [Field E] [NumberField E]
    (μ η : _root_.Formalism.L2.Host.HChar E) (r : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) * (Real.sqrt (_root_.Formalism.ConjugateSelfDual.normV v) : ℂ) ^ (-(r : ℤ)) =
      (((μ * η⁻¹).val v : ℂˣ) : ℂ) := by
  have hval : (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) =
      (((μ * η⁻¹).val v : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) :=
    _root_.GlobalTheory.GalChar.block_val μ η r v
  have hN : (_root_.Formalism.ConjugateSelfDual.normV v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    unfold _root_.Formalism.ConjugateSelfDual.normV
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    have := _root_.GlobalTheory.GalChar.absNorm_ne_zero v
    exact_mod_cast this
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hne)
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hNdef
  have hpow : (N : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N ^ r : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hpos.le]
    congr 2
    ring
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  rw [hval, hN]
  have hcast : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (N : ℂ) := by simp [hNdef]
  rw [hcast, hpow, zpow_neg, zpow_natCast, Complex.ofReal_pow, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hs)), mul_one]

open NumberField IsDedekindDomain Polynomial in

/- English proof (translation)
Introduce `E _ _ K _ ε μ η hμ hη r hr μH ηH hμH hηH`. Establish `hχ : (μH * ηH⁻¹).χ = ((μ * η⁻¹ : _root_.Formalism.L2.Host.HChar E) : _root_.Neutral.B1.Ideles E →* ℂˣ)`. Rewrite using `[_root_.Formalism.L2.NC.HC.mul_χ, _root_.Formalism.L2.NC.HC.inv_χ, hμH, hηH]`. Simplify using the standard rewrite rules. Establish `hblock` using `_root_.GlobalTheory.GalChar.AlmostIn.block hμ hη hr`.

Unfold `_root_.GlobalTheory.GalChar.AlmostIn at hblock`. Use `filter_upwards [hblock, _root_.GlobalTheory.GalChar.unr_ae (μ * η⁻¹)] with v hv hunr`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv]`. Conclude with `(_root_.GlobalTheory.HeckeUnifVal.at_val_and_unr_iff (μ * η⁻¹) (μH * ηH⁻¹) hχ v).1 hunr`.

Take `⟨y, hy⟩` from `hv`. Conclude with `⟨y⁻¹, by rw [map_inv₀, hy]⟩`.
-/
theorem _root_.GlobalTheory.BlockVal.block_val_ae : ∀ {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ)
    (μ η : _root_.Formalism.L2.Host.HChar E),
    _root_.GlobalTheory.GalChar.AlmostIn ε μ → η.ValuesIn (1 / 2) ε → ∀ {r : ℕ}, Odd r →
    ∀ (μH ηH : _root_.Formalism.L2.NC.HC E),
    μH.χ = (μ : _root_.Neutral.B1.Ideles E →* ℂˣ) → ηH.χ = (η : _root_.Neutral.B1.Ideles E →* ℂˣ) → ∀ᶠ v in Filter.cofinite,
    (μH * ηH⁻¹).At v ((((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) *
      (Real.sqrt (_root_.Formalism.ConjugateSelfDual.normV v) : ℂ) ^ (-(r : ℤ))) ∧
    ∃ y : K, ε y = (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ)⁻¹ := by
  intro E _ _ K _ ε μ η hμ hη r hr μH ηH hμH hηH
  have hχ : (μH * ηH⁻¹).χ = ((μ * η⁻¹ : _root_.Formalism.L2.Host.HChar E) : _root_.Neutral.B1.Ideles E →* ℂˣ) := by
    rw [_root_.Formalism.L2.NC.HC.mul_χ, _root_.Formalism.L2.NC.HC.inv_χ, hμH, hηH]
    simp
  have hblock := _root_.GlobalTheory.GalChar.AlmostIn.block hμ hη hr
  unfold _root_.GlobalTheory.GalChar.AlmostIn at hblock
  filter_upwards [hblock, _root_.GlobalTheory.GalChar.unr_ae (μ * η⁻¹)] with v hv hunr
  refine ⟨?_, ?_⟩
  · rw [block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv]
    exact (_root_.GlobalTheory.HeckeUnifVal.at_val_and_unr_iff (μ * η⁻¹) (μH * ηH⁻¹) hχ v).1 hunr
  · obtain ⟨y, hy⟩ := hv
    exact ⟨y⁻¹, by rw [map_inv₀, hy]⟩

end GlobalTheory.BlockVal

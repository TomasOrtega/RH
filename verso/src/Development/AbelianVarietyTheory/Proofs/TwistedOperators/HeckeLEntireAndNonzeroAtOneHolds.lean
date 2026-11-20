import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLSeriesContinuation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealMulAbsNormCpowEqExpTsum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EulerProductNeZeroOneOfEntire
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneSubRePosOfNormLeHalf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DedekindZetaEulerProductMulSubOneEntire
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RayInvariantContinuousEqOne
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtensionEmbeddingMixedSymmOfIsComplex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdealCharacterOfUnitaryHeckeCharStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfInfOfVal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaEulerProductNeZeroOneAddMulI

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeOne
open GlobalTheory.CMVal (eulerFactor IsHeckeL)
variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `NumberField.HeightOneSpectrum.one_lt_absNorm P`.
-/
theorem two_le_N (P : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm P.asIdeal :=
  NumberField.HeightOneSpectrum.one_lt_absNorm P

/- English proof (translation)
The claim follows from `((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2`.
-/
theorem sumN (σ : ℝ) (hσ : 1 < σ) : Summable fun P : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) :=
  ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 K)`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩`.
-/
theorem nonemptyN : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩

noncomputable def cf (χ : HChar K) (P : HeightOneSpectrum (𝓞 K)) : ℂ := if χ.UnrAt P then ((χ.val P : ℂˣ) : ℂ) else 0

/- English proof (translation)
Unfold `cf`. Use `split_ifs`. Conclude with `(h _).le`. Simplify using the standard rewrite rules.
-/
theorem norm_cf {χ : HChar K} (h : χ.IsUnitary) (P : HeightOneSpectrum (𝓞 K)) : ‖cf χ P‖ ≤ 1 := by
  unfold cf; split_ifs
  · exact (h _).le
  · simp

/- English proof (translation)
Use `(((GlobalTheory.eulerProduct_eq_exp_and_pos _ (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal) (cf χ) two_le_N (norm_cf h) sumN).1 s hs).2).congr_fun fun P => ?_` and prove the remaining obligations. Apply the tactic sequence `unfold eulerFactor cf; split_ifs <;> simp`.
-/
theorem hasProd_exp {χ : HChar K} (h : χ.IsUnitary) {s : ℂ} (hs : 1 < s.re) : HasProd (eulerFactor χ s)
    (Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - cf χ P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))) := by
  refine (((GlobalTheory.eulerProduct_eq_exp_and_pos _ (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal) (cf χ) two_le_N
    (norm_cf h) sumN).1 s hs).2).congr_fun fun P => ?_
  unfold eulerFactor cf; split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `v`. Establish `hiff : (χ * normChar K t).UnrAt v ↔ χ.UnrAt v` using `⟨fun h => by simpa using h.mul (unrAt_normChar t v).inv, fun h => h.mul (unrAt_normChar t v)⟩`. Establish `hN` using `two_le_N v`. Unfold `eulerFactor`. Distinguish the cases in `h : χ.UnrAt v`.

Rewrite using `[if_pos h, if_pos (hiff.2 h), Formalism.L2.Host.HChar.val_mul, Units.val_mul, val_normChar, mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0))]`. Use `congr 4`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_neg (mt hiff.1 h)]`.
-/
theorem eulerFactor_mul_normChar (χ : HChar K) (t : ℝ) (s : ℂ) :
    eulerFactor (χ * normChar K t) s = eulerFactor χ (s + (t : ℂ) * Complex.I) := by
  funext v
  have hiff : (χ * normChar K t).UnrAt v ↔ χ.UnrAt v :=
    ⟨fun h => by simpa using h.mul (unrAt_normChar t v).inv, fun h => h.mul (unrAt_normChar t v)⟩
  have hN := two_le_N v
  unfold eulerFactor
  by_cases h : χ.UnrAt v
  · rw [if_pos h, if_pos (hiff.2 h), Formalism.L2.Host.HChar.val_mul, Units.val_mul, val_normChar, mul_assoc,
      ← Complex.cpow_add _ _ (by exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0))]
    congr 4; ring
  · rw [if_neg h, if_neg (mt hiff.1 h)]

/- English proof (translation)
Take `⟨t, φ, hφ1, hφ2, hφ3, hφ4, hφ5⟩` from `GlobalTheory.HeckeOne.exists_normChar_smooth_homogeneous_inf K χ hu`. Use `set χ₀ := χ * normChar K (-t) with hχ₀`. Establish `he : χ = χ₀ * normChar K t`. Rewrite using `[hχ₀, mul_assoc, ← normChar_add, neg_add_cancel, normChar_zero, mul_one]`. Establish `hu₀ : χ₀.IsUnitary` using `hu.mul (isUnitary_normChar _)`.

Take `⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩` from `GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar K χ₀ hu₀`. Establish `hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)` using `fun β h0 h1 => by`. Establish `h0' : (β : K) ≠ 0` using `by exact_mod_cast h0`. Rewrite using `[hXβ β (Units.mk0 _ h0') rfl h1, ← hφ5]`. Both sides reduce to the same expression.

Establish `hJ : ∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hφ` using `GlobalTheory.eq_one_of_homogeneous_of_eq_one_on_class K m φ hm hφ3.continuousOn hφ2 (fun β h0 h1 => by`. Rewrite using `[← hβ β h0 h1]`.

Use `hcon _ (by rwa [Ne, Ideal.span_singleton_eq_bot]) ?_` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one, show (1 : 𝓞 K) = β - (β - 1) by ring]`. Conclude with `Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self β)) (Ideal.mem_sup_right h1))`. Establish `h1 : χ₀ = 1` using `GlobalTheory.HeckeUnrTrivial.eq_one_of_inf_of_val K χ₀ (fun k => by`. Use `hφ (mixedEmbedding K (k : K)) (by` as an intermediate fact.

Rewrite using `[mixedEmbedding.norm_eq_norm]`. Conclude with `abs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 k.ne_zero))` after adjusting the coercions. Rewrite `this` using `[hφ5, inv_eq_one]`. Conclude with `Units.ext this) fun v hv => by`. Establish `h2` using `hXP v`.

Rewrite `h2` using `[if_pos hv]`. Use `Units.ext (h2.symm.trans (hcon _ v.ne_bot ?_))` and prove the remaining obligations. Assume the negation of the conclusion as `h3`. Conclude with `(χ₀.val v).ne_zero (h2.symm.trans (hXz _ h3))`. Conclude with `hχ ⟨t, (isNormPow_iff _ _).2 (by rw [he, h1, one_mul])⟩`.

Establish `hle : ∀ I, ‖X I‖ ≤ 1` using `fun I => by`. Distinguish the cases in `hI : I = ⊥`. Simplify using `[hI, hX0]`. Distinguish the cases in `hI' : I ⊔ m = ⊤`. Conclude with `(hXn I hI hI').le`.

Simplify using `[hXz I hI']`. Take `⟨Z, hZd, hZ, hZ1⟩` from `GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hX0 hXm hXn hXz hφ1 hφ2 hφ3 hφ4 hβ`. Establish `hd : Differentiable ℂ (dslope Z 1)`. Rewrite `hZd`, the goal using `[← differentiableOn_univ]`. Conclude with `(Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd`.

Use `⟨fun s => dslope Z 1 (s + (t : ℂ) * Complex.I), hd.comp (by fun_prop), fun s hs => ?_⟩` and prove the remaining obligations. Establish `hs' : 1 < (s + (t : ℂ) * Complex.I).re` using `by simpa using hs`. Rewrite using `[he, eulerFactor_mul_normChar]`. Use `hasProd_exp hu₀ hs' using 1` and compare the differences between its conclusion and the goal. Establish `hs1 : s + (t : ℂ) * Complex.I ≠ 1` using `fun h => by rw [h] at hs'; simp at hs'`.

Establish `hs2` using `sub_ne_zero.mpr hs1`. Use `beta_reduce`. Rewrite using `[dslope_of_ne _ hs1, slope_def_field, hZ1 hJ, hZ _ hs', GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hX0 hX1 hXm hle _ hs', sub_zero, mul_div_cancel_left₀ _ hs2]`. Simplify using `only [hXP, cf]`.
-/
theorem entire_of_not_normPow {χ : HChar K} (hu : χ.IsUnitary) (hχ : ¬ ∃ t : ℝ, IsNormPow χ t) :
    ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ := by
  obtain ⟨t, φ, hφ1, hφ2, hφ3, hφ4, hφ5⟩ := GlobalTheory.HeckeOne.exists_normChar_smooth_homogeneous_inf K χ hu
  set χ₀ := χ * normChar K (-t) with hχ₀
  have he : χ = χ₀ * normChar K t := by
    rw [hχ₀, mul_assoc, ← normChar_add, neg_add_cancel, normChar_zero, mul_one]
  have hu₀ : χ₀.IsUnitary := hu.mul (isUnitary_normChar _)
  obtain ⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩ := GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar K χ₀ hu₀
  have hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β) := fun β h0 h1 => by
    have h0' : (β : K) ≠ 0 := by exact_mod_cast h0
    rw [hXβ β (Units.mk0 _ h0') rfl h1, ← hφ5]; rfl
  have hJ : ∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hφ := GlobalTheory.eq_one_of_homogeneous_of_eq_one_on_class K m φ hm hφ3.continuousOn hφ2 (fun β h0 h1 => by
      rw [← hβ β h0 h1]
      refine hcon _ (by rwa [Ne, Ideal.span_singleton_eq_bot]) ?_
      rw [Ideal.eq_top_iff_one, show (1 : 𝓞 K) = β - (β - 1) by ring]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self β)) (Ideal.mem_sup_right h1))
    have h1 : χ₀ = 1 := GlobalTheory.HeckeUnrTrivial.eq_one_of_inf_of_val K χ₀ (fun k => by
      have := hφ (mixedEmbedding K (k : K)) (by
        rw [mixedEmbedding.norm_eq_norm]
        exact_mod_cast abs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 k.ne_zero))
      rw [hφ5, inv_eq_one] at this
      exact Units.ext this) fun v hv => by
      have h2 := hXP v
      rw [if_pos hv] at h2
      refine Units.ext (h2.symm.trans (hcon _ v.ne_bot ?_))
      by_contra h3
      exact (χ₀.val v).ne_zero (h2.symm.trans (hXz _ h3))
    exact hχ ⟨t, (isNormPow_iff _ _).2 (by rw [he, h1, one_mul])⟩
  have hle : ∀ I, ‖X I‖ ≤ 1 := fun I => by
    by_cases hI : I = ⊥
    · simp [hI, hX0]
    by_cases hI' : I ⊔ m = ⊤
    · exact (hXn I hI hI').le
    · simp [hXz I hI']
  obtain ⟨Z, hZd, hZ, hZ1⟩ := GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hX0 hXm hXn hXz hφ1 hφ2 hφ3 hφ4 hβ
  have hd : Differentiable ℂ (dslope Z 1) := by
    rw [← differentiableOn_univ] at hZd ⊢
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd
  refine ⟨fun s => dslope Z 1 (s + (t : ℂ) * Complex.I), hd.comp (by fun_prop), fun s hs => ?_⟩
  have hs' : 1 < (s + (t : ℂ) * Complex.I).re := by simpa using hs
  rw [he, eulerFactor_mul_normChar]
  convert hasProd_exp hu₀ hs' using 1
  have hs1 : s + (t : ℂ) * Complex.I ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
  have hs2 := sub_ne_zero.mpr hs1
  beta_reduce
  rw [dslope_of_ne _ hs1, slope_def_field, hZ1 hJ, hZ _ hs',
    GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hX0 hX1 hXm hle _ hs', sub_zero, mul_div_cancel_left₀ _ hs2]
  simp only [hXP, cf]

/- English proof (translation)
Introduce `K _ _ χ hu`. Use `⟨entire_of_not_normPow hu, fun h1 => ?_⟩` and prove the remaining obligations. Take `⟨Z, hZd, hZ⟩` from `GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K`. Distinguish the cases in `hχ : ∃ t : ℝ, IsNormPow χ t`. Take `⟨t, ht⟩` from `hχ`.

Rewrite `ht` using `[isNormPow_iff]`. Substitute `ht` using the available equality. Establish `ht0 : t ≠ 0` using `fun h => h1 (h ▸ normChar_zero)`. Establish `ht1 : (1 : ℂ) + (t : ℂ) * Complex.I - 1 ≠ 0` using `by simpa using ht0`. Use `⟨fun s => Z (s + (t : ℂ) * Complex.I) / (s + (t : ℂ) * Complex.I - 1), ⟨?_, fun s hs => ?_⟩, div_ne_zero (GlobalTheory.zetaEulerProduct_ne_zero_one_add_mul_I _ _ two_le_N sumN nonemptyN Z hZd hZ t ht0) ht1⟩` and prove the remaining obligations.

Conclude with `((hZd.comp (f := fun s : ℂ => s + (t : ℂ) * Complex.I) (by fun_prop)).analyticAt 1).div (by fun_prop) ht1`. Establish `hs' : 1 < (s + (t : ℂ) * Complex.I).re` using `by simpa using hs`. Establish `hs1 : s + (t : ℂ) * Complex.I ≠ 1` using `fun h => by rw [h] at hs'; simp at hs'`. Rewrite using `[← one_mul (normChar K t), eulerFactor_mul_normChar]`. Use `hasProd_exp (χ := 1) (fun _ => by simp) hs' using 1` and compare the differences between its conclusion and the goal.

Establish `hc : ∀ P : HeightOneSpectrum (𝓞 K), cf 1 P = 1` using `fun P => if_pos fun _ _ => rfl`. Simplify using `only [hc]`. Rewrite using `[hZ _ hs', mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)]`. Take `⟨Λ, hΛ⟩` from `entire_of_not_normPow hu hχ`. Conclude with `⟨Λ, isContAtOne_of_isHeckeL hΛ, GlobalTheory.eulerProduct_ne_zero_one_of_entire _ _ (cf χ) two_le_N (norm_cf hu) sumN nonemptyN Z Λ hZd hΛ.1 hZ fun s hs => (hΛ.2 s hs).unique (hasProd_exp hu hs)⟩`.
-/
theorem _root_.GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne := by
  intro K _ _ χ hu
  refine ⟨entire_of_not_normPow hu, fun h1 => ?_⟩
  obtain ⟨Z, hZd, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  by_cases hχ : ∃ t : ℝ, IsNormPow χ t
  · obtain ⟨t, ht⟩ := hχ
    rw [isNormPow_iff] at ht
    subst ht
    have ht0 : t ≠ 0 := fun h => h1 (h ▸ normChar_zero)
    have ht1 : (1 : ℂ) + (t : ℂ) * Complex.I - 1 ≠ 0 := by simpa using ht0
    refine ⟨fun s => Z (s + (t : ℂ) * Complex.I) / (s + (t : ℂ) * Complex.I - 1), ⟨?_, fun s hs => ?_⟩,
      div_ne_zero (GlobalTheory.zetaEulerProduct_ne_zero_one_add_mul_I _ _ two_le_N sumN nonemptyN Z hZd hZ t ht0) ht1⟩
    · exact ((hZd.comp (f := fun s : ℂ => s + (t : ℂ) * Complex.I) (by fun_prop)).analyticAt 1).div (by fun_prop) ht1
    · have hs' : 1 < (s + (t : ℂ) * Complex.I).re := by simpa using hs
      have hs1 : s + (t : ℂ) * Complex.I ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
      rw [← one_mul (normChar K t), eulerFactor_mul_normChar]
      convert hasProd_exp (χ := 1) (fun _ => by simp) hs' using 1
      have hc : ∀ P : HeightOneSpectrum (𝓞 K), cf 1 P = 1 := fun P => if_pos fun _ _ => rfl
      simp only [hc]
      rw [hZ _ hs', mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)]
  · obtain ⟨Λ, hΛ⟩ := entire_of_not_normPow hu hχ
    exact ⟨Λ, isContAtOne_of_isHeckeL hΛ, GlobalTheory.eulerProduct_ne_zero_one_of_entire _ _ (cf χ) two_le_N (norm_cf hu) sumN
      nonemptyN Z Λ hZd hΛ.1 hZ fun s hs => (hΛ.2 s hs).unique (hasProd_exp hu hs)⟩

end GlobalTheory.HeckeOne

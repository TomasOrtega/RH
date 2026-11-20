import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ProdFormula

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise

section Infinite

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `rfl : m = GroundTheory.Global.measurableSpace_infiniteAdeleRing F` from `hm.measurable_eq.trans (GroundTheory.Global.borelSpace_infiniteAdeleRing (K := F)).measurable_eq.symm`. Establish `h` using `Measure.isAddLeftInvariant_eq_smul μ (GroundTheory.Global.infiniteAdeleMeasure F)`. Rewrite using `[h, Measure.map_smul, GroundTheory.Global.map_mul_left_infiniteAdeleMeasure, smul_comm]`.
-/
theorem map_mul_left_infinite {m : MeasurableSpace (InfiniteAdeleRing F)}
    (hm : @BorelSpace _ _ m) (b : (InfiniteAdeleRing F)ˣ) (μ : Measure (InfiniteAdeleRing F))
    (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun y => (b : InfiniteAdeleRing F) * y) =
      ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)‖ • μ := by
  obtain rfl : m = GroundTheory.Global.measurableSpace_infiniteAdeleRing F :=
    hm.measurable_eq.trans (GroundTheory.Global.borelSpace_infiniteAdeleRing (K := F)).measurable_eq.symm
  have h := Measure.isAddLeftInvariant_eq_smul μ (GroundTheory.Global.infiniteAdeleMeasure F)
  rw [h, Measure.map_smul, GroundTheory.Global.map_mul_left_infiniteAdeleMeasure, smul_comm]

/- English proof (translation)
Rewrite using `[InfiniteAdeleRing.norm_def]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `InfinitePlace.Completion.norm_coe w _`.
-/
theorem norm_algebraMap_infinite (a : F) :
    ‖algebraMap F (InfiniteAdeleRing F) a‖ = ∏ w : InfinitePlace F, w a ^ w.mult := by
  rw [InfiniteAdeleRing.norm_def]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  exact InfinitePlace.Completion.norm_coe w _

end Infinite

section Finite

open HeckeCharacterZeroLocus.SiegelWeilU

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Set `ϖ : Fv F v` to `(π : Fv F v)`. Establish `hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]`. Establish `hϖ0 : ϖ ≠ 0`.

Introduce `h`. Rewrite `hϖ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ.symm`. Establish `hva : Valued.v a ≠ 0` using `(Valuation.ne_zero_iff _).2 ha`. Use `set k : ℤ := WithZero.log (Valued.v a) with hk`.

Establish `hu0 : a * ϖ ^ k ≠ 0` using `mul_ne_zero ha (zpow_ne_zero _ hϖ0)`. Establish `hu : Valued.v (a * ϖ ^ k) = 1`. Rewrite using `[map_mul, map_zpow₀, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_zsmul, ← WithZero.exp_add, ← hk, ← WithZero.exp_zero]`. Use `congr 1`. Simplify using the standard rewrite rules.

Establish `hU : Units.mk0 (a * ϖ ^ k) hu0 = Units.mk0 a ha * (Units.mk0 ϖ hϖ0) ^ k` using `by ext; simp [Units.val_zpow_eq_zpow_val]`. Establish `h1` using `PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unit v _ hu hu0`. Rewrite `h1` using `[hU, map_mul, map_zpow, PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unif v ϖ hϖ hϖ0, inv_zpow]`. Establish `hq : ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k ≠ 0` using `zpow_ne_zero _ (by exact_mod_cast PI.UnitaryGroupMassFormula.LocJacTyp.BM.q_ne_zero v)`. Establish `h2 : distribHaarChar (Fv F v) (Units.mk0 a ha) = ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k` using `(mul_inv_eq_one₀ hq).1 h1`.

Rewrite using `[h2]`. Apply `NNReal.coe_injective` to reduce the goal to its premises. Rewrite using `[coe_nnnorm, ← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v ha, ← hk]`. Simplify using the standard rewrite rules.
-/
theorem distribHaarChar_eq_nnnorm (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (ha : a ≠ 0) :
    distribHaarChar (Fv F v) (Units.mk0 a ha) = ‖a‖₊ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  let ϖ : Fv F v := (π : Fv F v)
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  set k : ℤ := WithZero.log (Valued.v a) with hk
  have hu0 : a * ϖ ^ k ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hϖ0)
  have hu : Valued.v (a * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← hk, ← WithZero.exp_zero]
    congr 1
    simp
  have hU : Units.mk0 (a * ϖ ^ k) hu0 = Units.mk0 a ha * (Units.mk0 ϖ hϖ0) ^ k := by
    ext; simp [Units.val_zpow_eq_zpow_val]
  have h1 := PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unit v _ hu hu0
  rw [hU, map_mul, map_zpow, PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unif v ϖ hϖ hϖ0, inv_zpow] at h1
  have hq : ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast PI.UnitaryGroupMassFormula.LocJacTyp.BM.q_ne_zero v)
  have h2 : distribHaarChar (Fv F v) (Units.mk0 a ha) = ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k :=
    (mul_inv_eq_one₀ hq).1 h1
  rw [h2]
  apply NNReal.coe_injective
  rw [coe_nnnorm, ← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v ha, ← hk]
  simp

/- English proof (translation)
Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Use `haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v`. Use `haveI : μ.Regular := inferInstance`. Use extensionality with `S hS`. Rewrite using `[Measure.map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply]`.

Establish `h` using `distribHaarChar_mul μ (Units.mk0 a ha)⁻¹ S`. Establish `e : (fun x => a * x) ⁻¹' S = (Units.mk0 a ha)⁻¹ • S` using `Set.preimage_smul (Units.mk0 a ha) S`. Rewrite using `[e, ← h, map_inv, distribHaarChar_eq_nnnorm]`. Both sides reduce to the same expression.
-/
theorem map_mul_left_finite (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (ha : a ≠ 0)
    (μ : Measure (Fv F v)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun x => a * x) = (‖a‖₊)⁻¹ • μ := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : μ.Regular := inferInstance
  ext S hS
  rw [Measure.map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply]
  have h := distribHaarChar_mul μ (Units.mk0 a ha)⁻¹ S
  have e : (fun x => a * x) ⁻¹' S = (Units.mk0 a ha)⁻¹ • S :=
    Set.preimage_smul (Units.mk0 a ha) S
  rw [e, ← h, map_inv, distribHaarChar_eq_nnnorm]
  rfl

end Finite

section Main

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW

/- English proof (translation)
Introduce `F _ _ a ha`. Establish `hA : 0 < ∏ w : InfinitePlace F, w a ^ w.mult` using `Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 ha) _`. Establish `hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖algebraMap F (Fv F v) a‖).Finite` using `(FinitePlace.hasFiniteMulSupport ha).preimage (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn`. Establish `hprod : (∏ w : InfinitePlace F, w a ^ w.mult) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖ = 1`. Rewrite using `[← prod_abs_eq_one ha, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]`.

Both sides reduce to the same expression. Use `⟨((∏ w : InfinitePlace F, w a ^ w.mult)⁻¹).toNNReal, fun v => (‖algebraMap F (Fv F v) a‖₊)⁻¹, ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hfin.eventually_cofinite_notMem] with v hv`. Establish `h1 : ‖algebraMap F (Fv F v) a‖ = 1` using `by simpa using hv`. Establish `h2 : ‖algebraMap F (Fv F v) a‖₊ = 1` using `NNReal.coe_injective h1`.

Rewrite using `[h2, inv_one]`. Apply `NNReal.coe_injective` to reduce the goal to its premises. Establish `e : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (‖algebraMap F (Fv F v) a‖₊)⁻¹ : ℝ≥0) : ℝ) = (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖)⁻¹`. Rewrite using `[finprod_inv_distrib]`. Rewrite using `[NNReal.coe_inv]`.

Use `congr 1`. Conclude with `NNReal.toRealHom.map_finprod_of_injective NNReal.coe_injective _`. Rewrite using `[NNReal.coe_mul, e, NNReal.coe_one, Real.coe_toNNReal _ (inv_pos.2 hA).le, ← mul_inv, hprod, inv_one]`. Introduce `μ hμ`. Establish `hb : (((Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha))⁻¹ : (Ainf F)ˣ) : Ainf F) = algebraMap F (Ainf F) a⁻¹`.

Simplify using the standard rewrite rules. Establish `h` using `map_mul_left_infinite (F := F) (m := measAinf) ⟨rfl⟩ (Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha)) μ hμ`. Rewrite `h` using `[hb, norm_algebraMap_infinite]`. Establish `e : ∏ w : InfinitePlace F, w a⁻¹ ^ w.mult = (∏ w : InfinitePlace F, w a ^ w.mult)⁻¹`. Rewrite using `[← Finset.prod_inv_distrib]`.

Conclude with `Finset.prod_congr rfl fun w _ => by rw [map_inv₀, inv_pow]`. Rewrite `h` using `[e]`. Conclude with `h`. Introduce `v μ hμ`. Conclude with `map_mul_left_finite v _ ((map_ne_zero _).2 ha) μ hμ`.
-/
theorem unitProd_scalar : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 →
    ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧
      (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by
  intro F _ _ a ha
  have hA : 0 < ∏ w : InfinitePlace F, w a ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 ha) _
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖algebraMap F (Fv F v) a‖).Finite :=
    (FinitePlace.hasFiniteMulSupport ha).preimage
      (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
  have hprod : (∏ w : InfinitePlace F, w a ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖ = 1 := by
    rw [← prod_abs_eq_one ha, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    rfl
  refine ⟨((∏ w : InfinitePlace F, w a ^ w.mult)⁻¹).toNNReal,
    fun v => (‖algebraMap F (Fv F v) a‖₊)⁻¹, ⟨?_, ?_⟩, ?_, ?_⟩
  · filter_upwards [hfin.eventually_cofinite_notMem] with v hv
    have h1 : ‖algebraMap F (Fv F v) a‖ = 1 := by simpa using hv
    have h2 : ‖algebraMap F (Fv F v) a‖₊ = 1 := NNReal.coe_injective h1
    rw [h2, inv_one]
  · apply NNReal.coe_injective
    have e : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (‖algebraMap F (Fv F v) a‖₊)⁻¹ : ℝ≥0) : ℝ) =
        (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖)⁻¹ := by
      rw [finprod_inv_distrib]
      rw [NNReal.coe_inv]
      congr 1
      exact NNReal.toRealHom.map_finprod_of_injective NNReal.coe_injective _
    rw [NNReal.coe_mul, e, NNReal.coe_one, Real.coe_toNNReal _ (inv_pos.2 hA).le, ← mul_inv, hprod, inv_one]
  · intro μ hμ
    have hb : (((Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha))⁻¹ : (Ainf F)ˣ) : Ainf F) =
        algebraMap F (Ainf F) a⁻¹ := by
      simp
    have h := map_mul_left_infinite (F := F) (m := measAinf) ⟨rfl⟩
      (Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha)) μ hμ
    rw [hb, norm_algebraMap_infinite] at h
    have e : ∏ w : InfinitePlace F, w a⁻¹ ^ w.mult = (∏ w : InfinitePlace F, w a ^ w.mult)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [map_inv₀, inv_pow]
    rw [e] at h
    exact h
  · intro v μ hμ
    exact map_mul_left_finite v _ ((map_ne_zero _).2 ha) μ hμ

end Main

end GlobalTheory.CompanionTheory.SW.ProdFormula

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntValuationNormEqSumResidueDegreeMul

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.UnrTate.completion_norms

open GroundTheory.Global.SemiLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h0 : Valued.v a ≠ 0` using `(Valuation.ne_zero_iff _).2 ha`. Rewrite using `[FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]`. Take `⟨c, hc⟩` from `WithZero.ne_zero_iff_exists.mp h0`. Establish `: Multiplicative.toAdd (WithZero.unzero h0) = WithZero.log (Valued.v a)`. Simplify using `only [← hc]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem norm_eq_zpow (v : Pl F) {a : Fv F v} (ha : a ≠ 0) :
    ‖a‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log (Valued.v a) := by
  have h0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  obtain ⟨c, hc⟩ := WithZero.ne_zero_iff_exists.mp h0
  have : Multiplicative.toAdd (WithZero.unzero h0) = WithZero.log (Valued.v a) := by
    simp only [← hc]; rfl
  rw [this]
  push_cast
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[complMap_rfl]`. Use `sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val w _ fun n => ?_)` and prove the remaining obligations. Establish `hc` using `continuous_completionMap (w.under (𝓞 F)) w`. Establish `h1` using `(GlobalTheory.Mem.UnitOpen.isOpen_val_le (w.under (𝓞 F)) (-(n : ℤ))).preimage (continuous_sub_left a)`.

Establish `h2` using `(GlobalTheory.Mem.UnitOpen.isOpen_val_le w (-(n : ℤ))).preimage ((continuous_sub_left (completionMap _ w a)).comp hc)`. Take `⟨k, hk1, hk2⟩` from `(HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) (w.under (𝓞 F))).exists_mem_open (h1.inter h2) ⟨a, by simp, by simp⟩`. Establish `e : GlobalTheory.AdeleBaseChange.locMap F w a - completionMap (w.under (𝓞 F)) w a = GlobalTheory.AdeleBaseChange.locMap F w (a - algebraMap F ((w.under (𝓞 F)).adicCompletion F) k) - (completionMap (w.under (𝓞 F)) w a - completionMap (w.under (𝓞 F)) w (algebraMap F ((w.under (𝓞 F) …`. Rewrite using `[map_sub, GlobalTheory.AdeleBaseChange.locMap_algebraMap, completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (w.adicCompletion E)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Valuation.map_sub_le _ (GlobalTheory.AdeleBaseChange.locMap_valued w n _ hk1) hk2`.
-/
theorem complMap_eq (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (h : w.under (𝓞 F) = v) (a : Fv F v) : complMap h a = completionMap v w a := by
  subst h
  rw [complMap_rfl]
  refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val w _ fun n => ?_)
  have hc := continuous_completionMap (w.under (𝓞 F)) w
  have h1 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le (w.under (𝓞 F)) (-(n : ℤ))).preimage (continuous_sub_left a)
  have h2 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le w (-(n : ℤ))).preimage
    ((continuous_sub_left (completionMap _ w a)).comp hc)
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F)
    (w.under (𝓞 F))).exists_mem_open (h1.inter h2) ⟨a, by simp, by simp⟩
  have e : GlobalTheory.AdeleBaseChange.locMap F w a - completionMap (w.under (𝓞 F)) w a =
      GlobalTheory.AdeleBaseChange.locMap F w (a - algebraMap F ((w.under (𝓞 F)).adicCompletion F) k) -
        (completionMap (w.under (𝓞 F)) w a -
          completionMap (w.under (𝓞 F)) w (algebraMap F ((w.under (𝓞 F)).adicCompletion F) k)) := by
    rw [map_sub, GlobalTheory.AdeleBaseChange.locMap_algebraMap, completionMap_algebraMap,
      IsScalarTower.algebraMap_apply F E (w.adicCompletion E)]
    ring
  rw [e]
  exact Valuation.map_sub_le _ (GlobalTheory.AdeleBaseChange.locMap_valued w n _ hk1) hk2

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rw [toCompl_tmul, tensorEquiv_tmul, Pi.mul_apply, complMap_eq v w.1 h]`. Both sides reduce to the same expression. Consider the case `add y z hy hz => rw [map_add, map_add, hy, hz]`.

Both sides reduce to the same expression.
-/
theorem toCompl_eq (v : Pl F) (w : PlacesOver E v) (h : w.1.under (𝓞 F) = v) (y : Fv F v ⊗[F] E) :
    toCompl h y = tensorEquiv E v y w := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [toCompl_tmul, tensorEquiv_tmul, Pi.mul_apply, complMap_eq v w.1 h]; rfl
  | add y z hy hz => rw [map_add, map_add, hy, hz]; rfl

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : Module.Finite (Fv F v) (CompletionsOver E v) := Module.Finite.equiv (tensorEquiv E v).toLinearEquiv`. Set `b` to `Module.finBasis (Fv F v) (CompletionsOver E v)`. Establish `hlin : Continuous (Algebra.leftMulMatrix b : CompletionsOver E v → Matrix _ _ (Fv F v))` using `IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap`. Establish `h : (Algebra.norm (Fv F v) : CompletionsOver E v → Fv F v) = fun x => (Algebra.leftMulMatrix b x).det`.

Use function extensionality and compare the values at `x`. Conclude with `Algebra.norm_eq_matrix_det b x`. Rewrite using `[h]`. Conclude with `hlin.matrix_det`.
-/
theorem continuous_norm_completionsOver (v : Pl F) :
    Continuous (Algebra.norm (Fv F v) : CompletionsOver E v → Fv F v) := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Module.Finite (Fv F v) (CompletionsOver E v) := Module.Finite.equiv (tensorEquiv E v).toLinearEquiv
  let b := Module.finBasis (Fv F v) (CompletionsOver E v)
  have hlin : Continuous (Algebra.leftMulMatrix b : CompletionsOver E v → Matrix _ _ (Fv F v)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h : (Algebra.norm (Fv F v) : CompletionsOver E v → Fv F v) =
      fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]; exact hlin.matrix_det

/- English proof (translation)
Rewrite using `[mem_aboveF]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Both sides reduce to the same expression. Introduce `h`.

Conclude with `HeightOneSpectrum.ext h`.
-/
theorem mem_aboveF_iff (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) :
    w ∈ Formalism.L2.Host.aboveF (L := E) F v ↔ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
  rw [mem_aboveF]
  constructor
  · rintro rfl; rfl
  · intro h; exact HeightOneSpectrum.ext h

/- English proof (translation)
Use `haveI : w.asIdeal.IsMaximal := w.isMaximal`. Use `haveI : v.asIdeal.IsMaximal := v.isMaximal`. Rewrite using `[← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E) w.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal v.asIdeal, map_pow]`.
-/
theorem absNorm_eq_pow (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E) w.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal v.asIdeal, map_pow]

end GlobalTheory.UnrTate.completion_norms

namespace GlobalTheory.UnrTate.completion_norms

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hq]`.
-/
theorem prod_zpow_eq {ι : Type} (q : ℝ) (hq : q ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    ∏ i ∈ s, q ^ a i = q ^ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hq]

/- English proof (translation)
Use `lt_of_le_of_lt hs ?_` and prove the remaining obligations. Use `conv_rhs => rw [← WithZero.exp_log ht]`. Conclude with `WithZero.exp_lt_exp.2 (by omega)`.
-/
theorem lt_of_le_exp_log_sub_one {t s : WithZero (Multiplicative ℤ)} (ht : t ≠ 0)
    (hs : s ≤ WithZero.exp (WithZero.log t - 1)) : s < t := by
  refine lt_of_le_of_lt hs ?_
  conv_rhs => rw [← WithZero.exp_log ht]
  exact WithZero.exp_lt_exp.2 (by omega)

end GlobalTheory.UnrTate.completion_norms

namespace GlobalTheory.UnrTate

open GroundTheory.Global.SemiLocal completion_norms

/- English proof (translation)
Introduce `F E _ _ _ _ _ v x`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `set z : CompletionsOver E v := tensorEquiv E v x.1 with hz`. Establish `hN : Algebra.norm (Fv F v) x.1 = Algebra.norm (Fv F v) z` using `(Algebra.norm_eq_of_algEquiv (tensorEquiv E v) x.1).symm`. Establish `hzu : IsUnit z` using `x.isUnit.map (tensorEquiv E v)`.

Establish `hzw : ∀ w, z w ≠ 0` using `fun w => (hzu.map (Pi.evalRingHom _ w)).ne_zero`. Establish `hNz : Algebra.norm (Fv F v) z ≠ 0` using `(hzu.map (Algebra.norm (Fv F v))).ne_zero`. Use `set c : Fv F v := Algebra.norm (Fv F v) z with hc`. Establish `hc0 : Valued.v c ≠ 0` using `(Valuation.ne_zero_iff _).2 hNz`. Establish `hzw0 : ∀ w, Valued.v (z w) ≠ 0` using `fun w => (Valuation.ne_zero_iff _).2 (hzw w)`.

Set `U : Set (CompletionsOver E v)` to `(⋂ w, {y | Valued.v (y w - z w) ≤ WithZero.exp (WithZero.log (Valued.v (z w)) - 1)}) ∩ {y | Valued.v (Algebra.norm (Fv F v) y - c) ≤ WithZero.exp (WithZero.log (Valued.v c) - 1)}`. Establish `hU : IsOpen U`. Use `(isOpen_iInter_of_finite fun w => ?_).inter ?_` and prove the remaining obligations. Conclude with `IsOpen.preimage (f := fun y : CompletionsOver E v => y w - z w) ((continuous_apply w).sub continuous_const) (GlobalTheory.Mem.UnitOpen.isOpen_val_le w.1 (WithZero.log (Valued.v (z w)) - 1))`. Conclude with `IsOpen.preimage (f := fun y : CompletionsOver E v => Algebra.norm (Fv F v) y - c) ((continuous_norm_completionsOver v).sub continuous_const) (GlobalTheory.Mem.UnitOpen.isOpen_val_le v (WithZero.log (Valued.v c) - 1))`.

Establish `hzU : z ∈ U`. Use `⟨Set.mem_iInter.2 fun w => ?_, ?_⟩` and prove the remaining obligations. Use `show Valued.v (z w - z w) ≤ _`. Rewrite using `[sub_self, map_zero]`. Conclude with `zero_le'`.

Use `show Valued.v (c - c) ≤ _`. Rewrite using `[sub_self, map_zero]`. Conclude with `zero_le'`. Take `⟨b, hb1, hb2⟩` from `(denseRange_algebraMap_completionsOver E v).exists_mem_open hU ⟨z, hzU⟩`. Establish `hbw : ∀ w : PlacesOver E v, Valued.v (algebraMap E (w.1.adicCompletion E) b) = Valued.v (z w)` using `fun w => Valuation.map_eq_of_sub_lt _ (lt_of_le_exp_log_sub_one (hzw0 w) (Set.mem_iInter.1 hb1 w))`.

Establish `hbN : Valued.v (Algebra.norm (Fv F v) (algebraMap E (CompletionsOver E v) b)) = Valued.v c` using `Valuation.map_eq_of_sub_lt _ (lt_of_le_exp_log_sub_one hc0 hb2)`. Establish `hNb : Algebra.norm (Fv F v) (algebraMap E (CompletionsOver E v) b) = algebraMap F (Fv F v) (Algebra.norm F b)`. Rewrite using `[← tensorEquiv_one_tmul, Algebra.norm_eq_of_algEquiv, norm_one_tmul]`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hbN` using `[hNb, Algebra.norm_zero, map_zero, map_zero]`. Conclude with `hc0 hbN.symm`. Establish `hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0`. Conclude with `(Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors (I := v.asIdeal)).2 (mem_nonZeroDivisors_of_ne_zero v.ne_bot)` after adjusting the coercions. Establish `hL : ((absEv F E v x : ℝ≥0) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ ∑ w ∈ Formalism.L2.Host.aboveF (L` using `E) F v, (w.asIdeal.inertiaDeg (𝓞 F) : ℤ) * WithZero.log (w.valuation E b) := by`.

Rewrite using `[GlobalTheory.Doubling.absEv_apply, coe_nnnorm, hN, norm_eq_zpow v hNz, ← hbN, hNb, Formalism.UG.P.levelaf_valued_algebraMap]`. Conclude with `congrArg _ (GlobalTheory.NormValuation.log_valuation_norm_eq_sum F E v (Units.mk0 b hb0) _ (mem_aboveF_iff v))`. Rewrite using `[hL, ← prod_zpow_eq _ hq]`. Use `Finset.prod_congr rfl fun w hw => ?_` and prove the remaining obligations. Establish `h` using `mem_aboveF.1 hw`.

Use `haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h]; rfl⟩`. Establish `hval : -ordAt v w x = WithZero.log (w.valuation E b)`. Rewrite using `[ordAt, neg_neg, valAt_of_under h, toCompl_eq v ⟨w, inferInstance⟩ h, ← hz, ← hbw ⟨w, inferInstance⟩, Formalism.UG.P.levelaf_valued_algebraMap]`. Rewrite using `[hval, absNorm_eq_pow v w, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]`.
-/
theorem absEv_eq_prod_absNorm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Pl F) (x : (Fv F v ⊗[F] E)ˣ), ((absEv F E v x : ℝ≥0) : ℝ) =
      ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, (Ideal.absNorm w.asIdeal : ℝ) ^ (-GlobalTheory.UnrTate.ordAt v w x) := by
  intro F E _ _ _ _ _ v x
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set z : CompletionsOver E v := tensorEquiv E v x.1 with hz
  have hN : Algebra.norm (Fv F v) x.1 = Algebra.norm (Fv F v) z :=
    (Algebra.norm_eq_of_algEquiv (tensorEquiv E v) x.1).symm
  have hzu : IsUnit z := x.isUnit.map (tensorEquiv E v)
  have hzw : ∀ w, z w ≠ 0 := fun w => (hzu.map (Pi.evalRingHom _ w)).ne_zero
  have hNz : Algebra.norm (Fv F v) z ≠ 0 := (hzu.map (Algebra.norm (Fv F v))).ne_zero
  set c : Fv F v := Algebra.norm (Fv F v) z with hc
  have hc0 : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hNz
  have hzw0 : ∀ w, Valued.v (z w) ≠ 0 := fun w => (Valuation.ne_zero_iff _).2 (hzw w)
  let U : Set (CompletionsOver E v) :=
    (⋂ w, {y | Valued.v (y w - z w) ≤ WithZero.exp (WithZero.log (Valued.v (z w)) - 1)}) ∩
      {y | Valued.v (Algebra.norm (Fv F v) y - c) ≤ WithZero.exp (WithZero.log (Valued.v c) - 1)}
  have hU : IsOpen U := by
    refine (isOpen_iInter_of_finite fun w => ?_).inter ?_
    · exact IsOpen.preimage (f := fun y : CompletionsOver E v => y w - z w)
        ((continuous_apply w).sub continuous_const)
        (GlobalTheory.Mem.UnitOpen.isOpen_val_le w.1 (WithZero.log (Valued.v (z w)) - 1))
    · exact IsOpen.preimage (f := fun y : CompletionsOver E v => Algebra.norm (Fv F v) y - c)
        ((continuous_norm_completionsOver v).sub continuous_const)
        (GlobalTheory.Mem.UnitOpen.isOpen_val_le v (WithZero.log (Valued.v c) - 1))
  have hzU : z ∈ U := by
    refine ⟨Set.mem_iInter.2 fun w => ?_, ?_⟩
    · show Valued.v (z w - z w) ≤ _
      rw [sub_self, map_zero]; exact zero_le'
    · show Valued.v (c - c) ≤ _
      rw [sub_self, map_zero]; exact zero_le'
  obtain ⟨b, hb1, hb2⟩ := (denseRange_algebraMap_completionsOver E v).exists_mem_open hU ⟨z, hzU⟩
  have hbw : ∀ w : PlacesOver E v, Valued.v (algebraMap E (w.1.adicCompletion E) b) = Valued.v (z w) := fun w =>
    Valuation.map_eq_of_sub_lt _ (lt_of_le_exp_log_sub_one (hzw0 w) (Set.mem_iInter.1 hb1 w))
  have hbN : Valued.v (Algebra.norm (Fv F v) (algebraMap E (CompletionsOver E v) b)) = Valued.v c :=
    Valuation.map_eq_of_sub_lt _ (lt_of_le_exp_log_sub_one hc0 hb2)
  have hNb : Algebra.norm (Fv F v) (algebraMap E (CompletionsOver E v) b) =
      algebraMap F (Fv F v) (Algebra.norm F b) := by
    rw [← tensorEquiv_one_tmul, Algebra.norm_eq_of_algEquiv, norm_one_tmul]
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [hNb, Algebra.norm_zero, map_zero, map_zero] at hbN
    exact hc0 hbN.symm
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors (I := v.asIdeal)).2
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot)

  have hL : ((absEv F E v x : ℝ≥0) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^
      ∑ w ∈ Formalism.L2.Host.aboveF (L := E) F v,
        (w.asIdeal.inertiaDeg (𝓞 F) : ℤ) * WithZero.log (w.valuation E b) := by
    rw [GlobalTheory.Doubling.absEv_apply, coe_nnnorm, hN, norm_eq_zpow v hNz, ← hbN, hNb,
      Formalism.UG.P.levelaf_valued_algebraMap]
    exact congrArg _ (GlobalTheory.NormValuation.log_valuation_norm_eq_sum F E v (Units.mk0 b hb0) _ (mem_aboveF_iff v))
  rw [hL, ← prod_zpow_eq _ hq]
  refine Finset.prod_congr rfl fun w hw => ?_
  have h := mem_aboveF.1 hw
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h]; rfl⟩
  have hval : -ordAt v w x = WithZero.log (w.valuation E b) := by
    rw [ordAt, neg_neg, valAt_of_under h, toCompl_eq v ⟨w, inferInstance⟩ h, ← hz, ← hbw ⟨w, inferInstance⟩,
      Formalism.UG.P.levelaf_valued_algebraMap]
  rw [hval, absNorm_eq_pow v w, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]

end GlobalTheory.UnrTate

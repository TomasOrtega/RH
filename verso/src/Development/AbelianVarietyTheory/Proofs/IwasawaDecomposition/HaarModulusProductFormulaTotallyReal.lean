import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasureRealValuedLeExp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeProdFormula

/- English proof (translation)
Take `⟨a, ha⟩` from `GlobalTheory.HaarLatticeScale.exists_valued_eq_exp F v (-1)`. Establish `ha1 : a ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `((GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp _).2 ha.le).le`. Establish `h` using `(GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 ⟨a, ha1⟩ 1 (by simpa using ha)`.

Establish `e : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {⟨a, ha1⟩}`. Use extensionality with `y`. Rewrite using `[GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v (by change Valued.v a ≠ 0; rw [ha]; exact WithZero.exp_ne_zero)]`. Express the relevant statement in the definitionally equal form `_ ↔ _ ≤ Valued.v a`. Rewrite using `[ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]`.

Conclude with `Valuation.mem_maximalIdeal_iff _ _`. Rewrite `h` using `[pow_one, ← e]`. Conclude with `h`.
-/
theorem card_residue (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  obtain ⟨a, ha⟩ := GlobalTheory.HaarLatticeScale.exists_valued_eq_exp F v (-1)
  have ha1 : a ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp _).2 ha.le).le
  have h := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 ⟨a, ha1⟩ 1
    (by simpa using ha)
  have e : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {⟨a, ha1⟩} := by
    ext y
    rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v
      (by change Valued.v a ≠ 0; rw [ha]; exact WithZero.exp_ne_zero)]
    change _ ↔ _ ≤ Valued.v a
    rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  rw [pow_one, ← e] at h
  exact h

/- English proof (translation)
Establish `hu : IsUnit x` using `hx.isUnit`. Establish `hv : Valued.v x ≠ 0` using `by simpa using hx`. Set `μ : Measure (Fv F v)` to `Measure.addHaar`. Establish `h` using `GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp F v (Fv F v) μ Unit (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm (WithZero.log (Valued.v x))`. Establish `hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isOpen_valuationSubring _`.

Establish `e0 : (v.adicCompletionIntegers F : Set (Fv F v)) = Metric.closedBall 0 1`. Use extensionality with `y`. Rewrite using `[mem_closedBall_zero_iff, Valued.toNormedField.norm_le_one_iff]`. Both sides reduce to the same expression. Establish `h0 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ 0` using `(hO.measure_pos μ ⟨0, zero_mem _⟩).ne'`.

Establish `h1 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ ∞`. Rewrite using `[e0]`. Conclude with `(isCompact_closedBall _ _).measure_lt_top.ne`. Establish `e1 : {y : Fv F v | ∀ i, Valued.v ((ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i) ≤ WithZero.exp (WithZero.log (Valued.v x))} = hu.unit • (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `y`.

Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, WithZero.exp_log hv, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, IsUnit.unit_spec, inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]`. Simplify using the standard rewrite rules. Establish `e2 : {y : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i ∈ v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `y`. Simplify using the standard rewrite rules.

Rewrite `h` using `[e1, e2, Measure.real, ← distribHaarChar_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, card_residue, Fintype.card_unit, pow_one]`. Establish `h2` using `mul_right_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h`. Rewrite using `[modu, dif_pos hu, h2, FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]`. Use `push_cast`. Use `congr 1`.

Use `conv_lhs => rw [← WithZero.coe_unzero hv]`. Both sides reduce to the same expression.
-/
theorem modu_finite (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v)
    (hx : x ≠ 0) : (modu (Fv F v) x : ℝ) = ‖x‖ := by
  have hu : IsUnit x := hx.isUnit
  have hv : Valued.v x ≠ 0 := by simpa using hx
  let μ : Measure (Fv F v) := Measure.addHaar
  have h := GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp F v (Fv F v) μ Unit
    (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm (WithZero.log (Valued.v x))
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have e0 : (v.adicCompletionIntegers F : Set (Fv F v)) = Metric.closedBall 0 1 := by
    ext y
    rw [mem_closedBall_zero_iff, Valued.toNormedField.norm_le_one_iff]
    rfl
  have h0 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
  have h1 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ ∞ := by
    rw [e0]; exact (isCompact_closedBall _ _).measure_lt_top.ne
  have e1 : {y : Fv F v | ∀ i, Valued.v ((ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i) ≤
      WithZero.exp (WithZero.log (Valued.v x))} = hu.unit • (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, WithZero.exp_log hv, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul,
      Units.val_inv_eq_inv_val, map_inv₀, IsUnit.unit_spec, inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
    simp
  have e2 : {y : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i ∈
      v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp
  rw [e1, e2, Measure.real, ← distribHaarChar_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, card_residue,
    Fintype.card_unit, pow_one] at h
  have h2 := mul_right_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h
  rw [modu, dif_pos hu, h2, FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  push_cast
  congr 1
  conv_lhs => rw [← WithZero.coe_unzero hv]
  rfl

/- English proof (translation)
Establish `hu : ∀ i, (u : ι → ℝ) i ≠ 0` using `fun i => ((Pi.isUnit_iff.1 u.isUnit) i).ne_zero`. Establish `hp : (volume : Measure (ι → ℝ)) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) = 1`. Rewrite using `[volume_pi_pi]`. Simplify using the standard rewrite rules. Establish `e : u • (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) = Set.univ.pi fun i => (u : ι → ℝ) i • Set.Icc (0 : ℝ) 1`.

Use extensionality with `y`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Simplify using `only [Set.mem_pi, Set.mem_univ, forall_true_left]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem₀ (hu i), Units.smul_def, smul_eq_mul, smul_eq_mul, Pi.mul_apply]`.

Establish `: ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i = ((u : ι → ℝ) i)⁻¹` using `eq_inv_of_mul_eq_one_left (congrFun u.inv_mul i)`. Rewrite using `[this]`. Rewrite using `[distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) (r := ∏ i, ‖(u : ι → ℝ) i‖₊) (by rw [hp]; simp) (by rw [hp]; simp)]`. Simplify using the standard rewrite rules. Rewrite using `[hp, e, volume_pi_pi, mul_one, ENNReal.ofNNReal_finsetProd]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Measure.addHaar_smul]`. Rewrite using `[Module.finrank_self, pow_one, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one, ← Real.enorm_eq_ofReal_abs]`. Both sides reduce to the same expression.
-/
theorem distribHaarChar_pi_real (ι : Type) [Fintype ι] (u : (ι → ℝ)ˣ) :
    (distribHaarChar (ι → ℝ) u : ℝ) = ∏ i, |(u : ι → ℝ) i| := by
  have hu : ∀ i, (u : ι → ℝ) i ≠ 0 := fun i => ((Pi.isUnit_iff.1 u.isUnit) i).ne_zero
  have hp : (volume : Measure (ι → ℝ)) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) = 1 := by
    rw [volume_pi_pi]; simp
  have e : u • (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) =
      Set.univ.pi fun i => (u : ι → ℝ) i • Set.Icc (0 : ℝ) 1 := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hu i), Units.smul_def, smul_eq_mul, smul_eq_mul, Pi.mul_apply]
    have : ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i = ((u : ι → ℝ) i)⁻¹ :=
      eq_inv_of_mul_eq_one_left (congrFun u.inv_mul i)
    rw [this]
  rw [distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume)
    (s := Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) (r := ∏ i, ‖(u : ι → ℝ) i‖₊) (by rw [hp]; simp) (by rw [hp]; simp)]
  · simp
  · rw [hp, e, volume_pi_pi, mul_one, ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Measure.addHaar_smul]
    rw [Module.finrank_self, pow_one, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one,
      ← Real.enorm_eq_ofReal_abs]
    rfl

/- English proof (translation)
Set `r : Ainf F ≃+* (InfinitePlace F → ℝ)` to `RingEquiv.piCongrRight fun w => InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)`. Set `e : Ainf F ≃ₜ+ (InfinitePlace F → ℝ)` to `{ r.toAddEquiv with continuous_toFun := continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w) continuous_invFun := continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTot …`. Establish `h` using `GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e hx.unit (Units.map (r : Ainf F →* (InfinitePlace F → ℝ)) hx.unit) (fun y => map_mul r x y)`. Rewrite using `[modu, dif_pos hx, ← h, distribHaarChar_pi_real]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[← Real.norm_eq_abs]`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero (map_zero _) (x w)`.
-/
theorem modu_infinite (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ainf F) (hx : IsUnit x) :
    (modu (Ainf F) x : ℝ) = ∏ w : InfinitePlace F, ‖x w‖ := by
  let r : Ainf F ≃+* (InfinitePlace F → ℝ) := RingEquiv.piCongrRight fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  let e : Ainf F ≃ₜ+ (InfinitePlace F → ℝ) :=
    { r.toAddEquiv with
      continuous_toFun := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
          (continuous_apply w)
      continuous_invFun := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous.comp
          (continuous_apply w) }
  have h := GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e hx.unit
    (Units.map (r : Ainf F →* (InfinitePlace F → ℝ)) hx.unit) (fun y => map_mul r x y)
  rw [modu, dif_pos hx, ← h, distribHaarChar_pi_real]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal w)).norm_map_of_map_zero (map_zero _) (x w)

/- English proof (translation)
Introduce `F _ _ _ e he`. Establish `hf : ∀ v : HeightOneSpectrum (𝓞 F), (modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ) = FinitePlace.equivHeightOneSpectrum.symm v e` using `fun v => by`. Rewrite using `[modu_finite F v _ ((map_ne_zero _).2 he)]`. Both sides reduce to the same expression. Establish `hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v) (algebraMap F (Fv F v) e)).Finite`.

Use `((FinitePlace.hasFiniteMulSupport he).preimage (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn).subset fun v hv h => hv ?_` and prove the remaining obligations. Apply `NNReal.coe_injective` to reduce the goal to its premises. Rewrite using `[hf]`. Conclude with `h`. Use `⟨hfin, NNReal.coe_injective ?_⟩` and prove the remaining obligations.

Establish `h1 : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ≥0) : ℝ) = ∏ᶠ w : FinitePlace F, w e`. Rewrite using `[← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]`. Simplify using `only [← hf]`. Conclude with `(NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.map_finprod hfin`. Rewrite using `[NNReal.coe_mul, h1, modu_infinite F _ (he.isUnit.map _), NNReal.coe_one, ← prod_abs_eq_one he]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[(IsTotallyReal.isReal w).mult_eq_one, pow_one]`. Conclude with `InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 e)`.
-/
theorem prod_modu_eq_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : F), e ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v) (algebraMap F (Fv F v) e)).Finite ∧ modu (Ainf F) (algebraMap F (Ainf F) e) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) = 1 := by
  intro F _ _ _ e he
  have hf : ∀ v : HeightOneSpectrum (𝓞 F), (modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ) =
      FinitePlace.equivHeightOneSpectrum.symm v e := fun v => by
    rw [modu_finite F v _ ((map_ne_zero _).2 he)]
    rfl
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      modu (Fv F v) (algebraMap F (Fv F v) e)).Finite := by
    refine ((FinitePlace.hasFiniteMulSupport he).preimage
      (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn).subset fun v hv h => hv ?_
    apply NNReal.coe_injective
    rw [hf]
    exact h
  refine ⟨hfin, NNReal.coe_injective ?_⟩
  have h1 : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ≥0) : ℝ) =
      ∏ᶠ w : FinitePlace F, w e := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [← hf]
    exact (NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.map_finprod hfin
  rw [NNReal.coe_mul, h1, modu_infinite F _ (he.isUnit.map _), NNReal.coe_one, ← prod_abs_eq_one he]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  exact InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 e)

end GlobalTheory.GaugeProdFormula

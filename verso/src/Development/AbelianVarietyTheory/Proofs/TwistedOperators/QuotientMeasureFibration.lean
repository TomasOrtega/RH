import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.Orb.FubiniQuot

/- English proof (translation)
Take `⟨b, hb, h1⟩` from `exists_bruhat hA ds`. Establish `hm : ∀ x, Measurable fun t : TA => b (t * x)` using `fun x => hb.comp (measurable_subtype_coe.mul_const _)`. Establish `hlt : ∀ x, ∀ᵐ t : TA ∂ds, b (t * x) < ∞` using `fun x => ae_lt_top (hm x) (by simp [h1])`. Use `⟨fun x => (b x).toNNReal, hb.ennreal_toNNReal, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← h1 x]`.

Conclude with `lintegral_congr_ae ((hlt x).mono fun t ht => ENNReal.coe_toNNReal ht.ne)`.
-/
theorem exists_bruhat_nnreal {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [SecondCountableTopology A] [LocallyCompactSpace A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    {TA : Subgroup A} (hA : IsClosed (TA : Set A)) (ds : Measure TA) [ds.IsHaarMeasure] [ds.IsMulRightInvariant] :
    ∃ b : A → ℝ≥0, Measurable b ∧ ∀ a, ∫⁻ s : TA, (b (s * a) : ℝ≥0∞) ∂ds = 1 := by
  obtain ⟨b, hb, h1⟩ := exists_bruhat hA ds
  have hm : ∀ x, Measurable fun t : TA => b (t * x) := fun x => hb.comp (measurable_subtype_coe.mul_const _)
  have hlt : ∀ x, ∀ᵐ t : TA ∂ds, b (t * x) < ∞ := fun x => ae_lt_top (hm x) (by simp [h1])
  refine ⟨fun x => (b x).toNNReal, hb.ennreal_toNNReal, fun x => ?_⟩
  rw [← h1 x]
  exact lintegral_congr_ae ((hlt x).mono fun t ht => ENNReal.coe_toNNReal ht.ne)

section Prod

variable {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [SecondCountableTopology A]
  [LocallyCompactSpace A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
  [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [SecondCountableTopology B]
  [LocallyCompactSpace B] [T2Space B] [MeasurableSpace B] [BorelSpace B]

/- English proof (translation)
Use `haveI : LocallyCompactSpace TA := hA.locallyCompactSpace`. Use `haveI : LocallyCompactSpace TB := hB.locallyCompactSpace`. Establish `hUc : IsClosed (U : Set (A × B))`. Rewrite using `[show (U : Set (A × B)) = (TA : Set A) ×ˢ (TB : Set B) from Set.ext hU]`. Conclude with `hA.prod hB`.

Use `set dt := (ds.prod dr).map (prodSub hU) with hdt`. Use `haveI : dt.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _`. Use `haveI : dt.IsMulRightInvariant := isMulRightInvariant_map (prodSub hU) _`. Take `⟨bA, mA, hA1⟩` from `exists_bruhat_nnreal hA ds`. Take `⟨bB, mB, hB1⟩` from `exists_bruhat_nnreal hB dr`.

Use `set β : A × B → ℝ≥0 := fun x => bA x.1 * bB x.2 with hβ`. Establish `mβ : Measurable β` using `(mA.comp measurable_fst).mul (mB.comp measurable_snd)`. Establish `hβ1 : ∀ x, ∫⁻ t : U, (β (t * x) : ℝ≥0∞) ∂dt = 1` using `fun x => by`. Rewrite using `[hdt, lintegral_map (f := fun t : U => (β (t * x) : ℝ≥0∞)) (mβ.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)) (map_continuous _).measurable]`. Use `show ∫⁻ p : TA × TB, ((bA (p.1 * x.1) * bB (p.2 * x.2) : ℝ≥0) : ℝ≥0∞) ∂(ds.prod dr) = 1`.

Simplify using `only [ENNReal.coe_mul]`. Rewrite using `[lintegral_prod_mul (f := fun s : TA => (bA (s * x.1) : ℝ≥0∞)) (g := fun s : TB => (bB (s * x.2) : ℝ≥0∞)) (mA.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)).aemeasurable (mB.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)).aemeasurable, hA1, hB1, one_m …`. Establish `hν` using `(isQuotMeasure_quotMeas dt (da.prod db) hUc).eq_map (b := fun x => (β x : ℝ≥0∞)) mβ.coe_nnreal_ennreal hβ1`. Establish `hq : quotInt U dt (da.prod db) φ = ∫ x, β x • φ x ∂(da.prod db)`. Rewrite using `[quotInt, hν, integral_map measurable_mk.aemeasurable (hν ▸ hint.1), ← integral_withDensity_eq_integral_smul mβ]`.

Simplify using `only [hi.descend_mk]`. Establish `hF : Integrable (fun x => β x • φ x) (da.prod db)`. Establish `h2` using `hint`. Rewrite `h2` using `[hν]`. Use `replace h2 := h2.comp_measurable measurable_mk`.

Rewrite `h2` using `[show descend U φ ∘ mk U = φ from hi.lift_descend, integrable_withDensity_iff_integrable_smul mβ]`. Then use the resulting hypothesis. Establish `hAr : ∀ a, ∫ s : TA, (bA (s * a) : ℝ) ∂ds = 1` using `fun a => by`. Establish `hm : Measurable fun s : TA => (bA (s * a) : ℝ≥0∞)` using `mA.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)`. Use `integral_toReal (μ := ds) hm.aemeasurable (.of_forall fun _ => ENNReal.coe_lt_top)` as an intermediate fact. Rewrite `this` using `[hA1 a, ENNReal.toReal_one]`.

Simplify `this` using `only [ENNReal.coe_toReal]`. Rewrite using `[hq, integral_prod_symm _ hF]`. Use `integral_eq_zero_of_ae ?_` and prove the remaining obligations. Use `filter_upwards [hF.prod_left_ae] with b hb`. Distinguish the cases in `hb0 : bB b = 0`.

Simplify using `[hβ, hb0]`. Establish `hG : Integrable (fun a => bA a • φ (a, b)) da`. Establish `hb0' : (bB b : ℝ) ≠ 0` using `by exact_mod_cast hb0`. Use `(hb.smul ((bB b : ℝ)⁻¹)).congr (.of_forall fun a => ?_)` and prove the remaining obligations. Simplify using `only [hβ, NNReal.smul_def, NNReal.coe_mul, smul_smul, Pi.smul_apply]`.

Rewrite using `[mul_comm (bA a : ℝ), ← mul_assoc, inv_mul_cancel₀ hb0', one_mul]`. Establish `hw` using `(weil_integral (dt := ds) hA hG).2`. Establish `e1 : (fun a => ∫ s : TA, bA (s * a) • φ ((s : A) * a, b) ∂ds) = fun a => φ (a, b)` using `funext fun a => by`. Establish `hs : ∀ s : TA, φ ((s : A) * a, b) = φ (a, b)` using `fun s => by`. Simplify `hi ((s : A), 1) ((hU _).2 ⟨s.2, TB.one_mem⟩) (a, b)` using `only [Prod.mk_mul_mk, one_mul]`.

Simplify using `only [hs, NNReal.smul_def]`. Rewrite using `[integral_smul_const, hAr a, one_smul]`. Rewrite `hw` using `[e1]`. Establish `e2 : ∫ a, β (a, b) • φ (a, b) ∂da = bB b • ∫ a, bA a • φ (a, b) ∂da`. Rewrite using `[NNReal.smul_def, ← integral_smul]`.

Use `integral_congr_ae (.of_forall fun a => ?_)` and prove the remaining obligations. Simplify using `only [hβ, NNReal.smul_def, NNReal.coe_mul, smul_smul, mul_comm]`. Use `show ∫ a, β (a, b) • φ (a, b) ∂da = 0`. Rewrite using `[e2, ← hw.2, h0 b, smul_zero]`.
-/
theorem quotInt_prod_eq_zero {TA : Subgroup A} {TB : Subgroup B} {U : Subgroup (A × B)}
    (hU : ∀ x, x ∈ U ↔ x.1 ∈ TA ∧ x.2 ∈ TB) (hA : IsClosed (TA : Set A)) (hB : IsClosed (TB : Set B))
    (da : Measure A) [da.IsHaarMeasure] (db : Measure B) [db.IsHaarMeasure]
    (ds : Measure TA) [ds.IsHaarMeasure] [ds.IsMulRightInvariant]
    (dr : Measure TB) [dr.IsHaarMeasure] [dr.IsMulRightInvariant]
    (φ : A × B → ℂ) (hi : LeftInv U φ)
    (hint : Integrable (descend U φ) (quotMeas U ((ds.prod dr).map (prodSub hU)) (da.prod db)))
    (h0 : ∀ b, quotInt TA ds da (fun a => φ (a, b)) = 0) :
    quotInt U ((ds.prod dr).map (prodSub hU)) (da.prod db) φ = 0 := by
  haveI : LocallyCompactSpace TA := hA.locallyCompactSpace
  haveI : LocallyCompactSpace TB := hB.locallyCompactSpace
  have hUc : IsClosed (U : Set (A × B)) := by
    rw [show (U : Set (A × B)) = (TA : Set A) ×ˢ (TB : Set B) from Set.ext hU]
    exact hA.prod hB
  set dt := (ds.prod dr).map (prodSub hU) with hdt
  haveI : dt.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  haveI : dt.IsMulRightInvariant := isMulRightInvariant_map (prodSub hU) _
  obtain ⟨bA, mA, hA1⟩ := exists_bruhat_nnreal hA ds
  obtain ⟨bB, mB, hB1⟩ := exists_bruhat_nnreal hB dr
  set β : A × B → ℝ≥0 := fun x => bA x.1 * bB x.2 with hβ
  have mβ : Measurable β := (mA.comp measurable_fst).mul (mB.comp measurable_snd)
  have hβ1 : ∀ x, ∫⁻ t : U, (β (t * x) : ℝ≥0∞) ∂dt = 1 := fun x => by
    rw [hdt, lintegral_map (f := fun t : U => (β (t * x) : ℝ≥0∞))
      (mβ.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)) (map_continuous _).measurable]
    show ∫⁻ p : TA × TB, ((bA (p.1 * x.1) * bB (p.2 * x.2) : ℝ≥0) : ℝ≥0∞) ∂(ds.prod dr) = 1
    simp only [ENNReal.coe_mul]
    rw [lintegral_prod_mul (f := fun s : TA => (bA (s * x.1) : ℝ≥0∞)) (g := fun s : TB => (bB (s * x.2) : ℝ≥0∞))
      (mA.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)).aemeasurable
      (mB.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)).aemeasurable, hA1, hB1, one_mul]
  have hν := (isQuotMeasure_quotMeas dt (da.prod db) hUc).eq_map (b := fun x => (β x : ℝ≥0∞))
    mβ.coe_nnreal_ennreal hβ1
  have hq : quotInt U dt (da.prod db) φ = ∫ x, β x • φ x ∂(da.prod db) := by
    rw [quotInt, hν, integral_map measurable_mk.aemeasurable (hν ▸ hint.1),
      ← integral_withDensity_eq_integral_smul mβ]
    simp only [hi.descend_mk]
  have hF : Integrable (fun x => β x • φ x) (da.prod db) := by
    have h2 := hint
    rw [hν] at h2
    replace h2 := h2.comp_measurable measurable_mk
    rwa [show descend U φ ∘ mk U = φ from hi.lift_descend, integrable_withDensity_iff_integrable_smul mβ] at h2
  have hAr : ∀ a, ∫ s : TA, (bA (s * a) : ℝ) ∂ds = 1 := fun a => by
    have hm : Measurable fun s : TA => (bA (s * a) : ℝ≥0∞) :=
      mA.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)
    have := integral_toReal (μ := ds) hm.aemeasurable (.of_forall fun _ => ENNReal.coe_lt_top)
    rw [hA1 a, ENNReal.toReal_one] at this
    simpa only [ENNReal.coe_toReal] using this
  rw [hq, integral_prod_symm _ hF]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hF.prod_left_ae] with b hb
  by_cases hb0 : bB b = 0
  · simp [hβ, hb0]
  have hG : Integrable (fun a => bA a • φ (a, b)) da := by
    have hb0' : (bB b : ℝ) ≠ 0 := by exact_mod_cast hb0
    refine (hb.smul ((bB b : ℝ)⁻¹)).congr (.of_forall fun a => ?_)
    simp only [hβ, NNReal.smul_def, NNReal.coe_mul, smul_smul, Pi.smul_apply]
    rw [mul_comm (bA a : ℝ), ← mul_assoc, inv_mul_cancel₀ hb0', one_mul]
  have hw := (weil_integral (dt := ds) hA hG).2
  have e1 : (fun a => ∫ s : TA, bA (s * a) • φ ((s : A) * a, b) ∂ds) = fun a => φ (a, b) := funext fun a => by
    have hs : ∀ s : TA, φ ((s : A) * a, b) = φ (a, b) := fun s => by
      simpa only [Prod.mk_mul_mk, one_mul] using hi ((s : A), 1) ((hU _).2 ⟨s.2, TB.one_mem⟩) (a, b)
    simp only [hs, NNReal.smul_def]
    rw [integral_smul_const, hAr a, one_smul]
  rw [e1] at hw
  have e2 : ∫ a, β (a, b) • φ (a, b) ∂da = bB b • ∫ a, bA a • φ (a, b) ∂da := by
    rw [NNReal.smul_def, ← integral_smul]
    refine integral_congr_ae (.of_forall fun a => ?_)
    simp only [hβ, NNReal.smul_def, NNReal.coe_mul, smul_smul, mul_comm]
  show ∫ a, β (a, b) • φ (a, b) ∂da = 0
  rw [e2, ← hw.2, h0 b, smul_zero]

end Prod

/- English proof (translation)
Set `U : Subgroup (A × B)` to `T.comap (e : A × B →* H)`. Establish `hU : ∀ x, x ∈ U ↔ x.1 ∈ TA ∧ x.2 ∈ TB` using `fun x => hmem x.1 x.2`. Establish `h' : ∀ x, e x ∈ T ↔ x ∈ U` using `fun x => Iff.rfl`. Establish `hA : IsClosed (TA : Set A)`. Establish `: (TA : Set A) = (fun a => e (a, 1)) ⁻¹' (T : Set H)` using `Set.ext fun a => by simp [hmem]`.

Rewrite using `[this]`. Conclude with `hT.preimage (by fun_prop)`. Establish `hB : IsClosed (TB : Set B)`. Establish `: (TB : Set B) = (fun b => e (1, b)) ⁻¹' (T : Set H)` using `Set.ext fun b => by simp [hmem]`. Rewrite using `[this]`.

Conclude with `hT.preimage (by fun_prop)`. Establish `hUc : IsClosed (U : Set (A × B))` using `hT.preimage e.continuous`. Use `haveI : LocallyCompactSpace TA := hA.locallyCompactSpace`. Use `haveI : LocallyCompactSpace TB := hB.locallyCompactSpace`. Use `haveI : LocallyCompactSpace T := hT.locallyCompactSpace`.

Establish `hc : ∀ x y : T, x * y = y * x` using `fun x y => hcomm.is_comm.comm x y`. Establish `hcA : ∀ s s' : TA, s * s' = s' * s` using `fun s s' => by`. Use `congrArg Subtype.val (hc ⟨e ((s : A), 1), (hmem _ _).2 ⟨s.2, TB.one_mem⟩⟩ ⟨e ((s' : A), 1), (hmem _ _).2 ⟨s'.2, TB.one_mem⟩⟩)` as an intermediate fact. Simplify using `only [Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one] at this`. Conclude with `Subtype.ext (congrArg Prod.fst (e.injective this))`.

Establish `hcB : ∀ s s' : TB, s * s' = s' * s` using `fun s s' => by`. Use `congrArg Subtype.val (hc ⟨e (1, (s : B)), (hmem _ _).2 ⟨TA.one_mem, s.2⟩⟩ ⟨e (1, (s' : B)), (hmem _ _).2 ⟨TA.one_mem, s'.2⟩⟩)` as an intermediate fact. Simplify using `only [Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one] at this`. Conclude with `Subtype.ext (congrArg Prod.snd (e.injective this))`. Use `haveI : ds.IsMulRightInvariant := ⟨fun g => by`.

Rewrite using `[show (fun x : TA => x * g) = (fun x => g * x) from funext fun x => hcA x g]`. Conclude with `map_mul_left_eq_self ds g⟩`. Set `dr : Measure TB` to `Measure.haar`. Use `haveI : dr.IsMulRightInvariant := ⟨fun g => by`. Rewrite using `[show (fun x : TB => x * g) = (fun x => g * x) from funext fun x => hcB x g]`.

Conclude with `map_mul_left_eq_self dr g⟩`. Use `haveI : dt.IsMulRightInvariant := ⟨fun g => by`. Rewrite using `[show (fun x : T => x * g) = (fun x => g * x) from funext fun x => hc x g]`. Conclude with `map_mul_left_eq_self dt g⟩`. Set `dtU : Measure U` to `(ds.prod dr).map (prodSub hU)`.

Use `haveI : dtU.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _`. Use `haveI : dtU.IsMulRightInvariant := isMulRightInvariant_map (prodSub hU) _`. Set `dt' : Measure T` to `dtU.map (subEquiv e h')`. Use `haveI : dt'.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _`. Use `haveI : dt'.IsMulRightInvariant := isMulRightInvariant_map (subEquiv e h') _`.

Set `db : Measure B` to `Measure.haar`. Set `dh' : Measure H` to `(da.prod db).map e`. Use `haveI : dh'.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _`. Establish `hiU : LeftInv U (φ ∘ e)` using `fun γ hγ g => by`. Simplify using `only [Function.comp, map_mul]`.

Conclude with `hi _ hγ _`. Establish `ht` using `hasQuotInt_map (e := e) (h := h') (hT := hUc) (dt := dtU) (dh := da.prod db) hi (quotInt T dt' dh' φ)`. Establish `hk : Measure.haarScalarFactor dt dt' ≠ 0` using `fun h => NeZero.ne dt (by`. Rewrite using `[Measure.isMulLeftInvariant_eq_smul dt dt', h, zero_smul])`. Establish `hc0 : Measure.haarScalarFactor dh dh' ≠ 0` using `fun h => NeZero.ne dh (by`.

Rewrite using `[Measure.isMulLeftInvariant_eq_smul dh dh', h, zero_smul])`. Take `⟨k, hk0, edt⟩ : ∃ k : ℝ≥0, k ≠ 0 ∧ dt = k • dt'` from `⟨_, hk, Measure.isMulLeftInvariant_eq_smul dt dt'⟩`. Take `⟨c, hc1, edh⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ dh = c • dh'` from `⟨_, hc0, Measure.isMulLeftInvariant_eq_smul dh dh'⟩`. Substitute `edt edh` using the available equality. Establish `e1 : quotMeas T (k • dt') (c • dh') = ((k⁻¹ * c : ℝ≥0) : ℝ≥0∞) • quotMeas T dt' dh'`.

Rewrite using `[quotMeas_smul_right hT hk0, show c • dh' = (c : ℝ≥0∞) • dh' from rfl, quotMeas_smul_left hT, show ∀ (r : ℝ≥0) (μ : Measure (Quot T)), r • μ = (r : ℝ≥0∞) • μ from fun _ _ => rfl, smul_smul, ENNReal.coe_mul]`. Establish `hr0 : ((k⁻¹ * c : ℝ≥0) : ℝ≥0∞) ≠ 0` using `by simp [hk0, hc1]`. Rewrite `hint` using `[e1]`. Establish `hint'` using `(integrable_smul_measure hr0 ENNReal.coe_ne_top).1 hint`. Establish `hI` using `(ht.1.1 ⟨hint', rfl⟩).1`.

Establish `h00` using `quotInt_prod_eq_zero hU hA hB da db ds dr (φ ∘ e) hiU hI h0`. Establish `hz : quotInt T dt' dh' φ = 0` using `ht.2.trans h00`. Rewrite using `[quotInt, e1, integral_smul_measure]`. Rewrite `hz` using `[quotInt]`. Rewrite using `[hz, smul_zero]`.
-/
theorem quotInt_eq_zero_of_fiber (A : Type) [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [SecondCountableTopology A] [LocallyCompactSpace A] [T2Space A] [MeasurableSpace A] [BorelSpace A] (B : Type)
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [SecondCountableTopology B] [LocallyCompactSpace B]
    [T2Space B] [MeasurableSpace B] [BorelSpace B] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (e : A × B ≃ₜ* H) (TA : Subgroup A) (TB : Subgroup B) (T : Subgroup H)
    (hmem : ∀ a b, e (a, b) ∈ T ↔ a ∈ TA ∧ b ∈ TB) (hT : IsClosed (T : Set H)) (hcomm : IsMulCommutative T)
    (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (da : Measure A) [da.IsHaarMeasure]
    (ds : Measure TA) [ds.IsHaarMeasure] (φ : H → ℂ) (hi : LeftInv T φ)
    (hint : Integrable (descend T φ) (quotMeas T dt dh))
    (h0 : ∀ b, quotInt TA ds da (fun a => φ (e (a, b))) = 0) : quotInt T dt dh φ = 0 := by
  let U : Subgroup (A × B) := T.comap (e : A × B →* H)
  have hU : ∀ x, x ∈ U ↔ x.1 ∈ TA ∧ x.2 ∈ TB := fun x => hmem x.1 x.2
  have h' : ∀ x, e x ∈ T ↔ x ∈ U := fun x => Iff.rfl
  have hA : IsClosed (TA : Set A) := by
    have : (TA : Set A) = (fun a => e (a, 1)) ⁻¹' (T : Set H) := Set.ext fun a => by simp [hmem]
    rw [this]
    exact hT.preimage (by fun_prop)
  have hB : IsClosed (TB : Set B) := by
    have : (TB : Set B) = (fun b => e (1, b)) ⁻¹' (T : Set H) := Set.ext fun b => by simp [hmem]
    rw [this]
    exact hT.preimage (by fun_prop)
  have hUc : IsClosed (U : Set (A × B)) := hT.preimage e.continuous
  haveI : LocallyCompactSpace TA := hA.locallyCompactSpace
  haveI : LocallyCompactSpace TB := hB.locallyCompactSpace
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  have hc : ∀ x y : T, x * y = y * x := fun x y => hcomm.is_comm.comm x y
  have hcA : ∀ s s' : TA, s * s' = s' * s := fun s s' => by
    have := congrArg Subtype.val (hc ⟨e ((s : A), 1), (hmem _ _).2 ⟨s.2, TB.one_mem⟩⟩
      ⟨e ((s' : A), 1), (hmem _ _).2 ⟨s'.2, TB.one_mem⟩⟩)
    simp only [Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one] at this
    exact Subtype.ext (congrArg Prod.fst (e.injective this))
  have hcB : ∀ s s' : TB, s * s' = s' * s := fun s s' => by
    have := congrArg Subtype.val (hc ⟨e (1, (s : B)), (hmem _ _).2 ⟨TA.one_mem, s.2⟩⟩
      ⟨e (1, (s' : B)), (hmem _ _).2 ⟨TA.one_mem, s'.2⟩⟩)
    simp only [Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one] at this
    exact Subtype.ext (congrArg Prod.snd (e.injective this))
  haveI : ds.IsMulRightInvariant := ⟨fun g => by
    rw [show (fun x : TA => x * g) = (fun x => g * x) from funext fun x => hcA x g]
    exact map_mul_left_eq_self ds g⟩
  let dr : Measure TB := Measure.haar
  haveI : dr.IsMulRightInvariant := ⟨fun g => by
    rw [show (fun x : TB => x * g) = (fun x => g * x) from funext fun x => hcB x g]
    exact map_mul_left_eq_self dr g⟩
  haveI : dt.IsMulRightInvariant := ⟨fun g => by
    rw [show (fun x : T => x * g) = (fun x => g * x) from funext fun x => hc x g]
    exact map_mul_left_eq_self dt g⟩
  let dtU : Measure U := (ds.prod dr).map (prodSub hU)
  haveI : dtU.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  haveI : dtU.IsMulRightInvariant := isMulRightInvariant_map (prodSub hU) _
  let dt' : Measure T := dtU.map (subEquiv e h')
  haveI : dt'.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  haveI : dt'.IsMulRightInvariant := isMulRightInvariant_map (subEquiv e h') _

  let db : Measure B := Measure.haar
  let dh' : Measure H := (da.prod db).map e
  haveI : dh'.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  have hiU : LeftInv U (φ ∘ e) := fun γ hγ g => by
    simp only [Function.comp, map_mul]
    exact hi _ hγ _
  have ht := hasQuotInt_map (e := e) (h := h') (hT := hUc) (dt := dtU) (dh := da.prod db) hi
    (quotInt T dt' dh' φ)
  have hk : Measure.haarScalarFactor dt dt' ≠ 0 := fun h => NeZero.ne dt (by
    rw [Measure.isMulLeftInvariant_eq_smul dt dt', h, zero_smul])
  have hc0 : Measure.haarScalarFactor dh dh' ≠ 0 := fun h => NeZero.ne dh (by
    rw [Measure.isMulLeftInvariant_eq_smul dh dh', h, zero_smul])
  obtain ⟨k, hk0, edt⟩ : ∃ k : ℝ≥0, k ≠ 0 ∧ dt = k • dt' := ⟨_, hk, Measure.isMulLeftInvariant_eq_smul dt dt'⟩
  obtain ⟨c, hc1, edh⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ dh = c • dh' := ⟨_, hc0, Measure.isMulLeftInvariant_eq_smul dh dh'⟩
  subst edt edh
  have e1 : quotMeas T (k • dt') (c • dh') = ((k⁻¹ * c : ℝ≥0) : ℝ≥0∞) • quotMeas T dt' dh' := by
    rw [quotMeas_smul_right hT hk0, show c • dh' = (c : ℝ≥0∞) • dh' from rfl, quotMeas_smul_left hT,
      show ∀ (r : ℝ≥0) (μ : Measure (Quot T)), r • μ = (r : ℝ≥0∞) • μ from fun _ _ => rfl, smul_smul,
      ENNReal.coe_mul]
  have hr0 : ((k⁻¹ * c : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simp [hk0, hc1]
  rw [e1] at hint
  have hint' := (integrable_smul_measure hr0 ENNReal.coe_ne_top).1 hint
  have hI := (ht.1.1 ⟨hint', rfl⟩).1
  have h00 := quotInt_prod_eq_zero hU hA hB da db ds dr (φ ∘ e) hiU hI h0
  have hz : quotInt T dt' dh' φ = 0 := ht.2.trans h00
  rw [quotInt, e1, integral_smul_measure]
  rw [quotInt] at hz
  rw [hz, smul_zero]

end GlobalTheory.Orb.FubiniQuot

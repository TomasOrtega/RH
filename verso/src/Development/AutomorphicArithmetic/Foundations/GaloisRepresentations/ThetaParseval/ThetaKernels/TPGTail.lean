import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.IntOfOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDecomp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBadA

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
/- English proof (translation)
Set `μD : Measure D` to `Measure.haar`. Set `T : Set D` to `{d | j (d, 1) ∈ U}`. Establish `cj : Continuous fun d : D => j (d, 1)` using `j.continuous.comp (by fun_prop)`. Establish `oT : IsOpen T` using `hU.preimage cj`. Establish `m1 : (1 : D) ∈ T` using `by show j ((1 : D), (1 : C)) ∈ U`.

Rewrite using `[show ((1 : D), (1 : C)) = 1 from rfl, map_one]`. Conclude with `h1`. Establish `t0 : μD T ≠ 0` using `(oT.measure_pos μD ⟨1, m1⟩).ne'`. Establish `tt : μD T ≠ ⊤`. Establish `cpt : IsCompact (Prod.fst '' (j.symm '' U))` using `(hUc.image j.symm.continuous).image continuous_fst`.

Use `((measure_mono ?_).trans_lt cpt.measure_lt_top).ne` and prove the remaining obligations. Introduce `d hd`. Conclude with `⟨(d, 1), ⟨j (d, 1), hd, j.symm_apply_apply _⟩, rfl⟩`. Set `P : Measure (D × C)` to `μD.prod μC`. Establish `me : MeasurableEmbedding j` using `j.toHomeomorph.measurableEmbedding`.

Establish `hH : (P.map j).IsHaarMeasure` using `j.toMulEquiv.isHaarMeasure_map P j.continuous j.symm.continuous`. Establish `hν : P.map j = Measure.haarScalarFactor (P.map j) μ • μ` using `Measure.isMulLeftInvariant_eq_smul (P.map j) μ`. Establish `k0 : Measure.haarScalarFactor (P.map j) μ ≠ 0` using `(Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'`. Establish `a1 : μD T * ∫⁻ c in Kᶜ, F c ∂μC = ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P`. Rewrite using `[← Measure.prod_restrict, lintegral_prod (fun y : D × C => F y.2) (hF.comp measurable_snd).aemeasurable]`.

Simplify using `[lintegral_const, mul_comm]`. Establish `a2 : ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P ≤ ∫⁻ g in W, f g ∂(P.map j)`. Rewrite using `[me.restrict_map, me.lintegral_map]`. Combine the equalities or inequalities in the displayed calculation. Establish `a3 : (P.map j) U ≤ μD T * μC K`.

Rewrite using `[me.map_apply, ← Measure.prod_prod]`. Conclude with `measure_mono fun y hy => hc y.1 y.2 hy`. Establish `a4 : ∫⁻ g in W, f g ∂(P.map j) < (P.map j) U`. Rewrite using `[hν, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply]`. Establish `hk : ((Measure.haarScalarFactor (P.map j) μ : ℝ≥0) : ENNReal) ≠ 0` using `by exact_mod_cast k0`.

Simplify using `only [ENNReal.smul_def, smul_eq_mul]`. Conclude with `(ENNReal.mul_lt_mul_iff_right hk ENNReal.coe_ne_top).2 hlt`. Use `(a1.le.trans a2).trans_lt (a4.trans_le a3)` as an intermediate fact. Conclude with `(ENNReal.mul_lt_mul_iff_right t0 tt).1 this`.
-/
private theorem abs_tail_pk {G D C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [MeasurableSpace D] [BorelSpace D]
    [LocallyCompactSpace D] [SecondCountableTopology D]
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [MeasurableSpace C] [BorelSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    (j : D × C ≃ₜ* G) (μ : Measure G) [μ.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure]
    {U W : Set G} {K : Set C} (hU : IsOpen U) (hUc : IsCompact U) (h1 : (1 : G) ∈ U)
    (hK : MeasurableSet K) (f : G → ENNReal) (F : C → ENNReal) (hF : Measurable F)
    (hc : ∀ d c, j (d, c) ∈ U → j (d, 1) ∈ U ∧ c ∈ K)
    (hm : ∀ d c, j (d, 1) ∈ U → c ∉ K → j (d, c) ∈ W ∧ f (j (d, c)) = F c)
    (hlt : ∫⁻ g in W, f g ∂μ < μ U) : ∫⁻ c in Kᶜ, F c ∂μC < μC K := by
  let μD : Measure D := Measure.haar
  let T : Set D := {d | j (d, 1) ∈ U}
  have cj : Continuous fun d : D => j (d, 1) := j.continuous.comp (by fun_prop)
  have oT : IsOpen T := hU.preimage cj
  have m1 : (1 : D) ∈ T := by
    show j ((1 : D), (1 : C)) ∈ U
    rw [show ((1 : D), (1 : C)) = 1 from rfl, map_one]; exact h1
  have t0 : μD T ≠ 0 := (oT.measure_pos μD ⟨1, m1⟩).ne'
  have tt : μD T ≠ ⊤ := by
    have cpt : IsCompact (Prod.fst '' (j.symm '' U)) := (hUc.image j.symm.continuous).image continuous_fst
    refine ((measure_mono ?_).trans_lt cpt.measure_lt_top).ne
    intro d hd
    exact ⟨(d, 1), ⟨j (d, 1), hd, j.symm_apply_apply _⟩, rfl⟩
  let P : Measure (D × C) := μD.prod μC
  have me : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  have hH : (P.map j).IsHaarMeasure := j.toMulEquiv.isHaarMeasure_map P j.continuous j.symm.continuous
  have hν : P.map j = Measure.haarScalarFactor (P.map j) μ • μ := Measure.isMulLeftInvariant_eq_smul (P.map j) μ
  have k0 : Measure.haarScalarFactor (P.map j) μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have a1 : μD T * ∫⁻ c in Kᶜ, F c ∂μC = ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P := by
    rw [← Measure.prod_restrict, lintegral_prod (fun y : D × C => F y.2) (hF.comp measurable_snd).aemeasurable]
    simp [lintegral_const, mul_comm]
  have a2 : ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P ≤ ∫⁻ g in W, f g ∂(P.map j) := by
    rw [me.restrict_map, me.lintegral_map]
    calc _ = ∫⁻ y in T ×ˢ Kᶜ, f (j y) ∂P :=
          setLIntegral_congr_fun (oT.measurableSet.prod hK.compl) fun y hy => (hm y.1 y.2 hy.1 hy.2).2.symm
      _ ≤ _ := lintegral_mono_set fun y hy => (hm _ _ hy.1 hy.2).1
  have a3 : (P.map j) U ≤ μD T * μC K := by
    rw [me.map_apply, ← Measure.prod_prod]
    exact measure_mono fun y hy => hc y.1 y.2 hy
  have a4 : ∫⁻ g in W, f g ∂(P.map j) < (P.map j) U := by
    rw [hν, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply]
    have hk : ((Measure.haarScalarFactor (P.map j) μ : ℝ≥0) : ENNReal) ≠ 0 := by exact_mod_cast k0
    simp only [ENNReal.smul_def, smul_eq_mul]
    exact (ENNReal.mul_lt_mul_iff_right hk ENNReal.coe_ne_top).2 hlt
  have := (a1.le.trans a2).trans_lt (a4.trans_le a3)
  exact (ENNReal.mul_lt_mul_iff_right t0 tt).1 this
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n} {v : Pl F}
/- English proof (translation)
Establish `h : PositivityTheory.ThKG.Loc.idem F v • (mat g - 1) = 0` using `Matrix.ext fun i j => Bad.idem_off (by`. Use `congrFun₂ hg i j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply]`. Simplify using `[this, Matrix.one_apply, apply_ite (compFin F E v)])`. Establish `e : (mat g - 1) *ᵥ z = 0`.

Rewrite using `[← Bad.idem_smul hz, Matrix.mulVec_smul, ← Matrix.smul_mulVec, h, Matrix.zero_mulVec]`. Rewrite `e` using `[Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]`. Conclude with `e`.
-/
private theorem fix_off_pk {g : UA σ X.J} (hg : OffAt v g) {z : Fin n → AE F E} (hz : At (evFin F v) z) : mat g *ᵥ z = z := by
  have h : PositivityTheory.ThKG.Loc.idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => Bad.idem_off (by
    have := congrFun₂ hg i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
  have e : (mat g - 1) *ᵥ z = 0 := by
    rw [← Bad.idem_smul hz, Matrix.mulVec_smul, ← Matrix.smul_mulVec, h, Matrix.zero_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at e
  exact e
/- English proof (translation)
Introduce `z hz h` and use `by have e := fix_off_pk hg h have e' : mat g⁻¹ *ᵥ z = z := by conv_lhs => rw [← e] rw [Matrix.mulVec_mulVec, ← Euler.mm, inv_mul_cancel] exact Matrix.one_mulVec z exact ⟨e.symm ▸ hz, e'.symm ▸ hz⟩`.
-/
private theorem int_of_off_pk {g : UA σ X.J} (hg : OffAt v g) : IntAt v g := fun z hz h => by
  have e := fix_off_pk hg h
  have e' : mat g⁻¹ *ᵥ z = z := by
    conv_lhs => rw [← e]
    rw [Matrix.mulVec_mulVec, ← Euler.mm, inv_mul_cancel]
    exact Matrix.one_mulVec z
  exact ⟨e.symm ▸ hz, e'.symm ▸ hz⟩
/- English proof (translation)
The claim follows from `(Subgroup.closure_le (Euler.intGrp σ X v)).2 (fun _ hg => int_of_off_pk (hg.2 v hv)) hc`.
-/
private theorem int_gOff_pk {S : Finset (Pl F)} {c : UA σ X.J} (hc : c ∈ gOff σ X S) (hv : v ∈ S) : IntAt v c :=
  (Subgroup.closure_le (Euler.intGrp σ X v)).2 (fun _ hg => int_of_off_pk (hg.2 v hv)) hc
/- English proof (translation)
Establish `: gAt σ X S ≤ Euler.intGrp σ X v` using `iSup₂_le fun w hw x hx => by`. Establish `hvw : v ≠ w` using `fun e => hv (e ▸ hw)`. Use `(Euler.int_mul_ne hvw hx 1).2 (Euler.intGrp σ X v).one_mem` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis. Conclude with `this hb`.
-/
private theorem int_gAt_pk {S : Finset (Pl F)} {b : UA σ X.J} (hb : b ∈ gAt σ X S) (hv : v ∉ S) : IntAt v b := by
  have : gAt σ X S ≤ Euler.intGrp σ X v := iSup₂_le fun w hw x hx => by
    have hvw : v ≠ w := fun e => hv (e ▸ hw)
    have := (Euler.int_mul_ne hvw hx 1).2 (Euler.intGrp σ X v).one_mem
    rwa [mul_one] at this
  exact this hb
/- English proof (translation)
Take `⟨p, t, hp, k', hk', rfl⟩` from `ha.iwa x`. Rewrite using `[mul_assoc, ha.val p t hp _ (K.mul_mem hk' hk), ha.val p t hp k' hk']`.
-/
private theorem hgt_right_pk {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a) (x : G2 σ X) {k : G2 σ X} (hk : k ∈ K) :
    a (x * k) = a x := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa x
  rw [mul_assoc, ha.val p t hp _ (K.mul_mem hk' hk), ha.val p t hp k' hk']
end
end UpperTheory.TP
open UpperTheory.TP in
/- English proof (translation)
Introduce `T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he μ t hμ hi S₀`. Use `GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F` as an intermediate fact. Take `⟨a1, a2, a3⟩` from `Euler.lcsc_UA σ X.J`. Establish `hL` using `hX.lat`. Establish `dec` using `_root_.UpperTheory.TP.decomp_k T F E σ B n X hB hX`.

Set `U : Set (UA σ X.J)` to `{g | IntAll g}`. Establish `Um : ∀ {x y : UA σ X.J}, IntAll x → IntAll y → IntAll (x * y)` using `fun hx hy v => (Euler.intGrp σ X v).mul_mem (hx v) (hy v)`. Establish `Ui : ∀ {x : UA σ X.J}, IntAll x → IntAll x⁻¹` using `fun hx v => (Euler.intGrp σ X v).inv_mem (hx v)`. Establish `U1 : IntAll (1 : UA σ X.J)` using `fun v => (Euler.intGrp σ X v).one_mem`. Take `⟨-, -, -, -, cU, oU, -, -, -⟩` from `dec ∅`.

Establish `hr : ∀ g u : UA σ X.J, IntAll u → a (e (g * u, 1)) = a (e (g, 1))` using `fun g u hu => by`. Establish `: e (g * u, 1) = e (g, 1) * e (u, 1)` using `by rw [← map_mul, Prod.mk_mul_mk, mul_one]`. Rewrite using `[this, hgt_right_pk ha _ (_root_.GlobalTheory.ThK.Dbl.Bad.emb_mem_k hB hX (by simp) hK he hu)]`. Establish `lc : IsLocallyConstant fun g : UA σ X.J => a (e (g, 1))` using `(IsLocallyConstant.iff_exists_open _).2 fun g => ⟨{x | g⁻¹ * x ∈ U}, oU.preimage (by fun_prop), by show g⁻¹ * g ∈ U; rw [inv_mul_cancel]; exact U1, fun x hx => by`. Use `hr g _ hx` as an intermediate fact.

Rewrite using `[mul_inv_cancel_left] at this⟩` and apply the resulting hypothesis. Set `f : UA σ X.J → ENNReal` to `fun g => ENNReal.ofReal (a (e (g, 1)) ^ t)`. Establish `cf : Continuous f` using `(lc.comp fun r => ENNReal.ofReal (r ^ t)).continuous`. Set `m : Measure (UA σ X.J)` to `μ.withDensity f`. Establish `mfin : m Set.univ ≠ ⊤`.

Rewrite using `[withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]`. Conclude with `hi.lintegral_lt_top.ne`. Set `A : Finset (Pl F) → Set (UA σ X.J)` to `fun S => {g | ∀ v ∈ S, IntAt v g} \ U`. Establish `mA : ∀ S, MeasurableSet (A S)` using `fun S => by`. Use `MeasurableSet.diff ?_ oU.measurableSet` and prove the remaining obligations.

Simplify using `only [Set.setOf_forall]`. Conclude with `(isClosed_iInter fun u => isClosed_iInter fun _ => Euler.isClosed_int hL u).measurableSet`. Establish `anti : Antitone A` using `fun S S' hS g hg => ⟨fun v hv => hg.1 v (hS hv), hg.2⟩`. Establish `emp : ⋂ S, A S = ∅`. Use `Set.eq_empty_of_forall_notMem fun g hg => ?_` and prove the remaining obligations.

Establish `hg'` using `Set.mem_iInter.1 hg`. Conclude with `(hg' ∅).2 fun v => (hg' {v}).1 v (Finset.mem_singleton_self v)`. Establish `ten` using `tendsto_measure_iInter_atTop (μ := m) (fun S => (mA S).nullMeasurableSet) anti ⟨∅, ne_top_of_le_ne_top mfin (measure_mono (Set.subset_univ _))⟩`. Rewrite `ten` using `[emp, measure_empty]`. Establish `pos : 0 < μ U` using `oU.measure_pos μ ⟨1, U1⟩`.

Take `⟨S, hlt, hS⟩` from `((ten.eventually (gt_mem_nhds pos)).and (eventually_ge_atTop S₀)).exists`. Use `⟨S, hS, fun μC hC => ?_⟩` and prove the remaining obligations. Take `⟨⟨j, hj⟩, cI, cA, cO, -, -, iI, -, -⟩` from `dec S`. Establish `: LocallyCompactSpace (gInf σ X)` using `cI.isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: LocallyCompactSpace (gAt σ X S)` using `cA.isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Establish `: LocallyCompactSpace (gOff σ X S)` using `cO.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: SecondCountableTopology (gInf σ X)` using `IsEmbedding.subtypeVal.secondCountableTopology`. Establish `: SecondCountableTopology (gAt σ X S)` using `IsEmbedding.subtypeVal.secondCountableTopology`. Establish `: SecondCountableTopology (gOff σ X S)` using `IsEmbedding.subtypeVal.secondCountableTopology`. Set `j' : (gInf σ X × gAt σ X S) × gOff σ X S ≃ₜ* UA σ X.J` to `{ toMulEquiv := MulEquiv.prodAssoc.trans j.toMulEquiv continuous_toFun := j.continuous.comp ((continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd)) continuous_invFun := by`.

Use `j.symm.continuous` as an intermediate fact. Conclude with `((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)).comp this }`. Establish `hj' : ∀ d c, j' (d, c) = d.1.1 * d.2.1 * c.1` using `fun d c => hj (d.1, d.2, c)`. Establish `hj1 : ∀ d, j' (d, 1) = d.1.1 * d.2.1` using `fun d => by rw [hj']; simp`. Establish `hcm : ∀ d c, j' (d, c) = c.1 * (d.1.1 * d.2.1)` using `fun d c => by`.

Use `map_mul j' ((1 : gInf σ X × gAt σ X S), c) (d, (1 : gOff σ X S))` as an intermediate fact. Rewrite `this` using `[Prod.mk_mul_mk, one_mul, mul_one, hj1]`. Rewrite using `[this, hj']`. Simplify using the standard rewrite rules. Establish `res` using `abs_tail_pk j' μ μC (U := U) (W := A S) (K := {c | IntAll c.1}) oU cU U1 (oU.preimage continuous_subtype_val).measurableSet f (fun c => f c.1) (cf.measurable.comp measurable_subtype_coe) (fun d c hg => by`.

Establish `hx : IntAll d.1.1` using `iI _ d.1.2`. Establish `hg' : IntAll (d.1.1 * d.2.1 * c.1)` using `hj' d c ▸ hg`. Establish `hb : IntAll d.2.1` using `fun v => by`. Distinguish the cases in `hv : v ∈ S`. Establish `e1 : d.2.1 = d.1.1⁻¹ * (d.1.1 * d.2.1 * c.1) * c.1⁻¹` using `by group`.

Rewrite using `[e1]`. Conclude with `(Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).inv_mem (hx v)) (hg' v)) ((Euler.intGrp σ X v).inv_mem (int_gOff_pk c.2 hv))`. Conclude with `int_gAt_pk d.2.2 hv`. Establish `hxb` using `Um hx hb`. Use `⟨by rw [hj1]; exact hxb, ?_⟩` and prove the remaining obligations.

Use `show IntAll c.1`. Establish `e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1)` using `by group`. Rewrite using `[e2]`. Conclude with `Um (Ui hxb) hg')`. Use the proof step `(fun d c hd hcK => by`.

Establish `hd' : IntAll (d.1.1 * d.2.1)` using `hj1 d ▸ hd`. Use `⟨⟨fun v hv => ?_, fun hg => hcK ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hj']`. Conclude with `(Euler.intGrp σ X v).mul_mem (hd' v) (int_gOff_pk c.2 hv)`. Establish `hg' : IntAll (d.1.1 * d.2.1 * c.1)` using `hj' d c ▸ hg show IntAll c.1`.

Establish `e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1)` using `by group`. Rewrite using `[e2]`. Conclude with `Um (Ui hd') hg'`. Use `show ENNReal.ofReal (a (e (j' (d, c), 1)) ^ t) = ENNReal.ofReal (a (e (c.1, 1)) ^ t)`. Rewrite using `[hcm, hr _ _ hd'])`.

Use the proof step `(by`. Rewrite using `[← withDensity_apply _ (mA S)]`. Conclude with `hlt)`. Conclude with `res`.
-/
theorem UpperTheory.TP.tail_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Tail_k := by
  intro T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he μ t hμ hi S₀
  classical
  have := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨a1, a2, a3⟩ := Euler.lcsc_UA σ X.J
  have hL := hX.lat
  have dec := _root_.UpperTheory.TP.decomp_k T F E σ B n X hB hX
  let U : Set (UA σ X.J) := {g | IntAll g}
  have Um : ∀ {x y : UA σ X.J}, IntAll x → IntAll y → IntAll (x * y) := fun hx hy v => (Euler.intGrp σ X v).mul_mem (hx v) (hy v)
  have Ui : ∀ {x : UA σ X.J}, IntAll x → IntAll x⁻¹ := fun hx v => (Euler.intGrp σ X v).inv_mem (hx v)
  have U1 : IntAll (1 : UA σ X.J) := fun v => (Euler.intGrp σ X v).one_mem
  obtain ⟨-, -, -, -, cU, oU, -, -, -⟩ := dec ∅
  have hr : ∀ g u : UA σ X.J, IntAll u → a (e (g * u, 1)) = a (e (g, 1)) := fun g u hu => by
    have : e (g * u, 1) = e (g, 1) * e (u, 1) := by rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rw [this, hgt_right_pk ha _ (_root_.GlobalTheory.ThK.Dbl.Bad.emb_mem_k hB hX (by simp) hK he hu)]
  have lc : IsLocallyConstant fun g : UA σ X.J => a (e (g, 1)) := (IsLocallyConstant.iff_exists_open _).2 fun g =>
    ⟨{x | g⁻¹ * x ∈ U}, oU.preimage (by fun_prop), by show g⁻¹ * g ∈ U; rw [inv_mul_cancel]; exact U1, fun x hx => by
      have := hr g _ hx
      rwa [mul_inv_cancel_left] at this⟩
  let f : UA σ X.J → ENNReal := fun g => ENNReal.ofReal (a (e (g, 1)) ^ t)
  have cf : Continuous f := (lc.comp fun r => ENNReal.ofReal (r ^ t)).continuous
  let m : Measure (UA σ X.J) := μ.withDensity f
  have mfin : m Set.univ ≠ ⊤ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hi.lintegral_lt_top.ne
  let A : Finset (Pl F) → Set (UA σ X.J) := fun S => {g | ∀ v ∈ S, IntAt v g} \ U
  have mA : ∀ S, MeasurableSet (A S) := fun S => by
    refine MeasurableSet.diff ?_ oU.measurableSet
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => Euler.isClosed_int hL u).measurableSet
  have anti : Antitone A := fun S S' hS g hg => ⟨fun v hv => hg.1 v (hS hv), hg.2⟩
  have emp : ⋂ S, A S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    have hg' := Set.mem_iInter.1 hg
    exact (hg' ∅).2 fun v => (hg' {v}).1 v (Finset.mem_singleton_self v)
  have ten := tendsto_measure_iInter_atTop (μ := m) (fun S => (mA S).nullMeasurableSet) anti
    ⟨∅, ne_top_of_le_ne_top mfin (measure_mono (Set.subset_univ _))⟩
  rw [emp, measure_empty] at ten
  have pos : 0 < μ U := oU.measure_pos μ ⟨1, U1⟩
  obtain ⟨S, hlt, hS⟩ := ((ten.eventually (gt_mem_nhds pos)).and (eventually_ge_atTop S₀)).exists
  refine ⟨S, hS, fun μC hC => ?_⟩
  obtain ⟨⟨j, hj⟩, cI, cA, cO, -, -, iI, -, -⟩ := dec S
  have : LocallyCompactSpace (gInf σ X) := cI.isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (gAt σ X S) := cA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (gOff σ X S) := cO.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (gInf σ X) := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (gAt σ X S) := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (gOff σ X S) := IsEmbedding.subtypeVal.secondCountableTopology
  let j' : (gInf σ X × gAt σ X S) × gOff σ X S ≃ₜ* UA σ X.J :=
    { toMulEquiv := MulEquiv.prodAssoc.trans j.toMulEquiv
      continuous_toFun := j.continuous.comp ((continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      continuous_invFun := by
        have := j.symm.continuous
        exact ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)).comp this }
  have hj' : ∀ d c, j' (d, c) = d.1.1 * d.2.1 * c.1 := fun d c => hj (d.1, d.2, c)
  have hj1 : ∀ d, j' (d, 1) = d.1.1 * d.2.1 := fun d => by rw [hj']; simp
  have hcm : ∀ d c, j' (d, c) = c.1 * (d.1.1 * d.2.1) := fun d c => by
    have := map_mul j' ((1 : gInf σ X × gAt σ X S), c) (d, (1 : gOff σ X S))
    rw [Prod.mk_mul_mk, one_mul, mul_one, hj1] at this
    rw [this, hj']
    simp
  have res := abs_tail_pk j' μ μC (U := U) (W := A S) (K := {c | IntAll c.1}) oU cU U1
    (oU.preimage continuous_subtype_val).measurableSet f (fun c => f c.1) (cf.measurable.comp measurable_subtype_coe)
    (fun d c hg => by
      have hx : IntAll d.1.1 := iI _ d.1.2
      have hg' : IntAll (d.1.1 * d.2.1 * c.1) := hj' d c ▸ hg
      have hb : IntAll d.2.1 := fun v => by
        by_cases hv : v ∈ S
        · have e1 : d.2.1 = d.1.1⁻¹ * (d.1.1 * d.2.1 * c.1) * c.1⁻¹ := by group
          rw [e1]
          exact (Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).inv_mem (hx v)) (hg' v))
            ((Euler.intGrp σ X v).inv_mem (int_gOff_pk c.2 hv))
        · exact int_gAt_pk d.2.2 hv
      have hxb := Um hx hb
      refine ⟨by rw [hj1]; exact hxb, ?_⟩
      show IntAll c.1
      have e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1) := by group
      rw [e2]
      exact Um (Ui hxb) hg')
    (fun d c hd hcK => by
      have hd' : IntAll (d.1.1 * d.2.1) := hj1 d ▸ hd
      refine ⟨⟨fun v hv => ?_, fun hg => hcK ?_⟩, ?_⟩
      · rw [hj']
        exact (Euler.intGrp σ X v).mul_mem (hd' v) (int_gOff_pk c.2 hv)
      · have hg' : IntAll (d.1.1 * d.2.1 * c.1) := hj' d c ▸ hg
        show IntAll c.1
        have e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1) := by group
        rw [e2]
        exact Um (Ui hd') hg'
      · show ENNReal.ofReal (a (e (j' (d, c), 1)) ^ t) = ENNReal.ofReal (a (e (c.1, 1)) ^ t)
        rw [hcm, hr _ _ hd'])
    (by
      rw [← withDensity_apply _ (mA S)]
      exact hlt)
  exact res
end
end

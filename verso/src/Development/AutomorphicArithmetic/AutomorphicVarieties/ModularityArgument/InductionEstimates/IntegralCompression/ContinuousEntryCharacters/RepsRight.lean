import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Establish `h : (fun k => F (s k)) = fun k => ∑ x ∈ s.range, (s ⁻¹' {x}).indicator (fun _ => F x) k`. Use function extensionality and compare the values at `k`. Rewrite using `[Finset.sum_eq_single (s k)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Conclude with `Set.indicator_of_notMem (by simpa using fun h => hb h.symm) _`. Introduce `h`. Conclude with `absurd (s.mem_range_self k) h`. Rewrite using `[h, integral_finset_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_indicator_const _ (s.measurableSet_preimage _)]`. Introduce `x _`. Conclude with `(integrable_const (F x)).indicator (s.measurableSet_preimage _)`.
-/
private theorem simp_int {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (ν : Measure X) [IsFiniteMeasure ν]
    (s : SimpleFunc X X) (F : X → E) : ∫ k, F (s k) ∂ν = ∑ x ∈ s.range, ν.real (s ⁻¹' {x}) • F x := by
  have h : (fun k => F (s k)) = fun k => ∑ x ∈ s.range, (s ⁻¹' {x}).indicator (fun _ => F x) k := by
    funext k
    rw [Finset.sum_eq_single (s k)]
    · simp
    · intro b _ hb
      exact Set.indicator_of_notMem (by simpa using fun h => hb h.symm) _
    · intro h
      exact absurd (s.mem_range_self k) h
  rw [h, integral_finset_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_indicator_const _ (s.measurableSet_preimage _)]
  · intro x _
    exact (integrable_const (F x)).indicator (s.measurableSet_preimage _)

/- English proof (translation)
Take `⟨C, hC⟩` from `(isCompact_range hG).isBounded.exists_norm_le`. Use `tendsto_integral_of_dominated_convergence (fun _ => C) (fun i => ?_) (integrable_const C) (fun i => Eventually.of_forall fun k => hC _ ⟨_, rfl⟩) (Eventually.of_forall fun k => (hG.tendsto k).comp (hs k))` and prove the remaining obligations. Conclude with `((s i).map G).aestronglyMeasurable`.
-/
private theorem simp_lim {X E : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure X) [IsFiniteMeasure ν] (s : ℕ → SimpleFunc X X) (hs : ∀ k, Tendsto (fun i => s i k) atTop (𝓝 k)) (G : X → E) (hG : Continuous G) :
    Tendsto (fun i => ∫ k, G (s i k) ∂ν) atTop (𝓝 (∫ k, G k ∂ν)) := by
  obtain ⟨C, hC⟩ := (isCompact_range hG).isBounded.exists_norm_le
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun i => ?_) (integrable_const C) (fun i => Eventually.of_forall fun k => hC _ ⟨_, rfl⟩)
    (Eventually.of_forall fun k => (hG.tendsto k).comp (hs k))
  exact ((s i).map G).aestronglyMeasurable

/- English proof (translation)
Set `c : C(Y, C(X, ℂ))` to `ContinuousMap.curry ⟨fun p : Y × X => f p.1 p.2, hf⟩`. Establish `hI : Continuous fun g : C(X, ℂ) => ∫ k, g k ∂ν`. Use `Metric.continuous_iff.2 fun g ε hε => ?_` and prove the remaining obligations. Use `⟨ε / (ν.real Set.univ + 1), by positivity, fun h hh => ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, ← integral_sub (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]`.

Establish `hb : ∀ k, ‖h k - g k‖ ≤ dist h g` using `fun k => by`. Rewrite using `[← dist_eq_norm]`. Conclude with `ContinuousMap.dist_apply_le_dist k`. Use `(norm_integral_le_of_norm_le_const (Eventually.of_forall hb)).trans_lt ?_` and prove the remaining obligations. Establish `hp : 0 < ν.real Set.univ + 1` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul_of_nonneg_left (by linarith) dist_nonneg`. Use `_ < ε := (lt_div_iff₀ hp).1 hh`. Conclude with `hI.comp c.continuous`.
-/
private theorem cont_int {X Y : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    (ν : Measure X) [IsFiniteMeasure ν] (f : Y → X → ℂ) (hf : Continuous fun p : Y × X => f p.1 p.2) :
    Continuous fun y => ∫ k, f y k ∂ν := by
  let c : C(Y, C(X, ℂ)) := ContinuousMap.curry ⟨fun p : Y × X => f p.1 p.2, hf⟩
  have hI : Continuous fun g : C(X, ℂ) => ∫ k, g k ∂ν := by
    refine Metric.continuous_iff.2 fun g ε hε => ?_
    refine ⟨ε / (ν.real Set.univ + 1), by positivity, fun h hh => ?_⟩
    rw [dist_eq_norm, ← integral_sub (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have hb : ∀ k, ‖h k - g k‖ ≤ dist h g := fun k => by
      rw [← dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist k
    refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hb)).trans_lt ?_
    have hp : 0 < ν.real Set.univ + 1 := by positivity
    calc dist h g * ν.real Set.univ ≤ dist h g * (ν.real Set.univ + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) dist_nonneg
      _ < ε := (lt_div_iff₀ hp).1 hh
  exact hI.comp c.continuous

variable {μ : Measure (G1 K n)} [μ.IsHaarMeasure]

/- English proof (translation)
Use `Lp.ext ?_` and prove the remaining obligations. Establish `hm` using `map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K n) μ)`. Use `Measure.ae_le_iff_absolutelyContinuous.2 (hm ▸ Measure.AbsolutelyContinuous.rfl : quotientMeasure (Gam K n) μ ≪ Measure.map (mk (Gam K n)) (μ.restrict (fundamentalDomain (Gam K n)))) ?_` and prove the remaining obligations. Use `(ae_map_iff (measurable_mk _).aemeasurable ((Lp.stronglyMeasurable v).measurableSet_eq_fun (Lp.stronglyMeasurable w))).2 (ae_restrict_of_ae ?_)` and prove the remaining obligations. Use `filter_upwards [hv, hw] with y h1 h2`.

Rewrite using `[h1, h2]`.
-/
private theorem reps_ext' {v w : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) (hw : Reps μ w φ) : v = w := by
  refine Lp.ext ?_
  have hm := map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K n) μ)
  refine Measure.ae_le_iff_absolutelyContinuous.2 (hm ▸ Measure.AbsolutelyContinuous.rfl :
    quotientMeasure (Gam K n) μ ≪ Measure.map (mk (Gam K n)) (μ.restrict (fundamentalDomain (Gam K n)))) ?_
  refine (ae_map_iff (measurable_mk _).aemeasurable
    ((Lp.stronglyMeasurable v).measurableSet_eq_fun (Lp.stronglyMeasurable w))).2 (ae_restrict_of_ae ?_)
  filter_upwards [hv, hw] with y h1 h2
  rw [h1, h2]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy`. Simplify using `using hy`. Consider the case `insert a s ha ih => filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add (c a • v a) (∑ i ∈ s, c i • v i)), (quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul (c a) (v a)), h a (Finset.mem_insert_self _ _), ih fun i hi => h i (Finset.mem_insert_of_mem h …`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, h1, Pi.add_apply, h2, h4, Pi.smul_apply, h3, smul_eq_mul]`.
-/
private theorem reps_sum' {ι : Type} (s : Finset ι) (c : ι → ℂ) {v : ι → L2 μ} {φ : ι → G1 K n → ℂ} (h : ∀ i ∈ s, Reps μ (v i) (φ i)) :
    Reps μ (∑ i ∈ s, c i • v i) fun y => ∑ i ∈ s, c i * φ i y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
    simpa using hy
  | insert a s ha ih =>
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add (c a • v a) (∑ i ∈ s, c i • v i)),
      (quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul (c a) (v a)), h a (Finset.mem_insert_self _ _),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)] with y h1 h2 h3 h4
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, Pi.add_apply, h2, h4, Pi.smul_apply, h3, smul_eq_mul]

/- English proof (translation)
Use `filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (coeFn_rightRegularRep (Gam K n) μ g v), (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae hv] with y h1 h2`. Rewrite using `[h1, rightMul_mk, h2]`.
-/
private theorem reps_right' {v : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) (g : G1 K n) :
    Reps μ (rightRegularRep (Gam K n) μ g v) fun y => φ (y * g) := by
  filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (coeFn_rightRegularRep (Gam K n) μ g v),
    (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae hv] with y h1 h2
  rw [h1, rightMul_mk, h2]

/- English proof (translation)
Use `letI := TopologicalSpace.metrizableSpaceMetric X`. Use `haveI : TopologicalSpace.SeparableSpace (Set.univ : Set X) := inferInstance`. Set `s : ℕ → SimpleFunc X X` to `fun i => SimpleFunc.approxOn id measurable_id Set.univ (Classical.arbitrary X) (Set.mem_univ _) i`. Establish `hs : ∀ k, Tendsto (fun i => s i k) atTop (𝓝 k)` using `fun k => SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ _) (by simp)`. Set `G : X → LL μ` to `fun k => a k • rightRegularRep (Gam K n) μ (u k) v`.

Establish `hG : Continuous G` using `ha.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp hu)`. Set `W : ℕ → LL μ` to `fun i => ∫ k, G (s i k) ∂ν`. Set `P : ℕ → G1 K n → ℂ` to `fun i y => ∫ k, a (s i k) * φ (y * u (s i k)) ∂ν`. Establish `hW : ∀ i, Reps μ (W i) (P i)` using `fun i => by`. Establish `e1 : W i = ∑ x ∈ (s i).range, ((ν.real (s i ⁻¹' {x}) : ℂ) * a x) • rightRegularRep (Gam K n) μ (u x) v` using `by show ∫ k, G (s i k) ∂ν = _`.

Rewrite using `[simp_int]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `show ν.real (s i ⁻¹' {x}) • (a x • rightRegularRep (Gam K n) μ (u x) v) = _`. Rewrite using `[mul_smul, Complex.coe_smul]`. Both sides reduce to the same expression.

Establish `e2 : P i = fun y => ∑ x ∈ (s i).range, ((ν.real (s i ⁻¹' {x}) : ℂ) * a x) * φ (y * u x)`. Use function extensionality and compare the values at `y`. Use `(simp_int ν (s i) (fun x => a x * φ (y * u x))).trans (Finset.sum_congr rfl fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[Complex.real_smul, mul_assoc]`. Rewrite using `[e1, e2]`.

Conclude with `reps_sum' _ _ fun x _ => reps_right' hv (u x)`. Establish `hWl : Tendsto W atTop (𝓝 (∫ k, G k ∂ν))` using `simp_lim ν s hs G hG`. Establish `hPl : ∀ y, Tendsto (fun i => P i y) atTop (𝓝 (∫ k, a k * φ (y * u k) ∂ν))` using `fun y => simp_lim ν s hs (fun k => a k * φ (y * u k)) (ha.mul (hφ.comp (continuous_const.mul hu)))`. Take `⟨ns, hmono, hns⟩` from `(tendstoInMeasure_of_tendsto_Lp hWl).exists_seq_tendsto_ae`. Establish `h1` using `(quasiMeasurePreserving_mk (Gam K n) μ).ae hns`.

Establish `h2 : ∀ᵐ y ∂μ, ∀ i, (W i : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) = P i y` using `ae_all_iff.2 hW`. Use `filter_upwards [h1, h2] with y hy1 hy2`. Simplify using `only [hy2] at hy1`. Conclude with `tendsto_nhds_unique hy1 ((hPl y).comp hmono.tendsto_atTop)`.
-/
private theorem reps_int {X : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (a : X → ℂ) (ha : Continuous a) (u : X → G1 K n) (hu : Continuous u)
    {v : LL μ} {φ : G1 K n → ℂ} (hφ : Continuous φ) (hv : Reps μ v φ) :
    Reps μ (∫ k, a k • rightRegularRep (Gam K n) μ (u k) v ∂ν) fun y => ∫ k, a k * φ (y * u k) ∂ν := by
  letI := TopologicalSpace.metrizableSpaceMetric X
  haveI : TopologicalSpace.SeparableSpace (Set.univ : Set X) := inferInstance
  let s : ℕ → SimpleFunc X X := fun i => SimpleFunc.approxOn id measurable_id Set.univ (Classical.arbitrary X) (Set.mem_univ _) i
  have hs : ∀ k, Tendsto (fun i => s i k) atTop (𝓝 k) := fun k =>
    SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ _) (by simp)
  let G : X → LL μ := fun k => a k • rightRegularRep (Gam K n) μ (u k) v
  have hG : Continuous G := ha.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp hu)
  let W : ℕ → LL μ := fun i => ∫ k, G (s i k) ∂ν
  let P : ℕ → G1 K n → ℂ := fun i y => ∫ k, a (s i k) * φ (y * u (s i k)) ∂ν
  have hW : ∀ i, Reps μ (W i) (P i) := fun i => by
    have e1 : W i = ∑ x ∈ (s i).range, ((ν.real (s i ⁻¹' {x}) : ℂ) * a x) • rightRegularRep (Gam K n) μ (u x) v := by
      show ∫ k, G (s i k) ∂ν = _
      rw [simp_int]
      refine Finset.sum_congr rfl fun x _ => ?_
      show ν.real (s i ⁻¹' {x}) • (a x • rightRegularRep (Gam K n) μ (u x) v) = _
      rw [mul_smul, Complex.coe_smul]
      rfl
    have e2 : P i = fun y => ∑ x ∈ (s i).range, ((ν.real (s i ⁻¹' {x}) : ℂ) * a x) * φ (y * u x) := by
      funext y
      refine (simp_int ν (s i) (fun x => a x * φ (y * u x))).trans (Finset.sum_congr rfl fun x _ => ?_)
      rw [Complex.real_smul, mul_assoc]
    rw [e1, e2]
    exact reps_sum' _ _ fun x _ => reps_right' hv (u x)
  have hWl : Tendsto W atTop (𝓝 (∫ k, G k ∂ν)) := simp_lim ν s hs G hG
  have hPl : ∀ y, Tendsto (fun i => P i y) atTop (𝓝 (∫ k, a k * φ (y * u k) ∂ν)) := fun y =>
    simp_lim ν s hs (fun k => a k * φ (y * u k)) (ha.mul (hφ.comp (continuous_const.mul hu)))
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hWl).exists_seq_tendsto_ae
  have h1 := (quasiMeasurePreserving_mk (Gam K n) μ).ae hns
  have h2 : ∀ᵐ y ∂μ, ∀ i, (W i : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) = P i y := ae_all_iff.2 hW
  filter_upwards [h1, h2] with y hy1 hy2
  simp only [hy2] at hy1
  exact tendsto_nhds_unique hy1 ((hPl y).comp hmono.tendsto_atTop)

/- English proof (translation)
The claim follows from `Continuous.ae_eq_iff_eq μ hf hg |>.1 h`.
-/
private theorem cont_ae_eq {f g : G1 K n → ℂ} (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[μ] g) : f = g :=
  Continuous.ae_eq_iff_eq μ hf hg |>.1 h
end

/- English proof (translation)
Introduce `K _ _ _ ι _ C μ _ v φ hφ hv`. Use `haveI : TopologicalSpace.MetrizableSpace U2 := inferInstance`. Use `haveI : CompactSpace U2 := inferInstance`. Establish `hcu : ∀ i, Continuous (C.un i)` using `fun i => by`. Establish `hm : Continuous (fun x : U2 => (Pi.mulSingle i x : ι → U2))`.

Use `continuous_pi fun j => ?_` and prove the remaining obligations. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `using continuous_id'`. Simplify `continuous_const` using `[Pi.mulSingle_eq_of_ne h]`.

Unfold `Co.un arc1`. Conclude with `continuous_archP.comp (continuous_subtype_val.comp ((C.Φ 2).symm.continuous.comp hm))`. Establish `hca : Continuous (arc1 : archCompact K 2 → G1 K 2)` using `continuous_archP.comp continuous_subtype_val`. Use `haveI : TopologicalSpace.MetrizableSpace (archCompact K 2) := (C.Φ 2).toHomeomorph.isEmbedding.metrizableSpace`. Use `haveI : CompactSpace (archCompact K 2) := (C.Φ 2).toHomeomorph.symm.compactSpace`.

Use `⟨fun i n q h0 x => ?_, fun κ p hp => ?_⟩` and prove the remaining obligations. Establish `hT : Continuous (T n q)` using `continuous_const.mul (Complex.continuous_conj.comp (KT.continuous_psi n q n))`. Establish `hr` using `reps_int μK (T n q) hT (C.un i) (hcu i) hφ hv`. Establish `hc : Continuous fun y => ∫ m, T n q m * φ (y * C.un i m) ∂μK` using `cont_int μK _ (hT.comp continuous_snd |>.mul (hφ.comp (continuous_fst.mul ((hcu i).comp continuous_snd))))`. Establish `h0' : (∫ m, T n q m • rightRegularRep (Gam K 2) μ (C.un i m) v ∂μK) = 0` using `h0`.

Rewrite `hr` using `[h0']`. Establish `hz : Reps μ (0 : LL μ) fun _ => 0` using `by filter_upwards [(quasiMeasurePreserving_mk (Gam K 2) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K 2) μ))] with y hy`. Simplify using `using hy`. Establish `he : (fun y => ∫ m, T n q m * φ (y * C.un i m) ∂μK) = fun _ => 0`. Use `cont_ae_eq (μ := μ) hc continuous_const ?_` and prove the remaining obligations.

Use `filter_upwards [hr, hz] with y h1 h2`. Rewrite using `[← h1, h2]`. Establish `hx` using `congrFun he x`. Establish `hN : ((KT.normSqInt n q : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (KT.normSqInt_pos n q).ne'`. Simplify using `only [T, mul_assoc] at hx`.

Rewrite `hx` using `[integral_const_mul]`. Conclude with `(mul_eq_zero.1 hx).resolve_left (inv_ne_zero hN)`. Use `haveI := hp.haar.prob`. Establish `hr : Reps μ (pOp μ κ p v) fun y => ∫ k, p k * φ (y * arc1 k) ∂κ` using `reps_int κ p hp.cont arc1 hca hφ hv`. Establish `hc : Continuous fun y => ∫ k, p k * φ (y * arc1 k) ∂κ` using `cont_int κ _ (hp.cont.comp continuous_snd |>.mul (hφ.comp (continuous_fst.mul (hca.comp continuous_snd))))`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `hr` using `[h]`. Establish `he : (fun y => ∫ k, p k * φ (y * arc1 k) ∂κ) = φ`. Use `cont_ae_eq (μ := μ) hc hφ ?_` and prove the remaining obligations.

Use `filter_upwards [hr, hv] with y h1 h2`. Rewrite using `[← h1, h2]`. Conclude with `fun g => congrFun he g`. Introduce `h`. Establish `: (fun y => ∫ k, p k * φ (y * arc1 k) ∂κ) = φ` using `funext h`.

Rewrite `hr` using `[this]`. Conclude with `reps_ext' hr hv`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.ptPi :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (v : LL μ) (φ : G1 K 2 → ℂ), Continuous φ → Reps μ v φ →
      (∀ i n q, C.Pi μ i n q v = 0 → ∀ x, ∫ m, conj (KT.psi n q n m) * φ (x * C.un i m) ∂μK = 0) ∧
      ∀ (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), IdemA κ p → (pOp μ κ p v = v ↔ FixA κ p φ) := by
  intro K _ _ _ ι _ C μ _ v φ hφ hv
  haveI : TopologicalSpace.MetrizableSpace U2 := inferInstance
  haveI : CompactSpace U2 := inferInstance
  have hcu : ∀ i, Continuous (C.un i) := fun i => by
    have hm : Continuous (fun x : U2 => (Pi.mulSingle i x : ι → U2)) := by
      refine continuous_pi fun j => ?_
      by_cases h : j = i
      · subst h
        simpa using continuous_id'
      · simpa [Pi.mulSingle_eq_of_ne h] using continuous_const
    unfold Co.un arc1
    exact continuous_archP.comp (continuous_subtype_val.comp ((C.Φ 2).symm.continuous.comp hm))
  have hca : Continuous (arc1 : archCompact K 2 → G1 K 2) := continuous_archP.comp continuous_subtype_val
  haveI : TopologicalSpace.MetrizableSpace (archCompact K 2) := (C.Φ 2).toHomeomorph.isEmbedding.metrizableSpace
  haveI : CompactSpace (archCompact K 2) := (C.Φ 2).toHomeomorph.symm.compactSpace
  refine ⟨fun i n q h0 x => ?_, fun κ p hp => ?_⟩
  · have hT : Continuous (T n q) := continuous_const.mul (Complex.continuous_conj.comp (KT.continuous_psi n q n))
    have hr := reps_int μK (T n q) hT (C.un i) (hcu i) hφ hv
    have hc : Continuous fun y => ∫ m, T n q m * φ (y * C.un i m) ∂μK :=
      cont_int μK _ (hT.comp continuous_snd |>.mul (hφ.comp (continuous_fst.mul ((hcu i).comp continuous_snd))))
    have h0' : (∫ m, T n q m • rightRegularRep (Gam K 2) μ (C.un i m) v ∂μK) = 0 := h0
    rw [h0'] at hr
    have hz : Reps μ (0 : LL μ) fun _ => 0 := by
      filter_upwards [(quasiMeasurePreserving_mk (Gam K 2) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K 2) μ))] with y hy
      simpa using hy
    have he : (fun y => ∫ m, T n q m * φ (y * C.un i m) ∂μK) = fun _ => 0 := by
      refine cont_ae_eq (μ := μ) hc continuous_const ?_
      filter_upwards [hr, hz] with y h1 h2
      rw [← h1, h2]
    have hx := congrFun he x
    have hN : ((KT.normSqInt n q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (KT.normSqInt_pos n q).ne'
    simp only [T, mul_assoc] at hx
    rw [integral_const_mul] at hx
    exact (mul_eq_zero.1 hx).resolve_left (inv_ne_zero hN)
  · haveI := hp.haar.prob
    have hr : Reps μ (pOp μ κ p v) fun y => ∫ k, p k * φ (y * arc1 k) ∂κ := reps_int κ p hp.cont arc1 hca hφ hv
    have hc : Continuous fun y => ∫ k, p k * φ (y * arc1 k) ∂κ :=
      cont_int κ _ (hp.cont.comp continuous_snd |>.mul (hφ.comp (continuous_fst.mul (hca.comp continuous_snd))))
    constructor
    · intro h
      rw [h] at hr
      have he : (fun y => ∫ k, p k * φ (y * arc1 k) ∂κ) = φ := by
        refine cont_ae_eq (μ := μ) hc hφ ?_
        filter_upwards [hr, hv] with y h1 h2
        rw [← h1, h2]
      exact fun g => congrFun he g
    · intro h
      have : (fun y => ∫ k, p k * φ (y * arc1 k) ∂κ) = φ := funext h
      rw [this] at hr
      exact reps_ext' hr hv

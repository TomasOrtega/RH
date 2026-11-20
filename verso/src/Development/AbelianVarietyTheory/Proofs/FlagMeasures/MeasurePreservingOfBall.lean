import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.HomCovolume

section General

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

def HasCov (μ : Measure V) (L : Submodule ℤ V) (c : ℝ) : Prop :=
  ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L μ = c

/- English proof (translation)
Take `⟨hd, hz, hcov⟩` from `hc`. Establish `hL : L = ZLattice.comap ℝ L' (e : V →ₗ[ℝ] W)`. Use extensionality with `x`. Rewrite using `[h x]`. Both sides reduce to the same expression.

Substitute `hL` using the available equality. Conclude with `⟨ZLattice.comap_discreteTopology ℝ L' e.continuous e.injective, inferInstance, (ZLattice.covolume_comap L' ν μ he).trans hcov⟩`.
-/
theorem HasCov.of_measurePreserving {μ : Measure V} [μ.IsAddHaarMeasure] {ν : Measure W}
    [ν.IsAddHaarMeasure] (e : V ≃L[ℝ] W) (he : MeasurePreserving e μ ν) {L : Submodule ℤ V}
    {L' : Submodule ℤ W} (h : ∀ x, x ∈ L ↔ e x ∈ L') {c : ℝ} (hc : HasCov ν L' c) : HasCov μ L c := by
  obtain ⟨hd, hz, hcov⟩ := hc
  have hL : L = ZLattice.comap ℝ L' (e : V →ₗ[ℝ] W) := by
    ext x
    rw [h x]
    rfl
  subst hL
  exact ⟨ZLattice.comap_discreteTopology ℝ L' e.continuous e.injective, inferInstance,
    (ZLattice.covolume_comap L' ν μ he).trans hcov⟩

/- English proof (translation)
Take `⟨hd, hz, hcov⟩` from `hc`. Set `e : V ≃L[ℝ] V` to `(LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hf)).toContinuousLinearEquiv`. Establish `he : ∀ x, e x = f x` using `fun x => LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr hf) x`. Establish `hL : L = ZLattice.comap ℝ L' (e : V →ₗ[ℝ] V)`. Use extensionality with `x`.

Rewrite using `[h x, ← he x]`. Both sides reduce to the same expression. Substitute `hL` using the available equality. Use `⟨ZLattice.comap_discreteTopology ℝ L' e.continuous e.injective, inferInstance, ?_⟩` and prove the remaining obligations. Establish `hmp : MeasurePreserving e μ (Measure.map e μ)` using `⟨e.continuous.measurable, rfl⟩`.

Rewrite using `[ZLattice.covolume_comap L' (Measure.map e μ) μ hmp]`. Establish `hmap : Measure.map e μ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • μ`. Establish `hfun : (e : V → V) = f` using `funext he`. Rewrite using `[hfun]`. Conclude with `Measure.map_linearMap_addHaar_eq_smul_addHaar μ hf`.

Set `b` to `Module.Free.chooseBasis ℤ L'`. Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain L' _ (ZLattice.isAddFundamentalDomain b _), hmap, measureReal_ennreal_smul_apply, ← hcov, ZLattice.covolume_eq_measure_fundamentalDomain L' μ (ZLattice.isAddFundamentalDomain b μ), ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, div_ …`.
-/
theorem HasCov.of_det {μ : Measure V} [μ.IsAddHaarMeasure] (f : V →ₗ[ℝ] V)
    (hf : LinearMap.det f ≠ 0) {L L' : Submodule ℤ V} (h : ∀ x, x ∈ L ↔ f x ∈ L') {c : ℝ}
    (hc : HasCov μ L' c) : HasCov μ L (c / |LinearMap.det f|) := by
  obtain ⟨hd, hz, hcov⟩ := hc
  let e : V ≃L[ℝ] V := (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hf)).toContinuousLinearEquiv
  have he : ∀ x, e x = f x := fun x => LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr hf) x
  have hL : L = ZLattice.comap ℝ L' (e : V →ₗ[ℝ] V) := by
    ext x
    rw [h x, ← he x]
    rfl
  subst hL
  refine ⟨ZLattice.comap_discreteTopology ℝ L' e.continuous e.injective, inferInstance, ?_⟩
  have hmp : MeasurePreserving e μ (Measure.map e μ) :=
    ⟨e.continuous.measurable, rfl⟩
  rw [ZLattice.covolume_comap L' (Measure.map e μ) μ hmp]
  have hmap : Measure.map e μ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • μ := by
    have hfun : (e : V → V) = f := funext he
    rw [hfun]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar μ hf
  let b := Module.Free.chooseBasis ℤ L'
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L' _ (ZLattice.isAddFundamentalDomain b _),
    hmap, measureReal_ennreal_smul_apply, ← hcov,
    ZLattice.covolume_eq_measure_fundamentalDomain L' μ (ZLattice.isAddFundamentalDomain b μ),
    ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, div_eq_inv_mul]

/- English proof (translation)
Use `⟨e.continuous.measurable, ?_⟩` and prove the remaining obligations. Establish `hpre : (e : V → W) ⁻¹' Metric.closedBall 0 1 = Metric.closedBall 0 1`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, mem_closedBall_zero_iff]`. Conclude with `h x`.

Establish `hk` using `Measure.isAddLeftInvariant_eq_smul (Measure.map e μ) ν`. Use `set k := (Measure.map e μ).addHaarScalarFactor ν`. Establish `hball : Measure.map e μ (Metric.closedBall 0 1) = ν (Metric.closedBall 0 1)`. Rewrite using `[Measure.map_apply e.continuous.measurable Metric.isClosed_closedBall.measurableSet, hpre, hv]`. Establish `h0 : ν (Metric.closedBall 0 1) ≠ 0` using `(Metric.measure_closedBall_pos ν 0 one_pos).ne'`.

Establish `htop : ν (Metric.closedBall 0 1) ≠ ⊤` using `(isCompact_closedBall (0 : W) 1).measure_lt_top.ne`. Establish `hk1 : k = 1`. Rewrite `hball` using `[hk, Measure.smul_apply]`. Establish `: ((k : ENNReal)) * ν (Metric.closedBall 0 1) = 1 * ν (Metric.closedBall 0 1)`. Rewrite using `[one_mul]`.

Conclude with `hball`. Use `(ENNReal.mul_left_inj h0 htop).mp this` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[hk, hk1, one_smul]`.
-/
theorem measurePreserving_of_ball (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure W)
    [ν.IsAddHaarMeasure] (e : V ≃L[ℝ] W) (h : ∀ x, ‖e x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
    (hv : μ (Metric.closedBall 0 1) = ν (Metric.closedBall 0 1)) : MeasurePreserving e μ ν := by
  refine ⟨e.continuous.measurable, ?_⟩
  have hpre : (e : V → W) ⁻¹' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
    ext x
    simp only [Set.mem_preimage, mem_closedBall_zero_iff]
    exact h x
  have hk := Measure.isAddLeftInvariant_eq_smul (Measure.map e μ) ν
  set k := (Measure.map e μ).addHaarScalarFactor ν
  have hball : Measure.map e μ (Metric.closedBall 0 1) = ν (Metric.closedBall 0 1) := by
    rw [Measure.map_apply e.continuous.measurable Metric.isClosed_closedBall.measurableSet, hpre, hv]
  have h0 : ν (Metric.closedBall 0 1) ≠ 0 :=
    (Metric.measure_closedBall_pos ν 0 one_pos).ne'
  have htop : ν (Metric.closedBall 0 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : W) 1).measure_lt_top.ne
  have hk1 : k = 1 := by
    rw [hk, Measure.smul_apply] at hball
    have : ((k : ENNReal)) * ν (Metric.closedBall 0 1) = 1 * ν (Metric.closedBall 0 1) := by
      rw [one_mul]
      exact hball
    have := (ENNReal.mul_left_inj h0 htop).mp this
    exact_mod_cast this
  rw [hk, hk1, one_smul]

/- English proof (translation)
Establish `hspan` using `b.ofZLatticeBasis_span ℝ L`. Take `⟨⟨a, ha⟩, h1, h2⟩` from `ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ L) x`. Use `⟨a, ⟨hspan ▸ ha, by simpa [Submodule.vadd_def, vadd_eq_add] using h1⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `a' ⟨ha', h'⟩`. Use `h2 ⟨a', hspan.symm ▸ ha'⟩ (by simpa [Submodule.vadd_def, vadd_eq_add] using h')` as an intermediate fact.

Conclude with `congrArg Subtype.val this`.
-/
private theorem HasCov.existsUnique_lattice_translate_mem_fundamentalDomain {κ : Type} [Finite κ] (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (b : Module.Basis κ ℤ L) (x : V) :
    ∃! a : V, a ∈ L ∧ a + x ∈ ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) := by
  have hspan := b.ofZLatticeBasis_span ℝ L
  obtain ⟨⟨a, ha⟩, h1, h2⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ L) x
  refine ⟨a, ⟨hspan ▸ ha, by simpa [Submodule.vadd_def, vadd_eq_add] using h1⟩, ?_⟩
  rintro a' ⟨ha', h'⟩
  have := h2 ⟨a', hspan.symm ▸ ha'⟩ (by simpa [Submodule.vadd_def, vadd_eq_add] using h')
  exact congrArg Subtype.val this

/- English proof (translation)
Use `choose hd hz hcov using h`. Establish `hD : DiscreteTopology (Submodule.pi Set.univ L)`. Set `f : Submodule.pi Set.univ L → ∀ i, L i` to `fun g i => ⟨g.1 i, g.2 i (Set.mem_univ i)⟩`. Establish `hf : Continuous f` using `continuous_pi fun i => ((continuous_apply i).comp continuous_subtype_val).subtype_mk _`. Establish `hinj : Function.Injective f`.

Introduce `g g' hg`. Use extensionality with `i`. Conclude with `congrArg Subtype.val (congrFun hg i)`. Conclude with `DiscreteTopology.of_continuous_injective hf hinj`. Establish `hZ : IsZLattice ℝ (Submodule.pi Set.univ L)`.

Use `⟨?_⟩` and prove the remaining obligations. Use `eq_top_iff.mpr fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.univ_sum_single x]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hx : x i ∈ Submodule.span ℝ (L i : Set V)`.

Rewrite using `[(hz i).span_top]`. Discharge the goal by the elementary cases of `trivial`. Generalize the expression as in `x i = y at hx ⊢`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Use `Submodule.subset_span fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `using hy`. Simplify using `[hk]`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz'`. Rewrite using `[Pi.single_add]`. Conclude with `Submodule.add_mem _ hy hz'`. Consider the case `smul a y _ hy`.

Rewrite using `[Pi.single_smul']`. Conclude with `Submodule.smul_mem _ a hy`. Use `⟨hD, hZ, ?_⟩` and prove the remaining obligations. Set `b` to `fun i => Module.Free.chooseBasis ℤ (L i)`. Set `F` to `fun i => ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ (L i))`.

Establish `hmeas : MeasurableSet (Set.univ.pi F)` using `MeasurableSet.univ_pi fun i => ZSpan.fundamentalDomain_measurableSet _`. Establish `hfd : IsAddFundamentalDomain (Submodule.pi Set.univ L) (Set.univ.pi F) (Measure.pi fun _ : ι => μ)`. Use `IsAddFundamentalDomain.mk' hmeas.nullMeasurableSet fun x => ?_` and prove the remaining obligations. Use `choose a ha hu using fun i => HasCov.existsUnique_lattice_translate_mem_fundamentalDomain (L i) (b i) (x i)`. Use `⟨⟨a, fun i _ => (ha i).1⟩, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [Submodule.vadd_def, vadd_eq_add, Set.mem_univ_pi]`. Conclude with `fun i => (ha i).2`. Introduce and unpack `⟨g, hg⟩ hgx`. Simplify using `only [Submodule.vadd_def, vadd_eq_add, Set.mem_univ_pi] at hgx`. Use extensionality with `i`.

Conclude with `hu i (g i) ⟨hg i (Set.mem_univ i), hgx i⟩`. Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain _ _ hfd, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hcov i, ZLattice.covolume_eq_measure_fundamentalDomain (L i) μ (ZLattice.isAddFundamentalDomain (b i) μ), measureReal_def]`.
-/
theorem HasCov.pi {ι : Type} [Fintype ι] {μ : Measure V} [μ.IsAddHaarMeasure] {L : ι → Submodule ℤ V}
    {c : ι → ℝ} (h : ∀ i, HasCov μ (L i) (c i)) :
    HasCov (Measure.pi fun _ : ι => μ) (Submodule.pi Set.univ L) (∏ i, c i) := by
  choose hd hz hcov using h
  classical

  have hD : DiscreteTopology (Submodule.pi Set.univ L) := by
    let f : Submodule.pi Set.univ L → ∀ i, L i := fun g i => ⟨g.1 i, g.2 i (Set.mem_univ i)⟩
    have hf : Continuous f := continuous_pi fun i =>
      ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
    have hinj : Function.Injective f := by
      intro g g' hg
      ext i
      exact congrArg Subtype.val (congrFun hg i)
    exact DiscreteTopology.of_continuous_injective hf hinj

  have hZ : IsZLattice ℝ (Submodule.pi Set.univ L) := by
    refine ⟨?_⟩
    refine eq_top_iff.mpr fun x _ => ?_
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hx : x i ∈ Submodule.span ℝ (L i : Set V) := by
      rw [(hz i).span_top]
      trivial
    generalize x i = y at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      refine Submodule.subset_span fun k _ => ?_
      by_cases hk : k = i
      · subst hk
        simpa using hy
      · simp [hk]
    | zero => simp
    | add y z _ _ hy hz' =>
      rw [Pi.single_add]
      exact Submodule.add_mem _ hy hz'
    | smul a y _ hy =>
      rw [Pi.single_smul']
      exact Submodule.smul_mem _ a hy
  refine ⟨hD, hZ, ?_⟩

  let b := fun i => Module.Free.chooseBasis ℤ (L i)
  let F := fun i => ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ (L i))
  have hmeas : MeasurableSet (Set.univ.pi F) :=
    MeasurableSet.univ_pi fun i => ZSpan.fundamentalDomain_measurableSet _
  have hfd : IsAddFundamentalDomain (Submodule.pi Set.univ L) (Set.univ.pi F)
      (Measure.pi fun _ : ι => μ) := by
    refine IsAddFundamentalDomain.mk' hmeas.nullMeasurableSet fun x => ?_
    choose a ha hu using fun i => HasCov.existsUnique_lattice_translate_mem_fundamentalDomain (L i) (b i) (x i)
    refine ⟨⟨a, fun i _ => (ha i).1⟩, ?_, ?_⟩
    · simp only [Submodule.vadd_def, vadd_eq_add, Set.mem_univ_pi]
      exact fun i => (ha i).2
    · rintro ⟨g, hg⟩ hgx
      simp only [Submodule.vadd_def, vadd_eq_add, Set.mem_univ_pi] at hgx
      ext i
      exact hu i (g i) ⟨hg i (Set.mem_univ i), hgx i⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hfd, measureReal_def, Measure.pi_pi,
    ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hcov i, ZLattice.covolume_eq_measure_fundamentalDomain (L i) μ
    (ZLattice.isAddFundamentalDomain (b i) μ), measureReal_def]

end General

section Jac

/- English proof (translation)
Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]`.
-/
theorem det_real_mulVec {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    LinearMap.det ((Matrix.toLin' A).restrictScalars ℝ) = ‖A.det‖ ^ 2 := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]

/- English proof (translation)
Use `set e : (Fin r → Fin s → ℂ) ≃ₗ[ℂ] (Fin r × Fin s → ℂ) := (LinearEquiv.curry ℂ ℂ (Fin r) (Fin s)).symm`. Establish `key : (e : (Fin r → Fin s → ℂ) →ₗ[ℂ] (Fin r × Fin s → ℂ)) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] _) = Matrix.toLin' (kroneckerMap (· * ·) A Bᵀ)`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use function extensionality and compare the values at `p`.

Take `⟨i, k⟩` from `p`. Establish `h` using `congrFun (congrFun (hf (Function.curry v)) i) k`. Simplify using `only [Matrix.of_apply] at h`. Simplify using `only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Matrix.toLin'_apply, e]`. Simplify using `[LinearEquiv.curry]`.

Rewrite using `[h]`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, kroneckerMap_apply, transpose_apply, Fintype.sum_prod_type, Finset.sum_mul, Function.curry_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← LinearMap.det_conj f e, key, LinearMap.det_toLin', det_kronecker, det_transpose, Fintype.card_fin, Fintype.card_fin]`.
-/
theorem det_mul_mul {r s : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (B : Matrix (Fin s) (Fin s) ℂ)
    (f : (Fin r → Fin s → ℂ) →ₗ[ℂ] (Fin r → Fin s → ℂ))
    (hf : ∀ T, Matrix.of (f T) = A * Matrix.of T * B) : LinearMap.det f = A.det ^ s * B.det ^ r := by

  set e : (Fin r → Fin s → ℂ) ≃ₗ[ℂ] (Fin r × Fin s → ℂ) := (LinearEquiv.curry ℂ ℂ (Fin r) (Fin s)).symm
  have key : (e : (Fin r → Fin s → ℂ) →ₗ[ℂ] (Fin r × Fin s → ℂ)) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] _) =
      Matrix.toLin' (kroneckerMap (· * ·) A Bᵀ) := by
    apply LinearMap.ext
    intro v
    funext p
    obtain ⟨i, k⟩ := p
    have h := congrFun (congrFun (hf (Function.curry v)) i) k
    simp only [Matrix.of_apply] at h
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Matrix.toLin'_apply, e]
    simp [LinearEquiv.curry]
    rw [h]
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, kroneckerMap_apply,
      transpose_apply, Fintype.sum_prod_type, Finset.sum_mul, Function.curry_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [← LinearMap.det_conj f e, key, LinearMap.det_toLin', det_kronecker, det_transpose,
    Fintype.card_fin, Fintype.card_fin]

end Jac

/- English proof (translation)
Establish `h : ∀ _ : ι, (volume : Measure (κ → ℂ)).IsAddHaarMeasure` using `fun _ => inferInstance`. Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
theorem haar_two (ι κ : Type) [Fintype ι] [Fintype κ] : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := by
  have h : ∀ _ : ι, (volume : Measure (κ → ℂ)).IsAddHaarMeasure := fun _ => inferInstance
  exact Measure.pi.isAddHaarMeasure _

attribute [local instance] haar_two

/- English proof (translation)
Establish `h : ∀ _ : ι, (volume : Measure (κ → κ' → ℂ)).IsAddHaarMeasure` using `fun _ => haar_two κ κ'`. Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
theorem haar_three (ι κ κ' : Type) [Fintype ι] [Fintype κ] [Fintype κ'] :
    (volume : Measure (ι → κ → κ' → ℂ)).IsAddHaarMeasure := by
  have h : ∀ _ : ι, (volume : Measure (κ → κ' → ℂ)).IsAddHaarMeasure := fun _ => haar_two κ κ'
  exact Measure.pi.isAddHaarMeasure _

attribute [local instance] haar_three

section NF

variable (E : Type) [Field E] [NumberField E]

/- English proof (translation)
Establish `hf : Formalism.HermitianLatticesTheory.fDeg E = InfinitePlace.nrComplexPlaces E`. Rewrite using `[Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`. Establish `hpos : 0 < Formalism.HermitianLatticesTheory.fDeg E` using `Fintype.card_pos`. Rewrite using `[Formalism.HermitianLatticesTheory.vInv, div_pow, ← Real.rpow_natCast (|(discr E : ℝ)| ^ _), ← Real.rpow_mul (abs_nonneg _), Real.sqrt_eq_rpow, hf, div_eq_mul_inv, mul_comm, inv_pow]`. Use `congr 2`.

Rewrite using `[← hf]`. Clear the denominators using the available nonvanishing facts.
-/
theorem vInv_pow (hE : IsTotallyComplex E) :
    Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E = (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces E * √|(discr E : ℝ)| := by
  have hf : Formalism.HermitianLatticesTheory.fDeg E = InfinitePlace.nrComplexPlaces E := by
    rw [Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hpos : 0 < Formalism.HermitianLatticesTheory.fDeg E := Fintype.card_pos

  rw [Formalism.HermitianLatticesTheory.vInv, div_pow, ← Real.rpow_natCast (|(discr E : ℝ)| ^ _), ← Real.rpow_mul (abs_nonneg _),
    Real.sqrt_eq_rpow, hf, div_eq_mul_inv, mul_comm, inv_pow]
  congr 2
  rw [← hf]
  field_simp

/- English proof (translation)
Establish `hc : ∀ w : InfinitePlace E, w.IsComplex` using `fun w => hE.isComplex w`. Establish `: IsEmpty {w : InfinitePlace E // w.IsReal}` using `⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hc w.1) w.2⟩`. Set `σ : InfinitePlace E ≃ {w : InfinitePlace E // w.IsComplex}` to `(Equiv.subtypeUnivEquiv hc).symm`. Set `e₁ : (InfinitePlace E → ℂ) ≃ₗ[ℝ] ({w : InfinitePlace E // w.IsComplex} → ℂ)` to `LinearEquiv.piCongrLeft ℝ (fun _ => ℂ) σ`. Set `e₂ : ({w : InfinitePlace E // w.IsComplex} → ℂ) ≃ₗ[ℝ] mixedEmbedding.mixedSpace E` to `(LinearEquiv.uniqueProd).symm`.

Set `e : (InfinitePlace E → ℂ) ≃L[ℝ] mixedEmbedding.mixedSpace E` to `(e₁.trans e₂).toContinuousLinearEquiv`. Establish `he_apply : ∀ z, e z = ((0 : {w : InfinitePlace E // w.IsReal} → ℝ), fun w => z w.1)`. Introduce `z`. Use extensionality with `w`. Conclude with `(IsEmpty.false w).elim`.

Simplify using `[e, e₁, e₂, σ, LinearEquiv.piCongrLeft]`. Establish `hrel : ∀ z : InfinitePlace E → ℂ, MeasurableEquiv.piCongrLeft (fun _ => ℂ) σ z = fun w => z w.1`. Introduce `z`. Use extensionality with `⟨w, hw⟩`. Conclude with `Equiv.piCongrLeft_apply_apply (fun _ => ℂ) σ z w`.

Establish `hprod : MeasurePreserving (fun x : {w : InfinitePlace E // w.IsComplex} → ℂ => ((0 : {w : InfinitePlace E // w.IsReal} → ℝ), x)) volume (volume : Measure (mixedEmbedding.mixedSpace E))`. Use `⟨measurable_prodMk_left, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.volume_eq_prod, volume_pi (α := fun _ : {w : InfinitePlace E // w.IsReal} => ℝ), Measure.pi_of_empty _ 0, Measure.dirac_prod]`. Establish `he : MeasurePreserving e volume volume`. Establish `h` using `hprod.comp (volume_measurePreserving_piCongrLeft (fun _ => ℂ) σ)`.

Establish `hfun : (⇑e : (InfinitePlace E → ℂ) → mixedEmbedding.mixedSpace E) = (fun x : {w : InfinitePlace E // w.IsComplex} → ℂ => ((0 : {w : InfinitePlace E // w.IsReal} → ℝ), x)) ∘ MeasurableEquiv.piCongrLeft (fun _ => ℂ) σ`. Use function extensionality and compare the values at `z`. Rewrite using `[he_apply, Function.comp_apply, hrel]`. Rewrite using `[hfun]`. Conclude with `h`.

Set `I : (FractionalIdeal (𝓞 E)⁰ E)ˣ` to `Units.mk0 a ha`. Use `⟨(mixedEmbedding.idealLattice E I).comap ((e : (InfinitePlace E → ℂ) →ₗ[ℝ] _).restrictScalars ℤ), fun z => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e z ∈ mixedEmbedding.idealLattice E I ↔ _`. Rewrite using `[mixedEmbedding.mem_idealLattice]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, hyz⟩`. Use `⟨y, hy, fun w => ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun p => p.2 (σ w)) hyz`. Simplify using `only [he_apply] at h2`. Rewrite `h2` using `[mixedEmbedding.mixedEmbedding_apply_isComplex]`.

Conclude with `h2.symm`. Introduce and unpack `⟨y, hy, hyz⟩`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[he_apply]`. Use extensionality with `w`.

Conclude with `(IsEmpty.false w).elim`. Rewrite using `[mixedEmbedding.mixedEmbedding_apply_isComplex]`. Conclude with `(hyz w.1).symm`. Use `HasCov.of_measurePreserving e he (L' := mixedEmbedding.idealLattice E I) (fun _ => Iff.rfl) ⟨inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[mixedEmbedding.covolume_idealLattice, vInv_pow E hE, Units.val_mk0, mul_assoc]`.
-/
theorem exists_idealLat (hE : IsTotallyComplex E) (a : FractionalIdeal (𝓞 E)⁰ E) (ha : a ≠ 0) :
    ∃ L : Submodule ℤ (InfinitePlace E → ℂ), (∀ z, z ∈ L ↔ ∃ y ∈ a, ∀ w, z w = w.embedding y) ∧
      HasCov volume L ((FractionalIdeal.absNorm a : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) := by
  classical
  have hc : ∀ w : InfinitePlace E, w.IsComplex := fun w => hE.isComplex w
  have : IsEmpty {w : InfinitePlace E // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hc w.1) w.2⟩

  let σ : InfinitePlace E ≃ {w : InfinitePlace E // w.IsComplex} := (Equiv.subtypeUnivEquiv hc).symm
  let e₁ : (InfinitePlace E → ℂ) ≃ₗ[ℝ] ({w : InfinitePlace E // w.IsComplex} → ℂ) :=
    LinearEquiv.piCongrLeft ℝ (fun _ => ℂ) σ
  let e₂ : ({w : InfinitePlace E // w.IsComplex} → ℂ) ≃ₗ[ℝ] mixedEmbedding.mixedSpace E :=
    (LinearEquiv.uniqueProd).symm
  let e : (InfinitePlace E → ℂ) ≃L[ℝ] mixedEmbedding.mixedSpace E :=
    (e₁.trans e₂).toContinuousLinearEquiv
  have he_apply : ∀ z, e z = ((0 : {w : InfinitePlace E // w.IsReal} → ℝ), fun w => z w.1) := by
    intro z
    ext w
    · exact (IsEmpty.false w).elim
    · simp [e, e₁, e₂, σ, LinearEquiv.piCongrLeft]
  have hrel : ∀ z : InfinitePlace E → ℂ,
      MeasurableEquiv.piCongrLeft (fun _ => ℂ) σ z = fun w => z w.1 := by
    intro z
    ext ⟨w, hw⟩
    exact Equiv.piCongrLeft_apply_apply (fun _ => ℂ) σ z w
  have hprod : MeasurePreserving (fun x : {w : InfinitePlace E // w.IsComplex} → ℂ =>
      ((0 : {w : InfinitePlace E // w.IsReal} → ℝ), x)) volume
      (volume : Measure (mixedEmbedding.mixedSpace E)) := by
    refine ⟨measurable_prodMk_left, ?_⟩
    rw [Measure.volume_eq_prod, volume_pi (α := fun _ : {w : InfinitePlace E // w.IsReal} => ℝ),
      Measure.pi_of_empty _ 0, Measure.dirac_prod]
  have he : MeasurePreserving e volume volume := by
    have h := hprod.comp (volume_measurePreserving_piCongrLeft (fun _ => ℂ) σ)
    have hfun : (⇑e : (InfinitePlace E → ℂ) → mixedEmbedding.mixedSpace E) =
        (fun x : {w : InfinitePlace E // w.IsComplex} → ℂ =>
          ((0 : {w : InfinitePlace E // w.IsReal} → ℝ), x)) ∘ MeasurableEquiv.piCongrLeft (fun _ => ℂ) σ := by
      funext z
      rw [he_apply, Function.comp_apply, hrel]
    rw [hfun]
    exact h

  let I : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 a ha
  refine ⟨(mixedEmbedding.idealLattice E I).comap ((e : (InfinitePlace E → ℂ) →ₗ[ℝ] _).restrictScalars ℤ),
    fun z => ?_, ?_⟩
  · change e z ∈ mixedEmbedding.idealLattice E I ↔ _
    rw [mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨y, hy, hyz⟩
      refine ⟨y, hy, fun w => ?_⟩
      have h2 := congrArg (fun p => p.2 (σ w)) hyz
      simp only [he_apply] at h2
      rw [mixedEmbedding.mixedEmbedding_apply_isComplex] at h2
      exact h2.symm
    · rintro ⟨y, hy, hyz⟩
      refine ⟨y, hy, ?_⟩
      rw [he_apply]
      ext w
      · exact (IsEmpty.false w).elim
      · rw [mixedEmbedding.mixedEmbedding_apply_isComplex]
        exact (hyz w.1).symm
  · refine HasCov.of_measurePreserving e he (L' := mixedEmbedding.idealLattice E I) (fun _ => Iff.rfl)
      ⟨inferInstance, inferInstance, ?_⟩
    rw [mixedEmbedding.covolume_idealLattice, vInv_pow E hE, Units.val_mk0, mul_assoc]

/- English proof (translation)
Use `choose L hL hLc using fun i => exists_idealLat E hE (c i) (hc i)`. Set `e₀ : (InfinitePlace E → Fin j → ℂ) ≃ₗ[ℝ] (Fin j → InfinitePlace E → ℂ)` to `{ toFun := fun x i w => x w i invFun := fun y w i => y i w map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Set `e` to `e₀.toContinuousLinearEquiv`. Establish `he : MeasurePreserving e volume (volume : Measure (Fin j → InfinitePlace E → ℂ))`. Use `measurePreserving_of_ball _ _ e (fun x => ?_) ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `‖fun i w => x w i‖ ≤ 1 ↔ ‖x‖ ≤ 1`. Simplify using `only [pi_norm_le_iff_of_nonneg zero_le_one]`. Conclude with `forall_comm`. Simplify using `only [closedBall_pi _ zero_le_one, volume_pi_pi, Pi.zero_apply]`. Conclude with `Finset.prod_comm`.

Use `⟨Submodule.comap ((e : (InfinitePlace E → Fin j → ℂ) →L[ℝ] _).toLinearMap.restrictScalars ℤ) (Submodule.pi Set.univ L), fun z => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies]`. Express the relevant statement in the definitionally equal form `(∀ i, (fun w => z w i) ∈ L i) ↔ _`. Simplify using `only [hL]`. Conclude with `HasCov.of_measurePreserving e he (fun x => Iff.rfl) (by rw [volume_pi]; exact HasCov.pi hLc)`.
-/
theorem hasCov_vec (hE : IsTotallyComplex E) {j : ℕ} (c : Fin j → FractionalIdeal (𝓞 E)⁰ E)
    (hc : ∀ i, c i ≠ 0) :
    ∃ L : Submodule ℤ (InfinitePlace E → Fin j → ℂ),
      (∀ z, z ∈ L ↔ ∀ i, ∃ y ∈ c i, ∀ w, z w i = w.embedding y) ∧
      HasCov volume L (∏ i, (FractionalIdeal.absNorm (c i) : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) := by
  choose L hL hLc using fun i => exists_idealLat E hE (c i) (hc i)

  let e₀ : (InfinitePlace E → Fin j → ℂ) ≃ₗ[ℝ] (Fin j → InfinitePlace E → ℂ) :=
    { toFun := fun x i w => x w i
      invFun := fun y w i => y i w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e := e₀.toContinuousLinearEquiv
  have he : MeasurePreserving e volume (volume : Measure (Fin j → InfinitePlace E → ℂ)) := by
    refine measurePreserving_of_ball _ _ e (fun x => ?_) ?_
    · change ‖fun i w => x w i‖ ≤ 1 ↔ ‖x‖ ≤ 1
      simp only [pi_norm_le_iff_of_nonneg zero_le_one]
      exact forall_comm
    · simp only [closedBall_pi _ zero_le_one, volume_pi_pi, Pi.zero_apply]
      exact Finset.prod_comm
  refine ⟨Submodule.comap ((e : (InfinitePlace E → Fin j → ℂ) →L[ℝ] _).toLinearMap.restrictScalars ℤ)
    (Submodule.pi Set.univ L), fun z => ?_, ?_⟩
  · simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies]
    change (∀ i, (fun w => z w i) ∈ L i) ↔ _
    simp only [hL]
  · exact HasCov.of_measurePreserving e he (fun x => Iff.rfl) (by rw [volume_pi]; exact HasCov.pi hLc)

/- English proof (translation)
Use `choose L hL hLc using fun i => exists_idealLat E hE (c i) (hc i)`. Set `e₀ : (InfinitePlace E → Fin r → Fin s → ℂ) ≃ₗ[ℝ] (Fin r × Fin s → InfinitePlace E → ℂ)` to `{ toFun := fun x i w => x w i.1 i.2 invFun := fun y w a b => y (a, b) w map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Set `e` to `e₀.toContinuousLinearEquiv`. Establish `he : MeasurePreserving e volume (volume : Measure (Fin r × Fin s → InfinitePlace E → ℂ))`. Use `measurePreserving_of_ball _ _ e (fun x => ?_) ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `‖fun (i : Fin r × Fin s) w => x w i.1 i.2‖ ≤ 1 ↔ ‖x‖ ≤ 1`. Simplify using `only [pi_norm_le_iff_of_nonneg zero_le_one, Prod.forall]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h w a b => h a b w`. Conclude with `fun h a b w => h w a b`.

Simplify using `only [closedBall_pi _ zero_le_one, volume_pi_pi, Pi.zero_apply, Fintype.prod_prod_type]`. Rewrite using `[Finset.prod_comm]`. Conclude with `Finset.prod_congr rfl fun _ _ => Finset.prod_comm`. Use `⟨Submodule.comap ((e : (InfinitePlace E → Fin r → Fin s → ℂ) →L[ℝ] _).toLinearMap.restrictScalars ℤ) (Submodule.pi Set.univ L), fun z => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies]`.

Express the relevant statement in the definitionally equal form `(∀ i, (fun w => z w i.1 i.2) ∈ L i) ↔ _`. Simplify using `only [hL]`. Conclude with `HasCov.of_measurePreserving e he (fun x => Iff.rfl) (by rw [volume_pi]; exact HasCov.pi hLc)`.
-/
theorem hasCov_mat (hE : IsTotallyComplex E) {r s : ℕ} (c : Fin r × Fin s → FractionalIdeal (𝓞 E)⁰ E)
    (hc : ∀ i, c i ≠ 0) :
    ∃ L : Submodule ℤ (InfinitePlace E → Fin r → Fin s → ℂ),
      (∀ z, z ∈ L ↔ ∀ i, ∃ y ∈ c i, ∀ w, z w i.1 i.2 = w.embedding y) ∧
      HasCov volume L (∏ i, (FractionalIdeal.absNorm (c i) : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) := by
  choose L hL hLc using fun i => exists_idealLat E hE (c i) (hc i)

  let e₀ : (InfinitePlace E → Fin r → Fin s → ℂ) ≃ₗ[ℝ] (Fin r × Fin s → InfinitePlace E → ℂ) :=
    { toFun := fun x i w => x w i.1 i.2
      invFun := fun y w a b => y (a, b) w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e := e₀.toContinuousLinearEquiv
  have he : MeasurePreserving e volume (volume : Measure (Fin r × Fin s → InfinitePlace E → ℂ)) := by
    refine measurePreserving_of_ball _ _ e (fun x => ?_) ?_
    · change ‖fun (i : Fin r × Fin s) w => x w i.1 i.2‖ ≤ 1 ↔ ‖x‖ ≤ 1
      simp only [pi_norm_le_iff_of_nonneg zero_le_one, Prod.forall]
      constructor
      · exact fun h w a b => h a b w
      · exact fun h a b w => h w a b
    · simp only [closedBall_pi _ zero_le_one, volume_pi_pi, Pi.zero_apply, Fintype.prod_prod_type]
      rw [Finset.prod_comm]
      exact Finset.prod_congr rfl fun _ _ => Finset.prod_comm
  refine ⟨Submodule.comap ((e : (InfinitePlace E → Fin r → Fin s → ℂ) →L[ℝ] _).toLinearMap.restrictScalars ℤ)
    (Submodule.pi Set.univ L), fun z => ?_, ?_⟩
  · simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies]
    change (∀ i, (fun w => z w i.1 i.2) ∈ L i) ↔ _
    simp only [hL]
  · exact HasCov.of_measurePreserving e he (fun x => Iff.rfl) (by rw [volume_pi]; exact HasCov.pi hLc)

/- English proof (translation)
Distinguish the cases in `hI0 : I = 0`. Use `⟨fun _ => 1, rfl, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[hI0, FractionalIdeal.mem_zero_iff]`. Rewrite using `[hx, zero_smul]`. Conclude with `Λ.zero_mem`.

Establish `h1 : (1 : E) ∈ I * I⁻¹`. Rewrite using `[mul_inv_cancel₀ hI0]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩`. Establish `key : ∀ z ∈ I * I⁻¹, ∃ v : Fin (j + 1) → E, v 0 = z ∧ ∀ x ∈ I, x • v ∈ Λ`. Introduce `z hz`.

Use `FractionalIdeal.mul_induction_on hz ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Take `⟨y, hy, hy0⟩` from `(hI a).1 ha`. Use `⟨b • y, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `[hy0, mul_comm]`.

Take `⟨r, hr⟩` from `(FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hI0).1 hb x hx)`. Rewrite using `[smul_smul, mul_comm x b, ← hr, algebraMap_smul]`. Conclude with `Λ.smul_mem r hy`. Introduce and unpack `z₁ z₂ ⟨v₁, hv₁, h₁⟩ ⟨v₂, hv₂, h₂⟩`. Use `⟨v₁ + v₂, by simp [hv₁, hv₂], fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Conclude with `Λ.add_mem (h₁ x hx) (h₂ x hx)`. Conclude with `key 1 h1`.
-/
private theorem exists_vec_one_smul_mem_of_first_coord {j : ℕ} (Λ : Submodule (𝓞 E) (Fin (j + 1) → E))
    (I : FractionalIdeal (𝓞 E)⁰ E) (hI : ∀ x, x ∈ I ↔ ∃ y ∈ Λ, y 0 = x) :
    ∃ v : Fin (j + 1) → E, v 0 = 1 ∧ ∀ x ∈ I, x • v ∈ Λ := by
  by_cases hI0 : I = 0
  · refine ⟨fun _ => 1, rfl, fun x hx => ?_⟩
    rw [hI0, FractionalIdeal.mem_zero_iff] at hx
    rw [hx, zero_smul]
    exact Λ.zero_mem
  · have h1 : (1 : E) ∈ I * I⁻¹ := by
      rw [mul_inv_cancel₀ hI0]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    have key : ∀ z ∈ I * I⁻¹, ∃ v : Fin (j + 1) → E, v 0 = z ∧ ∀ x ∈ I, x • v ∈ Λ := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        obtain ⟨y, hy, hy0⟩ := (hI a).1 ha
        refine ⟨b • y, ?_, fun x hx => ?_⟩
        · simp [hy0, mul_comm]
        · obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hI0).1 hb x hx)
          rw [smul_smul, mul_comm x b, ← hr, algebraMap_smul]
          exact Λ.smul_mem r hy
      · rintro z₁ z₂ ⟨v₁, hv₁, h₁⟩ ⟨v₂, hv₂, h₂⟩
        refine ⟨v₁ + v₂, by simp [hv₁, hv₂], fun x hx => ?_⟩
        rw [smul_add]
        exact Λ.add_mem (h₁ x hx) (h₂ x hx)
    exact key 1 h1

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `Λ _`. Use `⟨1, fun i => i.elim0, by simp, fun y => ⟨fun _ i => i.elim0, fun _ => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[Subsingleton.elim y 0]`. Conclude with `Λ.zero_mem`. Consider the case `succ j ih`. Introduce `Λ hΛ`. Set `π : (Fin (j + 1) → E) →ₗ[𝓞 E] E` to `LinearMap.proj 0`.

Set `τ : (Fin (j + 1) → E) →ₗ[𝓞 E] (Fin j → E)` to `LinearMap.funLeft (𝓞 E) E Fin.succ`. Set `Λ' : Submodule (𝓞 E) (Fin j → E)` to `(Λ ⊓ LinearMap.ker π).map τ`. Establish `hΛ' : Λ'.FG` using `(hΛ.of_le inf_le_left).map τ`. Establish `hmem' : ∀ u, u ∈ Λ' ↔ (Fin.cons 0 u : Fin (j + 1) → E) ∈ Λ`. Introduce `u`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨hy, hy0⟩, rfl⟩`. Establish `hy0' : y 0 = 0` using `hy0`. Establish `hyc : (Fin.cons 0 (τ y) : Fin (j + 1) → E) = y`. Rewrite using `[← hy0']`.

Conclude with `Fin.cons_self_tail y`. Rewrite using `[hyc]`. Conclude with `hy`. Introduce `h`. Use `⟨Fin.cons 0 u, ⟨h, by simp [π]⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `i`. Simplify using `[τ, LinearMap.funLeft]`. Take `⟨P', c', hP', hc'⟩` from `ih Λ' hΛ'`. Set `I : FractionalIdeal (𝓞 E)⁰ E` to `⟨Λ.map π, FractionalIdeal.isFractional_of_fg (hΛ.map π)⟩`. Establish `hI : ∀ x, x ∈ I ↔ ∃ y ∈ Λ, y 0 = x`.

Introduce `x`. Rewrite using `[← FractionalIdeal.mem_coe, FractionalIdeal.coe_mk, Submodule.mem_map]`. Both sides reduce to the same expression. Take `⟨v, hv0, hv⟩` from `exists_vec_one_smul_mem_of_first_coord E Λ I hI`. Establish `htl : ∀ y z : Fin (j + 1) → E, Fin.tail (y + z) = Fin.tail y + Fin.tail z` using `fun _ _ => rfl`.

Establish `hts : ∀ (a : E) (y : Fin (j + 1) → E), Fin.tail (a • y) = a • Fin.tail y` using `fun _ _ => rfl`. Set `φ : (Fin (j + 1) → E) →ₗ[E] (Fin (j + 1) → E)` to `{ toFun := fun y => Fin.cons (y 0) (P' *ᵥ (Fin.tail y - y 0 • Fin.tail v)) map_add' := by`. Introduce `y z`. Use extensionality with `i`. Use `Fin.cases ?_ (fun k => ?_) i` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using `[htl, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, add_smul]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := by`. Introduce `a y`.

Use extensionality with `i`. Use `Fin.cases ?_ (fun k => ?_) i` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[hts, Matrix.mulVec_sub, Matrix.mulVec_smul]`. Use `ring }`.

Establish `hφ : ∀ y, φ y = Fin.cons (y 0) (P' *ᵥ (Fin.tail y - y 0 • Fin.tail v))` using `fun y => rfl`. Establish `hPv : ∀ y, LinearMap.toMatrix' φ *ᵥ y = φ y` using `fun y => by`. Rewrite using `[← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']`. Use `⟨LinearMap.toMatrix' φ, Fin.cons I c', ?_, ?_⟩` and prove the remaining obligations. Introduce `hdet`.

Take `⟨y, hy, hPy⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Rewrite `hPy` using `[hPv, hφ]`. Establish `h0 : y 0 = 0` using `by simpa using congrFun hPy 0`. Establish `ht : P' *ᵥ Fin.tail y = 0`. Use extensionality with `i`.

Simplify `congrFun hPy i.succ` using `[h0]`. Establish `ht' : Fin.tail y = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hP' (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hne, ht⟩)`. Apply `hy` to reduce the goal to its premises.

Rewrite using `[← Fin.cons_self_tail y, h0, ht']`. Use extensionality with `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun k => ?_) i <;> simp`. Introduce `y`. Rewrite using `[hPv, hφ, Fin.forall_fin_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[← hc', hmem']`. Establish `hcons : (Fin.cons 0 (Fin.tail y - y 0 • Fin.tail v) : Fin (j + 1) → E) = y - y 0 • v`. Use extensionality with `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun k => ?_) i <;> simp [hv0, Fin.tail]`.

Rewrite using `[hcons]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hy0 : y 0 ∈ I` using `(hI _).2 ⟨y, hy, rfl⟩`. Conclude with `⟨hy0, Λ.sub_mem hy (hv _ hy0)⟩`.

Introduce and unpack `⟨hy0, h⟩`. Simplify using `using Λ.add_mem h (hv _ hy0)`.
-/
private theorem exists_matrix_fractionalIdeals_coords_of_fg : ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Λ.FG →
    ∃ (P : Matrix (Fin j) (Fin j) E) (c : Fin j → FractionalIdeal (𝓞 E)⁰ E), P.det ≠ 0 ∧
      ∀ y, y ∈ Λ ↔ ∀ i, (P *ᵥ y) i ∈ c i := by
  intro j
  induction j with
  | zero =>
    intro Λ _
    refine ⟨1, fun i => i.elim0, by simp, fun y => ⟨fun _ i => i.elim0, fun _ => ?_⟩⟩
    rw [Subsingleton.elim y 0]
    exact Λ.zero_mem
  | succ j ih =>
    intro Λ hΛ
    let π : (Fin (j + 1) → E) →ₗ[𝓞 E] E := LinearMap.proj 0
    let τ : (Fin (j + 1) → E) →ₗ[𝓞 E] (Fin j → E) := LinearMap.funLeft (𝓞 E) E Fin.succ
    let Λ' : Submodule (𝓞 E) (Fin j → E) := (Λ ⊓ LinearMap.ker π).map τ
    have hΛ' : Λ'.FG := (hΛ.of_le inf_le_left).map τ
    have hmem' : ∀ u, u ∈ Λ' ↔ (Fin.cons 0 u : Fin (j + 1) → E) ∈ Λ := by
      intro u
      constructor
      · rintro ⟨y, ⟨hy, hy0⟩, rfl⟩
        have hy0' : y 0 = 0 := hy0
        have hyc : (Fin.cons 0 (τ y) : Fin (j + 1) → E) = y := by
          rw [← hy0']
          exact Fin.cons_self_tail y
        rw [hyc]
        exact hy
      · intro h
        refine ⟨Fin.cons 0 u, ⟨h, by simp [π]⟩, ?_⟩
        ext i
        simp [τ, LinearMap.funLeft]
    obtain ⟨P', c', hP', hc'⟩ := ih Λ' hΛ'
    let I : FractionalIdeal (𝓞 E)⁰ E := ⟨Λ.map π, FractionalIdeal.isFractional_of_fg (hΛ.map π)⟩
    have hI : ∀ x, x ∈ I ↔ ∃ y ∈ Λ, y 0 = x := by
      intro x
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mk, Submodule.mem_map]
      rfl
    obtain ⟨v, hv0, hv⟩ := exists_vec_one_smul_mem_of_first_coord E Λ I hI
    have htl : ∀ y z : Fin (j + 1) → E, Fin.tail (y + z) = Fin.tail y + Fin.tail z := fun _ _ => rfl
    have hts : ∀ (a : E) (y : Fin (j + 1) → E), Fin.tail (a • y) = a • Fin.tail y := fun _ _ => rfl
    let φ : (Fin (j + 1) → E) →ₗ[E] (Fin (j + 1) → E) :=
      { toFun := fun y => Fin.cons (y 0) (P' *ᵥ (Fin.tail y - y 0 • Fin.tail v))
        map_add' := by
          intro y z
          ext i
          refine Fin.cases ?_ (fun k => ?_) i
          · simp
          · simp [htl, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, add_smul]
            ring
        map_smul' := by
          intro a y
          ext i
          refine Fin.cases ?_ (fun k => ?_) i
          · simp
          · simp [hts, Matrix.mulVec_sub, Matrix.mulVec_smul]
            ring }
    have hφ : ∀ y, φ y = Fin.cons (y 0) (P' *ᵥ (Fin.tail y - y 0 • Fin.tail v)) := fun y => rfl
    have hPv : ∀ y, LinearMap.toMatrix' φ *ᵥ y = φ y := fun y => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    refine ⟨LinearMap.toMatrix' φ, Fin.cons I c', ?_, ?_⟩
    · intro hdet
      obtain ⟨y, hy, hPy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
      rw [hPv, hφ] at hPy
      have h0 : y 0 = 0 := by simpa using congrFun hPy 0
      have ht : P' *ᵥ Fin.tail y = 0 := by
        ext i
        simpa [h0] using congrFun hPy i.succ
      have ht' : Fin.tail y = 0 := by
        by_contra hne
        exact hP' (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hne, ht⟩)
      apply hy
      rw [← Fin.cons_self_tail y, h0, ht']
      ext i
      refine Fin.cases ?_ (fun k => ?_) i <;> simp
    · intro y
      rw [hPv, hφ, Fin.forall_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hc', hmem']
      have hcons : (Fin.cons 0 (Fin.tail y - y 0 • Fin.tail v) : Fin (j + 1) → E) = y - y 0 • v := by
        ext i
        refine Fin.cases ?_ (fun k => ?_) i <;> simp [hv0, Fin.tail]
      rw [hcons]
      constructor
      · intro hy
        have hy0 : y 0 ∈ I := (hI _).2 ⟨y, hy, rfl⟩
        exact ⟨hy0, Λ.sub_mem hy (hv _ hy0)⟩
      · rintro ⟨hy0, h⟩
        simpa using Λ.add_mem h (hv _ hy0)

/- English proof (translation)
Take `⟨P, c, hP, hc⟩` from `exists_matrix_fractionalIdeals_coords_of_fg E j Λ hΛ.fg`. Use `⟨P, c, hP, fun i hi => ?_, hc⟩` and prove the remaining obligations. Set `ψ : (Fin j → E) →ₗ[E] E` to `LinearMap.proj i ∘ₗ Matrix.toLin' P`. Establish `hle : Submodule.span E (Λ : Set (Fin j → E)) ≤ LinearMap.ker ψ`. Rewrite using `[Submodule.span_le]`.

Introduce `y hy`. Establish `hyi` using `(hc y).1 hy i`. Rewrite `hyi` using `[hi, FractionalIdeal.mem_zero_iff]`. Simplify `hyi` using `[ψ]`. Rewrite `hle` using `[hΛ.span_eq_top]`.

Establish `hu : IsUnit P.det` using `isUnit_iff_ne_zero.2 hP`. Establish `h1` using `hle (Submodule.mem_top (x := P⁻¹ *ᵥ Pi.single i 1))`. Rewrite `h1` using `[LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `(P *ᵥ (P⁻¹ *ᵥ Pi.single i 1)) i = 0 at h1`. Rewrite `h1` using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]`.

Simplify using `at h1`.
-/
theorem exists_coords {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) :
    ∃ (P : Matrix (Fin j) (Fin j) E) (c : Fin j → FractionalIdeal (𝓞 E)⁰ E), P.det ≠ 0 ∧ (∀ i, c i ≠ 0) ∧
      ∀ y, y ∈ Λ ↔ ∀ i, (P *ᵥ y) i ∈ c i := by
  obtain ⟨P, c, hP, hc⟩ := exists_matrix_fractionalIdeals_coords_of_fg E j Λ hΛ.fg
  refine ⟨P, c, hP, fun i hi => ?_, hc⟩
  let ψ : (Fin j → E) →ₗ[E] E := LinearMap.proj i ∘ₗ Matrix.toLin' P
  have hle : Submodule.span E (Λ : Set (Fin j → E)) ≤ LinearMap.ker ψ := by
    rw [Submodule.span_le]
    intro y hy
    have hyi := (hc y).1 hy i
    rw [hi, FractionalIdeal.mem_zero_iff] at hyi
    simpa [ψ] using hyi
  rw [hΛ.span_eq_top] at hle
  have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have h1 := hle (Submodule.mem_top (x := P⁻¹ *ᵥ Pi.single i 1))
  rw [LinearMap.mem_ker] at h1
  change (P *ᵥ (P⁻¹ *ᵥ Pi.single i 1)) i = 0 at h1
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h1
  simp at h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`.

Conclude with `⟨y, hy, fun w => rfl⟩`. Consider the case `zero => exact ⟨0, Λ.zero_mem, fun w => by ext a; simp [Matrix.mulVec, dotProduct]⟩`. Consider the case `add x x' _ _ hx hx'`. Take `⟨y, hy, hxy⟩` from `hx`. Take `⟨y', hy', hxy'⟩` from `hx'`.

Use `⟨y + y', Λ.add_mem hy hy', fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, hxy w, hxy' w, ← Matrix.mulVec_add]`. Use `congr 1`. Use extensionality with `a`. Simplify using the standard rewrite rules.

Consider the case `smul n x _ hx`. Take `⟨y, hy, hxy⟩` from `hx`. Use `⟨n • y, zsmul_mem hy n, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, hxy w, ← Matrix.mulVec_smul]`. Use `congr 1`.

Use extensionality with `a`. Simplify using the standard rewrite rules. Introduce and unpack `⟨y, hy, hz⟩`. Take `rfl : z = fun w => (Matrix.of (g w))⁻¹ *ᵥ fun a => w.embedding (y a)` from `funext hz`. Conclude with `Submodule.subset_span ⟨y, hy, rfl⟩`.
-/
theorem mem_latAt {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) (z : VecInf E j) :
    z ∈ latAt E j Λ g ↔ ∃ y ∈ Λ, ∀ w, z w = (Matrix.of (g w))⁻¹ *ᵥ fun a => w.embedding (y a) := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, fun w => rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, fun w => by ext a; simp [Matrix.mulVec, dotProduct]⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy, hxy⟩ := hx
      obtain ⟨y', hy', hxy'⟩ := hx'
      refine ⟨y + y', Λ.add_mem hy hy', fun w => ?_⟩
      rw [Pi.add_apply, hxy w, hxy' w, ← Matrix.mulVec_add]
      congr 1
      ext a
      simp
    | smul n x _ hx =>
      obtain ⟨y, hy, hxy⟩ := hx
      refine ⟨n • y, zsmul_mem hy n, fun w => ?_⟩
      rw [Pi.smul_apply, hxy w, ← Matrix.mulVec_smul]
      congr 1
      ext a
      simp
  · rintro ⟨y, hy, hz⟩
    obtain rfl : z = fun w => (Matrix.of (g w))⁻¹ *ᵥ fun a => w.embedding (y a) := funext hz
    exact Submodule.subset_span ⟨y, hy, rfl⟩

end NF

section Main

variable (E : Type) [Field E] [NumberField E]

/- English proof (translation)
Introduce `h`. Establish `h0 : detNorm E j g = 0` using `Finset.prod_eq_zero (Finset.mem_univ w) (by rw [h, norm_zero]; ring)`. Rewrite `hg` using `[h0]`. Conclude with `lt_irrefl 0 hg`.
-/
theorem det_ne_zero_of_detNorm {j : ℕ} {g : MatInf E j} (hg : 0 < detNorm E j g) (w : InfinitePlace E) :
    (Matrix.of (g w)).det ≠ 0 := by
  intro h
  have h0 : detNorm E j g = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ w) (by rw [h, norm_zero]; ring)
  rw [h0] at hg
  exact lt_irrefl 0 hg

/- English proof (translation)
Establish `e` using `RingHom.map_det w.embedding P`. Rewrite `e` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← e]`. Conclude with `(map_ne_zero _).mpr hP`.
-/
theorem det_map_ne_zero {j : ℕ} {P : Matrix (Fin j) (Fin j) E} (hP : P.det ≠ 0) (w : InfinitePlace E) :
    (P.map w.embedding).det ≠ 0 := by
  have e := RingHom.map_det w.embedding P
  rw [RingHom.mapMatrix_apply] at e
  rw [← e]
  exact (map_ne_zero _).mpr hP

/- English proof (translation)
Take `⟨L₀, hL₀, hcov⟩` from `hasCov_vec E hE c hc`. Establish `hMdet : ∀ w : InfinitePlace E, (P.map w.embedding * Matrix.of (g w)).det ≠ 0` using `fun w => by`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (det_map_ne_zero E hP w) (det_ne_zero_of_detNorm E hg w)`. Set `φ : VecInf E j →ₗ[ℝ] VecInf E j` to `LinearMap.pi fun w => ((Matrix.toLin' (P.map w.embedding * Matrix.of (g w))).restrictScalars ℝ) ∘ₗ LinearMap.proj w`.

Establish `hφ : ∀ z w, φ z w = (P.map w.embedding * Matrix.of (g w)) *ᵥ z w` using `fun z w => rfl`. Establish `hdet : LinearMap.det φ = ∏ w, ‖(P.map w.embedding * Matrix.of (g w)).det‖ ^ 2`. Rewrite using `[LinearMap.det_pi]`. Conclude with `Finset.prod_congr rfl fun w _ => det_real_mulVec _`. Establish `hpos : 0 < ∏ w, ‖(P.map w.embedding * Matrix.of (g w)).det‖ ^ 2` using `Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hMdet w)) 2`.

Establish `hmem : ∀ z, z ∈ latAt E j Λ g ↔ φ z ∈ L₀`. Introduce `z`. Rewrite using `[mem_latAt, hL₀]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hz⟩ i`.

Use `⟨(P *ᵥ y) i, (hΛ y).1 hy i, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, hz w, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_ne_zero_of_detNorm E hg w)), Matrix.mul_one, RingHom.map_mulVec]`. Both sides reduce to the same expression. Introduce `h choose x hx hxw using h`. Use `⟨P⁻¹ *ᵥ x, (hΛ _).2 fun i => ?_, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), Matrix.one_mulVec]`. Conclude with `hx i`. Establish `hx' : (fun a => w.embedding (x a)) = (P.map w.embedding * Matrix.of (g w)) *ᵥ z w`. Use function extensionality and compare the values at `i`. Rewrite using `[← hφ]`.

Conclude with `(hxw i w).symm`. Establish `hinv : P⁻¹.map w.embedding * P.map w.embedding = 1`. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP)]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hy : (fun a => w.embedding ((P⁻¹ *ᵥ x) a)) = P⁻¹.map w.embedding *ᵥ fun a => w.embedding (x a)`.

Use function extensionality and compare the values at `a`. Conclude with `RingHom.map_mulVec _ _ _ _`. Rewrite using `[hy, hx', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (Matrix.of (g w))⁻¹, ← Matrix.mul_assoc (P⁻¹.map _), hinv, Matrix.one_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (det_ne_zero_of_detNorm E hg w)), Matrix.one_mulVec]`. Take `⟨_, _, h⟩` from `HasCov.of_det φ (hdet ▸ hpos.ne') hmem hcov`. Rewrite using `[covAt, h, hdet, abs_of_pos hpos]`.
-/
theorem covAt_latAt (hE : IsTotallyComplex E) {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (P : Matrix (Fin j) (Fin j) E) (c : Fin j → FractionalIdeal (𝓞 E)⁰ E) (hP : P.det ≠ 0)
    (hc : ∀ i, c i ≠ 0) (hΛ : ∀ y, y ∈ Λ ↔ ∀ i, (P *ᵥ y) i ∈ c i) (g : MatInf E j)
    (hg : 0 < detNorm E j g) :
    covAt E j (latAt E j Λ g) =
      (∏ i, (FractionalIdeal.absNorm (c i) : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) /
        ∏ w : InfinitePlace E, ‖(P.map w.embedding * Matrix.of (g w)).det‖ ^ 2 := by
  classical
  obtain ⟨L₀, hL₀, hcov⟩ := hasCov_vec E hE c hc
  have hMdet : ∀ w : InfinitePlace E, (P.map w.embedding * Matrix.of (g w)).det ≠ 0 := fun w => by
    rw [Matrix.det_mul]
    exact mul_ne_zero (det_map_ne_zero E hP w) (det_ne_zero_of_detNorm E hg w)
  let φ : VecInf E j →ₗ[ℝ] VecInf E j := LinearMap.pi fun w =>
    ((Matrix.toLin' (P.map w.embedding * Matrix.of (g w))).restrictScalars ℝ) ∘ₗ LinearMap.proj w
  have hφ : ∀ z w, φ z w = (P.map w.embedding * Matrix.of (g w)) *ᵥ z w := fun z w => rfl
  have hdet : LinearMap.det φ = ∏ w, ‖(P.map w.embedding * Matrix.of (g w)).det‖ ^ 2 := by
    rw [LinearMap.det_pi]
    exact Finset.prod_congr rfl fun w _ => det_real_mulVec _
  have hpos : 0 < ∏ w, ‖(P.map w.embedding * Matrix.of (g w)).det‖ ^ 2 :=
    Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hMdet w)) 2
  have hmem : ∀ z, z ∈ latAt E j Λ g ↔ φ z ∈ L₀ := by
    intro z
    rw [mem_latAt, hL₀]
    constructor
    · rintro ⟨y, hy, hz⟩ i
      refine ⟨(P *ᵥ y) i, (hΛ y).1 hy i, fun w => ?_⟩
      rw [hφ, hz w, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_ne_zero_of_detNorm E hg w)), Matrix.mul_one,
        RingHom.map_mulVec]
      rfl
    · intro h
      choose x hx hxw using h
      refine ⟨P⁻¹ *ᵥ x, (hΛ _).2 fun i => ?_, fun w => ?_⟩
      · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), Matrix.one_mulVec]
        exact hx i
      · have hx' : (fun a => w.embedding (x a)) = (P.map w.embedding * Matrix.of (g w)) *ᵥ z w := by
          funext i
          rw [← hφ]
          exact (hxw i w).symm
        have hinv : P⁻¹.map w.embedding * P.map w.embedding = 1 := by
          rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP)]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        have hy : (fun a => w.embedding ((P⁻¹ *ᵥ x) a)) = P⁻¹.map w.embedding *ᵥ fun a => w.embedding (x a) := by
          funext a
          exact RingHom.map_mulVec _ _ _ _
        rw [hy, hx', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (Matrix.of (g w))⁻¹, ← Matrix.mul_assoc (P⁻¹.map _), hinv, Matrix.one_mul,
          Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (det_ne_zero_of_detNorm E hg w)), Matrix.one_mulVec]
  obtain ⟨_, _, h⟩ := HasCov.of_det φ (hdet ▸ hpos.ne') hmem hcov
  rw [covAt, h, hdet, abs_of_pos hpos]

/- English proof (translation)
Establish `hu : P' * P'⁻¹ = 1` using `Matrix.mul_nonsing_inv P' (isUnit_iff_ne_zero.mpr hP')`. Establish `key : ∀ u : Fin s → E, P *ᵥ T *ᵥ P'⁻¹ *ᵥ u = (P * T * P'⁻¹) *ᵥ u`. Introduce `u`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Prove the components needed by the constructor for the conclusion.

Introduce `h i k`. Rewrite using `[FractionalIdeal.mem_div_iff_of_ne_zero (hc' k)]`. Introduce `x hx`. Establish `hy : P'⁻¹ *ᵥ Pi.single k x ∈ Λ'`. Rewrite using `[hΛ']`.

Introduce `l`. Rewrite using `[Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]`. Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality. Simplify using `using hx`.

Rewrite using `[Pi.single_eq_of_ne hl, ← FractionalIdeal.mem_coe]`. Conclude with `Submodule.zero_mem _`. Use `(hΛ _).mp (h _ hy) i` as an intermediate fact. Rewrite `this` using `[key, Matrix.mulVec_single]`. Simplify `this` using `[mul_comm]`.

Introduce `h y hy`. Rewrite using `[hΛ]`. Introduce `i`. Establish `hy' : y = P'⁻¹ *ᵥ P' *ᵥ y`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P' (isUnit_iff_ne_zero.mpr hP'), Matrix.one_mulVec]`.

Rewrite using `[hy', key]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[← FractionalIdeal.mem_coe]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[FractionalIdeal.mem_coe]`.

Establish `h1` using `(FractionalIdeal.mem_div_iff_of_ne_zero (hc' k)).mp (h i k) _ ((hΛ' y).mp hy k)`. Conclude with `h1`.
-/
theorem maps_iff {r s : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin s → E))
    (P : Matrix (Fin r) (Fin r) E) (c : Fin r → FractionalIdeal (𝓞 E)⁰ E)
    (hΛ : ∀ y, y ∈ Λ ↔ ∀ i, (P *ᵥ y) i ∈ c i)
    (P' : Matrix (Fin s) (Fin s) E) (c' : Fin s → FractionalIdeal (𝓞 E)⁰ E) (hP' : P'.det ≠ 0)
    (hc' : ∀ i, c' i ≠ 0) (hΛ' : ∀ y, y ∈ Λ' ↔ ∀ i, (P' *ᵥ y) i ∈ c' i) (T : Matrix (Fin r) (Fin s) E) :
    (∀ y ∈ Λ', T *ᵥ y ∈ Λ) ↔ ∀ i k, (P * T * P'⁻¹) i k ∈ c i / c' k := by
  have hu : P' * P'⁻¹ = 1 := Matrix.mul_nonsing_inv P' (isUnit_iff_ne_zero.mpr hP')
  have key : ∀ u : Fin s → E, P *ᵥ T *ᵥ P'⁻¹ *ᵥ u = (P * T * P'⁻¹) *ᵥ u := by
    intro u
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  constructor
  · intro h i k
    rw [FractionalIdeal.mem_div_iff_of_ne_zero (hc' k)]
    intro x hx
    have hy : P'⁻¹ *ᵥ Pi.single k x ∈ Λ' := by
      rw [hΛ']
      intro l
      rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
      by_cases hl : l = k
      · subst hl
        simpa using hx
      · rw [Pi.single_eq_of_ne hl, ← FractionalIdeal.mem_coe]
        exact Submodule.zero_mem _
    have := (hΛ _).mp (h _ hy) i
    rw [key, Matrix.mulVec_single] at this
    simpa [mul_comm] using this
  · intro h y hy
    rw [hΛ]
    intro i
    have hy' : y = P'⁻¹ *ᵥ P' *ᵥ y := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P' (isUnit_iff_ne_zero.mpr hP'),
        Matrix.one_mulVec]
    rw [hy', key]
    simp only [Matrix.mulVec, dotProduct]
    rw [← FractionalIdeal.mem_coe]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [FractionalIdeal.mem_coe]
    have h1 := (FractionalIdeal.mem_div_iff_of_ne_zero (hc' k)).mp (h i k) _ ((hΛ' y).mp hy k)
    exact h1

/- English proof (translation)
Rewrite using `[div_pow, mul_pow, div_div_eq_mul_div, div_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, inv_pow, ← pow_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem homCovolume_eq_mul_pow (a b v Da Db : ℝ) (F r s : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hv : v ≠ 0)
    (hDa : Da ≠ 0) (hDb : Db ≠ 0) :
    a ^ s / b ^ r * v ^ (F * (r * s)) / (Da ^ (2 * s) * ((Db ^ 2)⁻¹) ^ r) =
      (a * (v ^ F) ^ r / Da ^ 2) ^ s * (v ^ (F * s) / (b * (v ^ F) ^ s / Db ^ 2)) ^ r := by
  rw [div_pow, mul_pow, div_div_eq_mul_div, div_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
    ← pow_mul, ← pow_mul, ← pow_mul, inv_pow, ← pow_mul]
  field_simp
  ring

end Main

/- English proof (translation)
Introduce `E _ _ hE r s Λ Λ' hΛl hΛ'l g g' hg hg' L hL`. Take `⟨P, c, hP, hc, hΛ⟩` from `exists_coords E Λ hΛl`. Take `⟨P', c', hP', hc', hΛ'⟩` from `exists_coords E Λ' hΛ'l`. Take `⟨L₀, hL₀, hcov⟩` from `hasCov_mat E hE (fun p : Fin r × Fin s => c p.1 / c' p.2) (fun p => div_ne_zero (hc p.1) (hc' p.2))`. Establish `hgu : ∀ w, IsUnit (Matrix.of (g w)).det` using `fun w => isUnit_iff_ne_zero.2 (det_ne_zero_of_detNorm E hg w)`.

Establish `hgu' : ∀ w, IsUnit (Matrix.of (g' w)).det` using `fun w => isUnit_iff_ne_zero.2 (det_ne_zero_of_detNorm E hg' w)`. Establish `hPi : ∀ (w : InfinitePlace E) {n : Type} [Fintype n] (X : Matrix (Fin r) n ℂ), P⁻¹.map w.embedding * (P.map w.embedding * X) = X`. Introduce `w n _ X`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`. Establish `hPi' : ∀ (w : InfinitePlace E) {n : Type} [Fintype n] (X : Matrix (Fin s) n ℂ), P'⁻¹.map w.embedding * (P'.map w.embedding * X) = X`.

Introduce `w n _ X`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP'), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`. Set `f : InfinitePlace E → (Fin r → Fin s → ℂ) →ₗ[ℂ] (Fin r → Fin s → ℂ)` to `fun w => { toFun := fun T => P.map w.embedding * Matrix.of (g w) * Matrix.of T * ((Matrix.of (g' w))⁻¹ * P'⁻¹.map w.embedding) map_add' := fun T U => by`. Rewrite using `[show Matrix.of (T + U) = Matrix.of T + Matrix.of U from rfl, Matrix.mul_add, Matrix.add_mul]`. Both sides reduce to the same expression.

Use the proof step `map_smul' := fun a T => by`. Rewrite using `[show Matrix.of (a • T) = a • Matrix.of T from rfl, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]`. Use `rfl }`. Set `φ : (InfinitePlace E → Fin r → Fin s → ℂ) →ₗ[ℝ] (InfinitePlace E → Fin r → Fin s → ℂ)` to `LinearMap.pi fun w => ((f w).restrictScalars ℝ) ∘ₗ LinearMap.proj w`. Establish `hφ : ∀ z w, Matrix.of (φ z w) = P.map w.embedding * Matrix.of (g w) * Matrix.of (z w) * ((Matrix.of (g' w))⁻¹ * P'⁻¹.map w.embedding)` using `fun z w => rfl`.

Establish `hB1 : ∀ w, ((Matrix.of (g' w))⁻¹ * P'⁻¹.map w.embedding).det * (P'.map w.embedding * Matrix.of (g' w)).det = 1`. Introduce `w`. Rewrite using `[← Matrix.det_mul, Matrix.mul_assoc, hPi' w, Matrix.nonsing_inv_mul _ (hgu' w), Matrix.det_one]`. Establish `hdetφ : LinearMap.det φ = (∏ w, ‖(P.map w.embedding * Matrix.of (g w)).det‖ ^ 2) ^ s * ((∏ w, ‖(P'.map w.embedding * Matrix.of (g' w)).det‖ ^ 2)⁻¹) ^ r`. Rewrite using `[LinearMap.det_pi, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.det_restrictScalars, det_mul_mul _ _ (f w) (fun T => rfl), Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_mul, norm_pow, norm_pow, eq_inv_of_mul_eq_one_left (by rw [← norm_mul, hB1 w, norm_one] : ‖((Matrix.of (g' w))⁻¹ * P'⁻¹.map w.embedding).det‖ * ‖(P'.m …`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : ∀ {n : ℕ} (Q : Matrix (Fin n) (Fin n) E) (h : MatInf E n), Q.det ≠ 0 → 0 < detNorm E n h → 0 < ∏ w, ‖(Q.map w.embedding * Matrix.of (h w)).det‖ ^ 2`. Introduce `n Q h hQ hh`.

Use `Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) 2` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (det_map_ne_zero E hQ w) (det_ne_zero_of_detNorm E hh w)`. Establish `hDa` using `hpos P g hP hg`. Establish `hDb` using `hpos P' g' hP' hg'`.

Establish `hdetpos : 0 < LinearMap.det φ`. Rewrite using `[hdetφ]`. Conclude with `mul_pos (pow_pos hDa _) (pow_pos (inv_pos.2 hDb) _)`. Establish `hmem : ∀ z, z ∈ L ↔ φ z ∈ L₀`. Introduce `z`.

Rewrite using `[hL, hL₀]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨T, hT, hz⟩ p`. Use `⟨(P * T * P'⁻¹) p.1 p.2, (maps_iff E Λ Λ' P c hΛ P' c' hP' hc' hΛ' T).1 hT p.1 p.2, fun w => ?_⟩` and prove the remaining obligations. Establish `hw : Matrix.of (φ z w) = (P * T * P'⁻¹).map w.embedding`.

Rewrite using `[hφ, hz w, Matrix.map_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ (hgu' w), Matrix.mul_nonsing_inv_cancel_left _ _ (hgu w)]`. Conclude with `congrFun (congrFun hw p.1) p.2`. Introduce `h choose y hy hyw using h`.

Use `⟨P⁻¹ * Matrix.of (fun i k => y (i, k)) * P', ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `hM : P * (P⁻¹ * Matrix.of (fun i k => y (i, k)) * P') * P'⁻¹ = Matrix.of (fun i k => y (i, k))`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP'), Matrix.mul_one]`. Use `(maps_iff E Λ Λ' P c hΛ P' c' hP' hc' hΛ' _).2 fun i k => ?_` and prove the remaining obligations. Rewrite using `[hM]`.

Conclude with `hy (i, k)`. Establish `hM : (Matrix.of (fun i k => y (i, k))).map w.embedding = Matrix.of (φ z w)`. Use extensionality with `i k`. Conclude with `(hyw (i, k) w).symm`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hM, hφ]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hPi w, Matrix.nonsing_inv_mul_cancel_left _ _ (hgu w), hPi' w, Matrix.nonsing_inv_mul _ (hgu' w), Matrix.mul_one]`. Take `⟨hd, hz, h⟩` from `HasCov.of_det φ hdetpos.ne' hmem hcov`. Use `⟨hd, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[h, abs_of_pos hdetpos, hdetφ, covAt_latAt E hE Λ P c hP hc hΛ g hg, covAt_latAt E hE Λ' P' c' hP' hc' hΛ' g' hg']`.

Establish `hv : 0 < Formalism.HermitianLatticesTheory.vInv E`. Unfold `Formalism.HermitianLatticesTheory.vInv`. Establish `: (0 : ℝ) < |(discr E : ℝ)|` using `abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero E))`. Check the signs of the components of the expression. Establish `hN : ∀ a : FractionalIdeal (𝓞 E)⁰ E, a ≠ 0 → (0 : ℝ) < (FractionalIdeal.absNorm a : ℝ)`.

Introduce `a ha`. Conclude with `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg a) (Ne.symm ((FractionalIdeal.absNorm_eq_zero_iff).not.2 ha))` after adjusting the coercions. Establish `hA` using `Finset.prod_pos fun i (_ : i ∈ Finset.univ) => hN _ (hc i)`. Establish `hB` using `Finset.prod_pos fun k (_ : k ∈ Finset.univ) => hN _ (hc' k)`. Simplify using `only [Fintype.prod_prod_type, map_div₀, Rat.cast_div, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_prod, Finset.prod_pow]`.

Establish `hDa' : (∏ w : InfinitePlace E, ‖(P.map w.embedding * Matrix.of (g w)).det‖) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun w _ => norm_ne_zero_iff.2 (by`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (det_map_ne_zero E hP w) (det_ne_zero_of_detNorm E hg w))`. Establish `hDb' : (∏ w : InfinitePlace E, ‖(P'.map w.embedding * Matrix.of (g' w)).det‖) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun w _ => norm_ne_zero_iff.2 (by`. Rewrite using `[Matrix.det_mul]`.

Conclude with `mul_ne_zero (det_map_ne_zero E hP' w) (det_ne_zero_of_detNorm E hg' w))`. Establish `hA'` using `hA.ne'`. Establish `hB'` using `hB.ne'`. Establish `hv'` using `hv.ne'`. Rewrite using `[← pow_mul, ← pow_mul]`.

Conclude with `homCovolume_eq_mul_pow _ _ _ _ _ _ _ _ hA' hB' hv' hDa' hDb'`.
-/
theorem homCovolume : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (r s : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin s → E)), Submodule.IsLattice E Λ → Submodule.IsLattice E Λ' → ∀ (g : MatInf E r) (g' : MatInf E s), 0 < detNorm E r g → 0 < detNorm E s g' → ∀ L : Submodule ℤ (InfinitePlace E → Fin r → Fin s → ℂ), (∀ z, z ∈ L ↔ ∃ T : Matrix (Fin r) (Fin s) E, (∀ y ∈ Λ', T *ᵥ y ∈ Λ) ∧ ∀ w, Matrix.of (z w) = (Matrix.of (g w))⁻¹ * T.map w.embedding * Matrix.of (g' w)) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = covAt E r (latAt E r Λ g) ^ s * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * s) / covAt E s (latAt E s Λ' g')) ^ r := by
  classical
  intro E _ _ hE r s Λ Λ' hΛl hΛ'l g g' hg hg' L hL
  obtain ⟨P, c, hP, hc, hΛ⟩ := exists_coords E Λ hΛl
  obtain ⟨P', c', hP', hc', hΛ'⟩ := exists_coords E Λ' hΛ'l
  obtain ⟨L₀, hL₀, hcov⟩ := hasCov_mat E hE (fun p : Fin r × Fin s => c p.1 / c' p.2)
    (fun p => div_ne_zero (hc p.1) (hc' p.2))
  have hgu : ∀ w, IsUnit (Matrix.of (g w)).det := fun w => isUnit_iff_ne_zero.2 (det_ne_zero_of_detNorm E hg w)
  have hgu' : ∀ w, IsUnit (Matrix.of (g' w)).det := fun w =>
    isUnit_iff_ne_zero.2 (det_ne_zero_of_detNorm E hg' w)

  have hPi : ∀ (w : InfinitePlace E) {n : Type} [Fintype n] (X : Matrix (Fin r) n ℂ),
      P⁻¹.map w.embedding * (P.map w.embedding * X) = X := by
    intro w n _ X
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  have hPi' : ∀ (w : InfinitePlace E) {n : Type} [Fintype n] (X : Matrix (Fin s) n ℂ),
      P'⁻¹.map w.embedding * (P'.map w.embedding * X) = X := by
    intro w n _ X
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP'),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

  let f : InfinitePlace E → (Fin r → Fin s → ℂ) →ₗ[ℂ] (Fin r → Fin s → ℂ) := fun w =>
    { toFun := fun T => P.map w.embedding * Matrix.of (g w) * Matrix.of T *
        ((Matrix.of (g' w))⁻¹ * P'⁻¹.map w.embedding)
      map_add' := fun T U => by
        rw [show Matrix.of (T + U) = Matrix.of T + Matrix.of U from rfl, Matrix.mul_add, Matrix.add_mul]
        rfl
      map_smul' := fun a T => by
        rw [show Matrix.of (a • T) = a • Matrix.of T from rfl, Matrix.mul_smul, Matrix.smul_mul,
          RingHom.id_apply]
        rfl }
  let φ : (InfinitePlace E → Fin r → Fin s → ℂ) →ₗ[ℝ] (InfinitePlace E → Fin r → Fin s → ℂ) :=
    LinearMap.pi fun w => ((f w).restrictScalars ℝ) ∘ₗ LinearMap.proj w
  have hφ : ∀ z w, Matrix.of (φ z w) = P.map w.embedding * Matrix.of (g w) * Matrix.of (z w) *
      ((Matrix.of (g' w))⁻¹ * P'⁻¹.map w.embedding) := fun z w => rfl
  have hB1 : ∀ w, ((Matrix.of (g' w))⁻¹ * P'⁻¹.map w.embedding).det *
      (P'.map w.embedding * Matrix.of (g' w)).det = 1 := by
    intro w
    rw [← Matrix.det_mul, Matrix.mul_assoc, hPi' w, Matrix.nonsing_inv_mul _ (hgu' w), Matrix.det_one]
  have hdetφ : LinearMap.det φ = (∏ w, ‖(P.map w.embedding * Matrix.of (g w)).det‖ ^ 2) ^ s *
      ((∏ w, ‖(P'.map w.embedding * Matrix.of (g' w)).det‖ ^ 2)⁻¹) ^ r := by
    rw [LinearMap.det_pi, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [LinearMap.det_restrictScalars, det_mul_mul _ _ (f w) (fun T => rfl), Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, norm_mul, norm_pow, norm_pow,
      eq_inv_of_mul_eq_one_left (by rw [← norm_mul, hB1 w, norm_one] :
        ‖((Matrix.of (g' w))⁻¹ * P'⁻¹.map w.embedding).det‖ *
          ‖(P'.map w.embedding * Matrix.of (g' w)).det‖ = 1)]
    ring
  have hpos : ∀ {n : ℕ} (Q : Matrix (Fin n) (Fin n) E) (h : MatInf E n), Q.det ≠ 0 → 0 < detNorm E n h →
      0 < ∏ w, ‖(Q.map w.embedding * Matrix.of (h w)).det‖ ^ 2 := by
    intro n Q h hQ hh
    refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) 2
    rw [Matrix.det_mul]
    exact mul_ne_zero (det_map_ne_zero E hQ w) (det_ne_zero_of_detNorm E hh w)
  have hDa := hpos P g hP hg
  have hDb := hpos P' g' hP' hg'
  have hdetpos : 0 < LinearMap.det φ := by
    rw [hdetφ]
    exact mul_pos (pow_pos hDa _) (pow_pos (inv_pos.2 hDb) _)
  have hmem : ∀ z, z ∈ L ↔ φ z ∈ L₀ := by
    intro z
    rw [hL, hL₀]
    constructor
    · rintro ⟨T, hT, hz⟩ p
      refine ⟨(P * T * P'⁻¹) p.1 p.2, (maps_iff E Λ Λ' P c hΛ P' c' hP' hc' hΛ' T).1 hT p.1 p.2,
        fun w => ?_⟩
      have hw : Matrix.of (φ z w) = (P * T * P'⁻¹).map w.embedding := by
        rw [hφ, hz w, Matrix.map_mul, Matrix.map_mul]
        simp only [Matrix.mul_assoc]
        rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hgu' w), Matrix.mul_nonsing_inv_cancel_left _ _ (hgu w)]
      exact congrFun (congrFun hw p.1) p.2
    · intro h
      choose y hy hyw using h
      refine ⟨P⁻¹ * Matrix.of (fun i k => y (i, k)) * P', ?_, fun w => ?_⟩
      · have hM : P * (P⁻¹ * Matrix.of (fun i k => y (i, k)) * P') * P'⁻¹ = Matrix.of (fun i k => y (i, k)) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP),
            Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP'), Matrix.mul_one]
        refine (maps_iff E Λ Λ' P c hΛ P' c' hP' hc' hΛ' _).2 fun i k => ?_
        rw [hM]
        exact hy (i, k)
      · have hM : (Matrix.of (fun i k => y (i, k))).map w.embedding = Matrix.of (φ z w) := by
          ext i k
          exact (hyw (i, k) w).symm
        rw [Matrix.map_mul, Matrix.map_mul, hM, hφ]
        simp only [Matrix.mul_assoc]
        rw [hPi w, Matrix.nonsing_inv_mul_cancel_left _ _ (hgu w), hPi' w, Matrix.nonsing_inv_mul _ (hgu' w),
          Matrix.mul_one]
  obtain ⟨hd, hz, h⟩ := HasCov.of_det φ hdetpos.ne' hmem hcov
  refine ⟨hd, hz, ?_⟩
  rw [h, abs_of_pos hdetpos, hdetφ, covAt_latAt E hE Λ P c hP hc hΛ g hg,
    covAt_latAt E hE Λ' P' c' hP' hc' hΛ' g' hg']
  have hv : 0 < Formalism.HermitianLatticesTheory.vInv E := by
    unfold Formalism.HermitianLatticesTheory.vInv
    have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero E))
    positivity
  have hN : ∀ a : FractionalIdeal (𝓞 E)⁰ E, a ≠ 0 → (0 : ℝ) < (FractionalIdeal.absNorm a : ℝ) := by
    intro a ha
    exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg a)
      (Ne.symm ((FractionalIdeal.absNorm_eq_zero_iff).not.2 ha))
  have hA := Finset.prod_pos fun i (_ : i ∈ Finset.univ) => hN _ (hc i)
  have hB := Finset.prod_pos fun k (_ : k ∈ Finset.univ) => hN _ (hc' k)
  simp only [Fintype.prod_prod_type, map_div₀, Rat.cast_div, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_prod, Finset.prod_pow]
  have hDa' : (∏ w : InfinitePlace E, ‖(P.map w.embedding * Matrix.of (g w)).det‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => norm_ne_zero_iff.2 (by
      rw [Matrix.det_mul]; exact mul_ne_zero (det_map_ne_zero E hP w) (det_ne_zero_of_detNorm E hg w))
  have hDb' : (∏ w : InfinitePlace E, ‖(P'.map w.embedding * Matrix.of (g' w)).det‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => norm_ne_zero_iff.2 (by
      rw [Matrix.det_mul]; exact mul_ne_zero (det_map_ne_zero E hP' w) (det_ne_zero_of_detNorm E hg' w))
  have hA' := hA.ne'
  have hB' := hB.ne'
  have hv' := hv.ne'
  rw [← pow_mul, ← pow_mul]
  exact homCovolume_eq_mul_pow _ _ _ _ _ _ _ _ hA' hB' hv' hDa' hDb'

end GlobalTheory.HomCovolume

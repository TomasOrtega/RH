import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Establish `hzy : z y = e' y` using `he' hy'`. Establish `hzy2 : z y = e y` using `he hy`. Establish `hopen : IsOpen (e.target ∩ (e'.target ∩ e'.symm ⁻¹' e.source))` using `e.open_target.inter (e'.isOpen_inter_preimage_symm e.open_source)`. Establish `hmem : z y ∈ e.target ∩ (e'.target ∩ e'.symm ⁻¹' e.source)`. Use `⟨by rw [hzy2]; exact e.map_source hy, by rw [hzy]; exact e'.map_source hy', ?_⟩` and prove the remaining obligations.

Use `show e'.symm (z y) ∈ e.source`. Rewrite using `[hzy, e'.left_inv hy']`. Conclude with `hy`. Use `filter_upwards [hopen.mem_nhds hmem] with w hw`. Take `⟨_, hw2, hw3⟩` from `hw`.

Establish `ha : e'.symm w ∈ e'.source` using `e'.map_target hw2`. Establish `hea : e (e'.symm w) = w`. Rewrite using `[← he hw3, he' ha, e'.right_inv hw2]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem coe_symm_apply_of_isChart_val {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (y : M) (hy : y ∈ e.source) (hy' : y ∈ e'.source) :
    e'.symm =ᶠ[𝓝 (z y)] e.symm := by

  have hzy : z y = e' y := he' hy'
  have hzy2 : z y = e y := he hy
  have hopen : IsOpen (e.target ∩ (e'.target ∩ e'.symm ⁻¹' e.source)) :=
    e.open_target.inter (e'.isOpen_inter_preimage_symm e.open_source)
  have hmem : z y ∈ e.target ∩ (e'.target ∩ e'.symm ⁻¹' e.source) := by
    refine ⟨by rw [hzy2]; exact e.map_source hy, by rw [hzy]; exact e'.map_source hy', ?_⟩
    show e'.symm (z y) ∈ e.source
    rw [hzy, e'.left_inv hy']
    exact hy
  filter_upwards [hopen.mem_nhds hmem] with w hw
  obtain ⟨_, hw2, hw3⟩ := hw
  have ha : e'.symm w ∈ e'.source := e'.map_target hw2
  have hea : e (e'.symm w) = w := by
    rw [← he hw3, he' ha, e'.right_inv hw2]
  calc e'.symm w = e.symm (e (e'.symm w)) := (e.left_inv hw3).symm
    _ = e.symm w := by rw [hea]

/- English proof (translation)
Unfold `wdb`. Rewrite using `[h.fderiv_eq]`.
-/
private theorem wdb_apply_congr_of_eventuallyEq (n : ℕ) (k : Fin n) {F G : V n → ℂ} {p : V n} (h : F =ᶠ[𝓝 p] G) :
    wdb n k F p = wdb n k G p := by
  unfold wdb
  rw [h.fderiv_eq]

/- English proof (translation)
Unfold `wd`. Rewrite using `[h.fderiv_eq]`.
-/
private theorem wd_apply_congr_of_eventuallyEq (n : ℕ) (k : Fin n) {F G : V n → ℂ} {p : V n} (h : F =ᶠ[𝓝 p] G) :
    wd n k F p = wd n k G p := by
  unfold wd
  rw [h.fderiv_eq]

/- English proof (translation)
Establish `hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source` using `⟨e, he, hy⟩`. Unfold `db`. Rewrite using `[dif_pos hex]`. Apply `wdb_apply_congr_of_eventuallyEq` to reduce the goal to its premises. Conclude with `(coe_symm_apply_of_isChart_val n z e (Classical.choose hex) he (Classical.choose_spec hex).1 y hy (Classical.choose_spec hex).2).fun_comp f`.
-/
private theorem db_apply_eq_wdb_of_mem_source {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : db n z k f y = wdb n k (f ∘ e.symm) (z y) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  unfold db
  rw [dif_pos hex]
  apply wdb_apply_congr_of_eventuallyEq
  exact (coe_symm_apply_of_isChart_val n z e (Classical.choose hex) he (Classical.choose_spec hex).1 y hy
    (Classical.choose_spec hex).2).fun_comp f

/- English proof (translation)
Establish `hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source` using `⟨e, he, hy⟩`. Unfold `d`. Rewrite using `[dif_pos hex]`. Apply `wd_apply_congr_of_eventuallyEq` to reduce the goal to its premises. Conclude with `(coe_symm_apply_of_isChart_val n z e (Classical.choose hex) he (Classical.choose_spec hex).1 y hy (Classical.choose_spec hex).2).fun_comp f`.
-/
private theorem d_apply_eq_wd_of_mem_source {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : d n z k f y = wd n k (f ∘ e.symm) (z y) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  unfold d
  rw [dif_pos hex]
  apply wd_apply_congr_of_eventuallyEq
  exact (coe_symm_apply_of_isChart_val n z e (Classical.choose hex) he (Classical.choose_spec hex).1 y hy
    (Classical.choose_spec hex).2).fun_comp f

/- English proof (translation)
Introduce `w hw`. Simplify using `only [Function.comp_apply]`. Rewrite using `[he (e.map_target hw), e.right_inv hw]`.
-/
theorem leviZ_coord_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (l : Fin n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    EqOn ((fun y => z y l) ∘ e.symm) (fun w : V n => w l) e.target := by
  intro w hw
  simp only [Function.comp_apply]
  rw [he (e.map_target hw), e.right_inv hw]

/- English proof (translation)
Establish `hL : fderiv ℝ (fun w : V n => w l) y = ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)` using `((EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ).fderiv`. Unfold `wd`. Rewrite using `[hL]`. Distinguish the cases in `h : j = l`. Substitute `h` using the available equality.

Simplify using `[bas, EuclideanSpace.single_apply, Complex.I_mul_I]`. Simplify using `[bas, EuclideanSpace.single_apply, h, Ne.symm h]`.
-/
theorem leviZ_wd_coord (n : ℕ) (j l : Fin n) (y : V n) :
    wd n j (fun w : V n => w l) y = if j = l then 1 else 0 := by
  have hL : fderiv ℝ (fun w : V n => w l) y =
      ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) :=
    ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ).fderiv
  unfold wd
  rw [hL]
  by_cases h : j = l
  · subst h
    simp [bas, EuclideanSpace.single_apply, Complex.I_mul_I]
  · simp [bas, EuclideanSpace.single_apply, h, Ne.symm h]

/- English proof (translation)
Take `⟨e, hx, hze⟩` from `hz x`. Establish `he : IsChart n z e` using `fun y _ => congrFun hze y`. Establish `hzx : z x ∈ e.target` using `by rw [he hx]; exact e.map_source hx`. Rewrite using `[d_apply_eq_wd_of_mem_source n z j _ e he x hx, wd_apply_congr_of_eventuallyEq n j (G := fun w : V n => w l) (by filter_upwards [e.open_target.mem_nhds hzx] with w hw`. Conclude with `leviZ_coord_chart n z l e he hw)]`.

Conclude with `leviZ_wd_coord n j l (z x)`.
-/
theorem leviZ_d_coord {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j l : Fin n) (x : M) :
    d n z j (fun y => z y l) x = if j = l then 1 else 0 := by
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => congrFun hze y
  have hzx : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  rw [d_apply_eq_wd_of_mem_source n z j _ e he x hx,
    wd_apply_congr_of_eventuallyEq n j (G := fun w : V n => w l) (by
      filter_upwards [e.open_target.mem_nhds hzx] with w hw
      exact leviZ_coord_chart n z l e he hw)]
  exact leviZ_wd_coord n j l (z x)

/- English proof (translation)
Establish `hP : ∀ l, HasFDerivAt (fun w : V n => w l) ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) p` using `fun l => (EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ`. Establish `hC : ∀ l, HasFDerivAt (fun w : V n => conj (w l)) (Complex.conjCLE.toContinuousLinearMap.comp ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)) p` using `fun l => Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p (hP l)`. Establish `hF : HasFDerivAt (fun w : V n => ∑ l, w l * conj (w l)) (∑ l, (p l • Complex.conjCLE.toContinuousLinearMap.comp ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) + conj (p l) • (EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)) p` using `HasFDerivAt.fun_sum (fun l _ => (hP l).mul (hC l))`. Unfold `wdb`. Rewrite using `[hF.fderiv]`.

Simplify using `[bas, EuclideanSpace.single_apply]`. Simplify using `only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, Complex.conj_I, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Take the linear combination `((starRingEnd ℂ (p.ofLp k) - p.ofLp k) / 2) * Complex.I_sq`.
-/
private theorem wdb_sum_mul_conj_eq_coord (n : ℕ) (k : Fin n) (p : V n) :
    wdb n k (fun w : V n => ∑ l, w l * conj (w l)) p = p k := by
  have hP : ∀ l, HasFDerivAt (fun w : V n => w l)
      ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) p :=
    fun l => (EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ
  have hC : ∀ l, HasFDerivAt (fun w : V n => conj (w l))
      (Complex.conjCLE.toContinuousLinearMap.comp
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)) p :=
    fun l => Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p (hP l)
  have hF : HasFDerivAt (fun w : V n => ∑ l, w l * conj (w l))
      (∑ l, (p l • Complex.conjCLE.toContinuousLinearMap.comp
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) +
        conj (p l) • (EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)) p :=
    HasFDerivAt.fun_sum (fun l _ => (hP l).mul (hC l))
  unfold wdb
  rw [hF.fderiv]
  simp [bas, EuclideanSpace.single_apply]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, Complex.conj_I,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linear_combination ((starRingEnd ℂ (p.ofLp k) - p.ofLp k) / 2) * Complex.I_sq

/- English proof (translation)
Introduce `z hz`. Establish `hchart : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source`. Introduce `x`. Take `⟨e, hx, hze⟩` from `hz x`. Conclude with `⟨e, fun y _ => congrFun hze y, hx⟩`.

Establish `hloc : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e → EqOn ((fun y => ((‖z y‖ ^ 2 : ℝ) : ℂ)) ∘ e.symm) (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) e.target`. Introduce `e he w hw`. Simplify using `only [Function.comp_apply]`. Rewrite using `[he (e.map_target hw), e.right_inv hw]`. Establish `hsq : (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) = fun w => ∑ l, w l * conj (w l)`.

Use function extensionality and compare the values at `w`. Rewrite using `[EuclideanSpace.norm_sq_eq]`. Use `push_cast`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Simplify using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `⟨fun e he => ?_, fun x ξ => ?_⟩` and prove the remaining obligations. Establish `hsm : ContDiffOn ℝ ∞ (fun w : V n => ∑ l, w l * conj (w l)) e.target`. Use `ContDiffOn.sum (fun l _ => ?_)` and prove the remaining obligations. Establish `hPc : ContDiff ℝ ∞ (fun w : V n => w l)` using `((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ).contDiff`. Establish `hCc : ContDiff ℝ ∞ (fun w : V n => conj (w l))` using `(Complex.conjCLE.toContinuousLinearMap.comp ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)).contDiff`.

Conclude with `(hPc.mul hCc).contDiffOn`. Rewrite `hsm` using `[← hsq]`. Conclude with `hsm.congr (hloc e he)`. Establish `hdb : ∀ k, db n z k (fun y => ((‖z y‖ ^ 2 : ℝ) : ℂ)) = fun y => z y k`. Introduce `k`.

Use function extensionality and compare the values at `y`. Take `⟨e, he, hy⟩` from `hchart y`. Establish `hzy : z y ∈ e.target` using `by rw [he hy]; exact e.map_source hy`. Rewrite using `[db_apply_eq_wdb_of_mem_source n z k _ e he y hy, wdb_apply_congr_of_eventuallyEq n k (G := fun w : V n => ∑ l, w l * conj (w l)) (by`. Rewrite using `[← hsq]`.

Use `filter_upwards [e.open_target.mem_nhds hzy] with w hw`. Conclude with `hloc e he hw)]`. Conclude with `wdb_sum_mul_conj_eq_coord n k (z y)`. Simplify using `only [Levi, hdb, leviZ_d_coord n z hz]`. Rewrite using `[Complex.ofReal_sum]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j]`. Simplify using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Introduce `k _ hkj`. Simplify using `[Ne.symm hkj]`.

Simplify using the standard rewrite rules.
-/
theorem leviNormSq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : LeviNormSqStatement n M := by
  intro z hz
  have hchart : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := by
    intro x
    obtain ⟨e, hx, hze⟩ := hz x
    exact ⟨e, fun y _ => congrFun hze y, hx⟩

  have hloc : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      EqOn ((fun y => ((‖z y‖ ^ 2 : ℝ) : ℂ)) ∘ e.symm) (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ))
        e.target := by
    intro e he w hw
    simp only [Function.comp_apply]
    rw [he (e.map_target hw), e.right_inv hw]
  have hsq : (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) = fun w => ∑ l, w l * conj (w l) := by
    funext w
    rw [EuclideanSpace.norm_sq_eq]
    push_cast
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine ⟨fun e he => ?_, fun x ξ => ?_⟩
  · have hsm : ContDiffOn ℝ ∞ (fun w : V n => ∑ l, w l * conj (w l)) e.target := by
      refine ContDiffOn.sum (fun l _ => ?_)
      have hPc : ContDiff ℝ ∞ (fun w : V n => w l) :=
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ).contDiff
      have hCc : ContDiff ℝ ∞ (fun w : V n => conj (w l)) :=
        (Complex.conjCLE.toContinuousLinearMap.comp
          ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)).contDiff
      exact (hPc.mul hCc).contDiffOn
    rw [← hsq] at hsm
    exact hsm.congr (hloc e he)
  ·
    have hdb : ∀ k, db n z k (fun y => ((‖z y‖ ^ 2 : ℝ) : ℂ)) = fun y => z y k := by
      intro k
      funext y
      obtain ⟨e, he, hy⟩ := hchart y
      have hzy : z y ∈ e.target := by rw [he hy]; exact e.map_source hy
      rw [db_apply_eq_wdb_of_mem_source n z k _ e he y hy,
        wdb_apply_congr_of_eventuallyEq n k (G := fun w : V n => ∑ l, w l * conj (w l)) (by
          rw [← hsq]
          filter_upwards [e.open_target.mem_nhds hzy] with w hw
          exact hloc e he hw)]
      exact wdb_sum_mul_conj_eq_coord n k (z y)
    simp only [Levi, hdb, leviZ_d_coord n z hz]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · intro k _ hkj
      simp [Ne.symm hkj]
    · simp

end

end ReciprocityTheory.L2DbarEstimates.F

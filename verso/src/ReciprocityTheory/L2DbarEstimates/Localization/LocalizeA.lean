import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Use `⟨fun x => ?_⟩` and prove the remaining obligations. Take `⟨e, hx, -⟩` from `hz x`. Establish `ht : e x ∈ e.target` using `e.map_source hx`. Take `⟨r, hr, hsub⟩` from `Metric.isOpen_iff.mp e.open_target (e x) ht`. Use `⟨e.symm '' Metric.closedBall (e x) (r / 2), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono ((Metric.closedBall_subset_ball (by linarith)).trans hsub))`. Establish `h1 : e.source ∩ e ⁻¹' Metric.ball (e x) (r / 2) ∈ 𝓝 x` using `(e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨hx, Metric.mem_ball_self (by linarith)⟩`. Use `Filter.mem_of_superset h1 ?_` and prove the remaining obligations. Introduce and unpack `y ⟨hy1, hy2⟩`. Conclude with `⟨e y, Metric.ball_subset_closedBall hy2, e.left_inv hy1⟩`.
-/
theorem loc_weaklyLocallyCompact {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) : WeaklyLocallyCompactSpace M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨e, hx, -⟩ := hz x
  have ht : e x ∈ e.target := e.map_source hx
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) ht
  refine ⟨e.symm '' Metric.closedBall (e x) (r / 2), ?_, ?_⟩
  · exact (isCompact_closedBall _ _).image_of_continuousOn
      (e.continuousOn_symm.mono ((Metric.closedBall_subset_ball (by linarith)).trans hsub))
  · have h1 : e.source ∩ e ⁻¹' Metric.ball (e x) (r / 2) ∈ 𝓝 x :=
      (e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨hx, Metric.mem_ball_self (by linarith)⟩
    refine Filter.mem_of_superset h1 ?_
    rintro y ⟨hy1, hy2⟩
    exact ⟨e y, Metric.ball_subset_closedBall hy2, e.left_inv hy1⟩

/- English proof (translation)
Distinguish the cases in `hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source`. Simplify using `only [d, dif_pos hc] set e := Classical.choose hc with he_def`. Establish `he : IsChart n z e ∧ x ∈ e.source` using `Classical.choose_spec hc`. Establish `hzx : z x = e x` using `he.1 he.2`. Establish `ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x)` using `by first`.

Consider the case `exact e.tendsto_symm he.2`. Consider the case `(have hc' : Tendsto e.symm (𝓝 (e x)) (𝓝 (e.symm (e x))) := e.continuousAt_symm (e.map_source he.2)`. Rewrite using `[e.left_inv he.2] at hc')` and apply the resulting hypothesis. Establish `hfg : f ∘ e.symm =ᶠ[𝓝 (z x)] g ∘ e.symm`. Rewrite using `[hzx]`.

Conclude with `ht.eventually h`. Unfold `wd`. Rewrite using `[hfg.fderiv_eq]`. Simplify using `only [d, dif_neg hc]`.
-/
theorem loc_d_congr {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (x : M) (h : f =ᶠ[𝓝 x] g) :
    d n z j f x = d n z j g x := by
  by_cases hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [d, dif_pos hc]
    set e := Classical.choose hc with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hc
    have hzx : z x = e x := he.1 he.2
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      first
      | exact e.tendsto_symm he.2
      | (have hc' : Tendsto e.symm (𝓝 (e x)) (𝓝 (e.symm (e x))) := e.continuousAt_symm (e.map_source he.2)
         rwa [e.left_inv he.2] at hc')
    have hfg : f ∘ e.symm =ᶠ[𝓝 (z x)] g ∘ e.symm := by
      rw [hzx]
      exact ht.eventually h
    unfold wd
    rw [hfg.fderiv_eq]
  · simp only [d, dif_neg hc]

/- English proof (translation)
Distinguish the cases in `hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source`. Simplify using `only [db, dif_pos hc] set e := Classical.choose hc with he_def`. Establish `he : IsChart n z e ∧ x ∈ e.source` using `Classical.choose_spec hc`. Establish `hzx : z x = e x` using `he.1 he.2`. Establish `ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x)` using `by first`.

Consider the case `exact e.tendsto_symm he.2`. Consider the case `(have hc' : Tendsto e.symm (𝓝 (e x)) (𝓝 (e.symm (e x))) := e.continuousAt_symm (e.map_source he.2)`. Rewrite using `[e.left_inv he.2] at hc')` and apply the resulting hypothesis. Establish `hfg : f ∘ e.symm =ᶠ[𝓝 (z x)] g ∘ e.symm`. Rewrite using `[hzx]`.

Conclude with `ht.eventually h`. Unfold `wdb`. Rewrite using `[hfg.fderiv_eq]`. Simplify using `only [db, dif_neg hc]`.
-/
theorem loc_db_congr {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (x : M) (h : f =ᶠ[𝓝 x] g) :
    db n z j f x = db n z j g x := by
  by_cases hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [db, dif_pos hc]
    set e := Classical.choose hc with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hc
    have hzx : z x = e x := he.1 he.2
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      first
      | exact e.tendsto_symm he.2
      | (have hc' : Tendsto e.symm (𝓝 (e x)) (𝓝 (e.symm (e x))) := e.continuousAt_symm (e.map_source he.2)
         rwa [e.left_inv he.2] at hc')
    have hfg : f ∘ e.symm =ᶠ[𝓝 (z x)] g ∘ e.symm := by
      rw [hzx]
      exact ht.eventually h
    unfold wdb
    rw [hfg.fderiv_eq]
  · simp only [db, dif_neg hc]

/- English proof (translation)
Unfold `Ck at hf ⊢`. Introduce `e he`. Conclude with `(ContDiffOn.sum fun i _ => hf i e he : ContDiffOn ℝ _ (fun y => ∑ i ∈ s, (f i ∘ e.symm) y) e.target)`.
-/
theorem loc_ck_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, Ck n z k (f i)) :
    Ck n z k (fun x => ∑ i ∈ s, f i x) := by
  unfold Ck at hf ⊢
  intro e he
  exact (ContDiffOn.sum fun i _ => hf i e he :
    ContDiffOn ℝ _ (fun y => ∑ i ∈ s, (f i ∘ e.symm) y) e.target)

/- English proof (translation)
Distinguish the cases in `hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source`. Simplify using `only [d, dif_pos hc] set e := Classical.choose hc with he_def`. Establish `he : IsChart n z e ∧ x ∈ e.source` using `Classical.choose_spec hc`. Establish `hdiff : ∀ i ∈ s, DifferentiableAt ℝ (f i ∘ e.symm) (z x)`. Introduce `i _`.

Rewrite using `[he.1 he.2]`. Apply the tactic sequence `exact ((hf i e he.1).contDiffAt (e.open_target.mem_nhds (e.map_source he.2))).differentiableAt (by first | simp | norm_num | exact le_rfl)`. Establish `hsum : ((fun y => ∑ i ∈ s, f i y) ∘ e.symm) = fun y => ∑ i ∈ s, (f i ∘ e.symm) y` using `rfl`. Unfold `wd`. Apply the tactic sequence `(first | rw [hsum, fderiv_fun_sum hdiff] | rw [hsum, ← Finset.sum_fn, fderiv_sum hdiff])`.

Establish `key : ∀ L : ι → (V n →L[ℝ] ℂ), ((∑ i ∈ s, L i) (bas n j) - Complex.I * (∑ i ∈ s, L i) (Complex.I • bas n j)) / 2 = ∑ i ∈ s, (L i (bas n j) - Complex.I * L i (Complex.I • bas n j)) / 2`. Introduce `L`. Simplify using `only [ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]`. Conclude with `key _`. Simplify using `only [d, dif_neg hc, Finset.sum_const_zero]`.
-/
theorem loc_d_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, Ck n z 1 (f i)) (j : Fin n) (x : M) :
    d n z j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, d n z j (f i) x := by
  by_cases hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [d, dif_pos hc]
    set e := Classical.choose hc with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hc
    have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (f i ∘ e.symm) (z x) := by
      intro i _
      rw [he.1 he.2]
      exact ((hf i e he.1).contDiffAt (e.open_target.mem_nhds (e.map_source he.2))).differentiableAt
        (by first | simp | norm_num | exact le_rfl)
    have hsum : ((fun y => ∑ i ∈ s, f i y) ∘ e.symm) = fun y => ∑ i ∈ s, (f i ∘ e.symm) y := rfl
    unfold wd
    (first | rw [hsum, fderiv_fun_sum hdiff] | rw [hsum, ← Finset.sum_fn, fderiv_sum hdiff])
    have key : ∀ L : ι → (V n →L[ℝ] ℂ), ((∑ i ∈ s, L i) (bas n j) - Complex.I * (∑ i ∈ s, L i) (Complex.I • bas n j)) / 2 =
        ∑ i ∈ s, (L i (bas n j) - Complex.I * L i (Complex.I • bas n j)) / 2 := by
      intro L
      simp only [ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact key _
  · simp only [d, dif_neg hc, Finset.sum_const_zero]

/- English proof (translation)
Distinguish the cases in `hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source`. Simplify using `only [db, dif_pos hc] set e := Classical.choose hc with he_def`. Establish `he : IsChart n z e ∧ x ∈ e.source` using `Classical.choose_spec hc`. Establish `hdiff : ∀ i ∈ s, DifferentiableAt ℝ (f i ∘ e.symm) (z x)`. Introduce `i _`.

Rewrite using `[he.1 he.2]`. Apply the tactic sequence `exact ((hf i e he.1).contDiffAt (e.open_target.mem_nhds (e.map_source he.2))).differentiableAt (by first | simp | norm_num | exact le_rfl)`. Establish `hsum : ((fun y => ∑ i ∈ s, f i y) ∘ e.symm) = fun y => ∑ i ∈ s, (f i ∘ e.symm) y` using `rfl`. Unfold `wdb`. Apply the tactic sequence `(first | rw [hsum, fderiv_fun_sum hdiff] | rw [hsum, ← Finset.sum_fn, fderiv_sum hdiff])`.

Establish `key : ∀ L : ι → (V n →L[ℝ] ℂ), ((∑ i ∈ s, L i) (bas n j) + Complex.I * (∑ i ∈ s, L i) (Complex.I • bas n j)) / 2 = ∑ i ∈ s, (L i (bas n j) + Complex.I * L i (Complex.I • bas n j)) / 2`. Introduce `L`. Simplify using `only [ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]`. Conclude with `key _`. Simplify using `only [db, dif_neg hc, Finset.sum_const_zero]`.
-/
theorem loc_db_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, Ck n z 1 (f i)) (j : Fin n) (x : M) :
    db n z j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, db n z j (f i) x := by
  by_cases hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [db, dif_pos hc]
    set e := Classical.choose hc with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hc
    have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (f i ∘ e.symm) (z x) := by
      intro i _
      rw [he.1 he.2]
      exact ((hf i e he.1).contDiffAt (e.open_target.mem_nhds (e.map_source he.2))).differentiableAt
        (by first | simp | norm_num | exact le_rfl)
    have hsum : ((fun y => ∑ i ∈ s, f i y) ∘ e.symm) = fun y => ∑ i ∈ s, (f i ∘ e.symm) y := rfl
    unfold wdb
    (first | rw [hsum, fderiv_fun_sum hdiff] | rw [hsum, ← Finset.sum_fn, fderiv_sum hdiff])
    have key : ∀ L : ι → (V n →L[ℝ] ℂ), ((∑ i ∈ s, L i) (bas n j) + Complex.I * (∑ i ∈ s, L i) (Complex.I • bas n j)) / 2 =
        ∑ i ∈ s, (L i (bas n j) + Complex.I * L i (Complex.I • bas n j)) / 2 := by
      intro L
      simp only [ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    exact key _
  · simp only [db, dif_neg hc, Finset.sum_const_zero]

/- English proof (translation)
Establish `h1 : ‖∑ i, a i‖ ≤ ∑ i, ‖a i‖` using `norm_sum_le _ _`. Establish `h2 : (∑ i, ‖a i‖) ^ 2 ≤ N * ∑ i, ‖a i‖ ^ 2` using `by first`. Consider the case `(have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => ‖a i‖)`. Simplify using `using h3)`. Consider the case `(have h3 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i‖)`.

Simplify using `using h3)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem loc_norm_sum_sq {E : Type*} [SeminormedAddCommGroup E] {N : ℕ} (a : Fin N → E) :
    ‖∑ i, a i‖ ^ 2 ≤ N * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i, a i‖ ≤ ∑ i, ‖a i‖ := norm_sum_le _ _
  have h2 : (∑ i, ‖a i‖) ^ 2 ≤ N * ∑ i, ‖a i‖ ^ 2 := by
    first
    | (have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
       simpa using h3)
    | (have h3 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i‖)
       simpa using h3)
  calc ‖∑ i, a i‖ ^ 2 ≤ (∑ i, ‖a i‖) ^ 2 := by gcongr
    _ ≤ N * ∑ i, ‖a i‖ ^ 2 := h2

/- English proof (translation)
Establish `h : ∀ j k, ‖∑ i, σ i j k‖ ^ 2 ≤ N * ∑ i, ‖σ i j k‖ ^ 2` using `fun j k => loc_norm_sum_sq (fun i => σ i j k)`. Establish `hs : ∑ i, ∑ j, ∑ k, ‖σ i j k‖ ^ 2 = ∑ j, ∑ k, ∑ i, ‖σ i j k‖ ^ 2`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_comm`. Simplify using `only [sq2]`.

Rewrite using `[← Finset.sum_div, ← mul_div_assoc, hs, Finset.mul_sum]`. Use `gcongr with j _`. Rewrite using `[Finset.mul_sum]`. Use `gcongr with k _`. Conclude with `h j k`.
-/
theorem two_form_sq_finset_sum_le {n N : ℕ} (σ : Fin N → Fin n → Fin n → ℂ) :
    sq2 n (fun j k => ∑ i, σ i j k) ≤ N * ∑ i, sq2 n (σ i) := by
  have h : ∀ j k, ‖∑ i, σ i j k‖ ^ 2 ≤ N * ∑ i, ‖σ i j k‖ ^ 2 := fun j k =>
    loc_norm_sum_sq (fun i => σ i j k)
  have hs : ∑ i, ∑ j, ∑ k, ‖σ i j k‖ ^ 2 = ∑ j, ∑ k, ∑ i, ‖σ i j k‖ ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  simp only [sq2]
  rw [← Finset.sum_div, ← mul_div_assoc, hs, Finset.mul_sum]
  gcongr with j _
  rw [Finset.mul_sum]
  gcongr with k _
  exact h j k

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)).mp h.2` as an intermediate fact. Simplify `this` using `[ENNReal.rpow_two]`. Introduce `h`.

Use `⟨hf, ?_⟩` and prove the remaining obligations. Use `(eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)).mpr ?_` and prove the remaining obligations. Simplify `h` using `[ENNReal.rpow_two]`.
-/
theorem loc_memLp_iff {M E : Type*} [MeasurableSpace M] [NormedAddCommGroup E] (ν : Measure M)
    (f : M → E) (hf : AEStronglyMeasurable f ν) :
    MemLp f 2 ν ↔ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν < ⊤ := by
  constructor
  · intro h
    have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)).mp h.2
    simpa [ENNReal.rpow_two] using this
  · intro h
    refine ⟨hf, ?_⟩
    refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)).mpr ?_
    simpa [ENNReal.rpow_two] using h

/- English proof (translation)
Use `⟨hf, fun C hC => ?_⟩` and prove the remaining obligations. Establish `m1 : MemLp g₁ 2 (μ.restrict C)` using `(loc_memLp_iff _ _ h₁.1.restrict).mpr (h₁.2 C hC)`. Establish `m2 : MemLp g₂ 2 (μ.restrict C)` using `(loc_memLp_iff _ _ h₂.1.restrict).mpr (h₂.2 C hC)`. Establish `m3 : MemLp (fun x => c * (‖g₁ x‖ + ‖g₂ x‖)) 2 (μ.restrict C)` using `(m1.norm.add m2.norm).const_mul c`. Establish `m4 : MemLp f 2 (μ.restrict C)` using `m3.of_le hf.restrict (Filter.Eventually.of_forall fun x => by show ‖f x‖ ≤ ‖c * (‖g₁ x‖ + ‖g₂ x‖)‖`.

Rewrite using `[Real.norm_eq_abs]`. Conclude with `(hle x).trans (le_abs_self _))`. Conclude with `(loc_memLp_iff _ _ hf.restrict).mp m4`.
-/
theorem locL2_of_le_sum {M E F₁ F₂ : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] (μ : Measure M)
    (f : M → E) (g₁ : M → F₁) (g₂ : M → F₂) (c : ℝ) (h₁ : LocalL2Isometry μ g₁) (h₂ : LocalL2Isometry μ g₂)
    (hf : AEStronglyMeasurable f μ) (hle : ∀ x, ‖f x‖ ≤ c * (‖g₁ x‖ + ‖g₂ x‖)) : LocalL2Isometry μ f := by
  refine ⟨hf, fun C hC => ?_⟩
  have m1 : MemLp g₁ 2 (μ.restrict C) := (loc_memLp_iff _ _ h₁.1.restrict).mpr (h₁.2 C hC)
  have m2 : MemLp g₂ 2 (μ.restrict C) := (loc_memLp_iff _ _ h₂.1.restrict).mpr (h₂.2 C hC)
  have m3 : MemLp (fun x => c * (‖g₁ x‖ + ‖g₂ x‖)) 2 (μ.restrict C) := (m1.norm.add m2.norm).const_mul c
  have m4 : MemLp f 2 (μ.restrict C) := m3.of_le hf.restrict (Filter.Eventually.of_forall fun x => by
    show ‖f x‖ ≤ ‖c * (‖g₁ x‖ + ‖g₂ x‖)‖
    rw [Real.norm_eq_abs]
    exact (hle x).trans (le_abs_self _))
  exact (loc_memLp_iff _ _ hf.restrict).mp m4

def locG {M : Type*} {n : ℕ} (η : M → ℝ) (G : M → V n) : M → V n :=
  fun x => (η x : ℂ) • G x

def locD {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ) (G : M → V n)
    (D : M → ℂ) : M → ℂ :=
  fun x => (η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j

def locS {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ) (G : M → V n)
    (S : M → Fin n → Fin n → ℂ) : M → Fin n → Fin n → ℂ :=
  fun x j k => (η x : ℂ) * S x j k +
    wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k

/- English proof (translation)
Use `first`. Consider the case `exact Finset.sum_apply j Finset.univ a`. Consider the case `simp [Finset.sum_apply]`. Consider the case `simp [WithLp.ofLp_sum]`. Consider the case `exact map_sum (EuclideanSpace.proj (𝕜 := ℂ) j) a Finset.univ`.

Consider the case `simpa using map_sum (EuclideanSpace.proj (𝕜 := ℂ) j) a Finset.univ`.
-/
theorem loc_sum_apply {n N : ℕ} (a : Fin N → V n) (j : Fin n) :
    (∑ i, a i) j = ∑ i, a i j := by
  first
  | exact Finset.sum_apply j Finset.univ a
  | simp [Finset.sum_apply]
  | simp [WithLp.ofLp_sum]
  | exact map_sum (EuclideanSpace.proj (𝕜 := ℂ) j) a Finset.univ
  | simpa using map_sum (EuclideanSpace.proj (𝕜 := ℂ) j) a Finset.univ

/- English proof (translation)
Use `closure_minimal (fun x hx => ?_) hT` and prove the remaining obligations. Assume the negation of the conclusion as `hxT`. Conclude with `hx (h x hxT)`.
-/
theorem loc_tsupport_sub {M E : Type*} [TopologicalSpace M] [Zero E] (f : M → E) (T : Set M)
    (hT : IsClosed T) (h : ∀ x, x ∉ T → f x = 0) : tsupport f ⊆ T := by
  refine closure_minimal (fun x hx => ?_) hT
  by_contra hxT
  exact hx (h x hxT)

/- English proof (translation)
Use `first`. Consider the case `(unfold wedge; fun_prop)`. Consider the case `(refine continuous_pi fun j => continuous_pi fun k => ?_`. Unfold `wedge`. Use the proof step `fun_prop)`.

Consider the case `(refine continuous_pi fun j => continuous_pi fun k => ?_`. Simplify using `only [wedge]`. Conclude with `(((continuous_apply j).comp continuous_fst).mul ((continuous_apply k).comp continuous_snd)).sub (((continuous_apply k).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)))`.
-/
theorem loc_continuous_wedge (n : ℕ) :
    Continuous (fun p : (Fin n → ℂ) × (Fin n → ℂ) => wedge p.1 p.2) := by
  first
  | (unfold wedge; fun_prop)
  | (refine continuous_pi fun j => continuous_pi fun k => ?_
     unfold wedge
     fun_prop)
  | (refine continuous_pi fun j => continuous_pi fun k => ?_
     simp only [wedge]
     exact (((continuous_apply j).comp continuous_fst).mul ((continuous_apply k).comp continuous_snd)).sub
       (((continuous_apply k).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)))

/- English proof (translation)
Use `show Continuous (fun σ : Fin n → Fin n → ℂ => (∑ j, ∑ k, ‖σ j k‖ ^ 2) / 2)`. Use `first`. Consider the case `fun_prop`. Consider the case `exact (continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun k _ => (((continuous_apply k).comp (continuous_apply j)).norm.pow 2)).div_const 2`.
-/
theorem continuous_two_form_norm_sq (n : ℕ) : Continuous (sq2 n) := by
  show Continuous (fun σ : Fin n → Fin n → ℂ => (∑ j, ∑ k, ‖σ j k‖ ^ 2) / 2)
  first
  | fun_prop
  | exact (continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun k _ =>
      (((continuous_apply k).comp (continuous_apply j)).norm.pow 2)).div_const 2

/- English proof (translation)
Establish `hzy : z y = e y` using `he hy`. Establish `hzy' : z y = e' y` using `he' hy'`. Establish `h1 : ∀ᶠ w in 𝓝 (z y), w ∈ e.target`. Rewrite using `[hzy]`. Conclude with `e.open_target.mem_nhds (e.map_source hy)`.

Establish `h2 : ∀ᶠ w in 𝓝 (z y), w ∈ e'.target`. Rewrite using `[hzy']`. Conclude with `e'.open_target.mem_nhds (e'.map_source hy')`. Establish `ht : Tendsto e'.symm (𝓝 (z y)) (𝓝 y)`. Rewrite using `[hzy']`.

Use `first`. Consider the case `exact e'.tendsto_symm hy'`. Consider the case `(have hc' : Tendsto e'.symm (𝓝 (e' y)) (𝓝 (e'.symm (e' y))) := e'.continuousAt_symm (e'.map_source hy')`. Rewrite using `[e'.left_inv hy'] at hc')` and apply the resulting hypothesis. Establish `h3 : ∀ᶠ w in 𝓝 (z y), e'.symm w ∈ e.source` using `ht.eventually (e.open_source.mem_nhds hy)`.

Use `filter_upwards [h1, h2, h3] with w hw hw' hw''`. Use `e.injOn hw'' (e.map_target hw) ?_` and prove the remaining obligations. Rewrite using `[e.right_inv hw, ← he hw'', he' (e'.map_target hw'), e'.right_inv hw']`.
-/
private theorem chart_symm_eventuallyEq_at_chart_point {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e') (y : M)
    (hy : y ∈ e.source) (hy' : y ∈ e'.source) : e'.symm =ᶠ[𝓝 (z y)] e.symm := by
  have hzy : z y = e y := he hy
  have hzy' : z y = e' y := he' hy'
  have h1 : ∀ᶠ w in 𝓝 (z y), w ∈ e.target := by
    rw [hzy]
    exact e.open_target.mem_nhds (e.map_source hy)
  have h2 : ∀ᶠ w in 𝓝 (z y), w ∈ e'.target := by
    rw [hzy']
    exact e'.open_target.mem_nhds (e'.map_source hy')
  have ht : Tendsto e'.symm (𝓝 (z y)) (𝓝 y) := by
    rw [hzy']
    first
    | exact e'.tendsto_symm hy'
    | (have hc' : Tendsto e'.symm (𝓝 (e' y)) (𝓝 (e'.symm (e' y))) := e'.continuousAt_symm (e'.map_source hy')
       rwa [e'.left_inv hy'] at hc')
  have h3 : ∀ᶠ w in 𝓝 (z y), e'.symm w ∈ e.source := ht.eventually (e.open_source.mem_nhds hy)
  filter_upwards [h1, h2, h3] with w hw hw' hw''
  refine e.injOn hw'' (e.map_target hw) ?_
  rw [e.right_inv hw, ← he hw'', he' (e'.map_target hw'), e'.right_inv hw']

/- English proof (translation)
Establish `hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source` using `⟨e, he, hy⟩`. Simplify using `only [d, dif_pos hc]`. Establish `hs` using `Classical.choose_spec hc`. Establish `hfg : g ∘ (Classical.choose hc).symm =ᶠ[𝓝 (z y)] g ∘ e.symm` using `(chart_symm_eventuallyEq_at_chart_point n z e (Classical.choose hc) he hs.1 y hy hs.2).fun_comp g`. Rewrite using `[← he hy]`.

Unfold `wd`. Rewrite using `[hfg.fderiv_eq]`.
-/
private theorem d_eq_wd_at_chart_image {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M) (hy : y ∈ e.source) (j : Fin n) :
    d n z j g y = wd n j (g ∘ e.symm) (e y) := by
  have hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  simp only [d, dif_pos hc]
  have hs := Classical.choose_spec hc
  have hfg : g ∘ (Classical.choose hc).symm =ᶠ[𝓝 (z y)] g ∘ e.symm :=
    (chart_symm_eventuallyEq_at_chart_point n z e (Classical.choose hc) he hs.1 y hy hs.2).fun_comp g
  rw [← he hy]
  unfold wd
  rw [hfg.fderiv_eq]

/- English proof (translation)
Establish `hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source` using `⟨e, he, hy⟩`. Simplify using `only [db, dif_pos hc]`. Establish `hs` using `Classical.choose_spec hc`. Establish `hfg : g ∘ (Classical.choose hc).symm =ᶠ[𝓝 (z y)] g ∘ e.symm` using `(chart_symm_eventuallyEq_at_chart_point n z e (Classical.choose hc) he hs.1 y hy hs.2).fun_comp g`. Rewrite using `[← he hy]`.

Unfold `wdb`. Rewrite using `[hfg.fderiv_eq]`.
-/
private theorem db_eq_wdb_at_chart_image {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M) (hy : y ∈ e.source) (j : Fin n) :
    db n z j g y = wdb n j (g ∘ e.symm) (e y) := by
  have hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  simp only [db, dif_pos hc]
  have hs := Classical.choose_spec hc
  have hfg : g ∘ (Classical.choose hc).symm =ᶠ[𝓝 (z y)] g ∘ e.symm :=
    (chart_symm_eventuallyEq_at_chart_point n z e (Classical.choose hc) he hs.1 y hy hs.2).fun_comp g
  rw [← he hy]
  unfold wdb
  rw [hfg.fderiv_eq]

/- English proof (translation)
Use `continuous_iff_continuousAt.mpr fun x => ?_` and prove the remaining obligations. Take `⟨e, hx, hze⟩` from `hz x`. Establish `he : IsChart n z e` using `fun y _ => by rw [hze]`. Apply the tactic sequence `have hF : ContinuousOn (fun w => fderiv ℝ (g ∘ e.symm) w) e.target := (hg e he).continuousOn_fderiv_of_isOpen e.open_target (by first | simp | exact_mod_cast le_top | norm_num)`. Establish `h0 : ContinuousOn (fun w => wd n j (g ∘ e.symm) w) e.target`.

Unfold `wd`. Conclude with `((hF.clm_apply continuousOn_const).sub (continuousOn_const.mul (hF.clm_apply continuousOn_const))).div_const 2`. Establish `hW : ContinuousOn (fun y => wd n j (g ∘ e.symm) (e y)) e.source` using `h0.comp e.continuousOn (fun y hy => e.map_source hy)`. Establish `hc` using `hW.continuousAt (e.open_source.mem_nhds hx)`. Establish `hEv : (fun y => wd n j (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] fun y => d n z j g y` using `by filter_upwards [e.open_source.mem_nhds hx] with y hy`.

Conclude with `(d_eq_wd_at_chart_image n z g e he y hy j).symm`. Use `first`. Consider the case `exact hc.congr hEv`. Consider the case `exact hc.congr_of_eventuallyEq hEv.symm`. Consider the case `exact (continuousAt_congr hEv).mp hc`.
-/
private theorem continuous_d_of_smooth {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Smooth n z g) (j : Fin n) :
    Continuous (fun x => d n z j g x) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => by rw [hze]
  have hF : ContinuousOn (fun w => fderiv ℝ (g ∘ e.symm) w) e.target :=
    (hg e he).continuousOn_fderiv_of_isOpen e.open_target (by first | simp | exact_mod_cast le_top | norm_num)
  have h0 : ContinuousOn (fun w => wd n j (g ∘ e.symm) w) e.target := by
    unfold wd
    exact ((hF.clm_apply continuousOn_const).sub (continuousOn_const.mul
      (hF.clm_apply continuousOn_const))).div_const 2
  have hW : ContinuousOn (fun y => wd n j (g ∘ e.symm) (e y)) e.source :=
    h0.comp e.continuousOn (fun y hy => e.map_source hy)
  have hc := hW.continuousAt (e.open_source.mem_nhds hx)
  have hEv : (fun y => wd n j (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] fun y => d n z j g y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact (d_eq_wd_at_chart_image n z g e he y hy j).symm
  first
  | exact hc.congr hEv
  | exact hc.congr_of_eventuallyEq hEv.symm
  | exact (continuousAt_congr hEv).mp hc

/- English proof (translation)
Use `continuous_iff_continuousAt.mpr fun x => ?_` and prove the remaining obligations. Take `⟨e, hx, hze⟩` from `hz x`. Establish `he : IsChart n z e` using `fun y _ => by rw [hze]`. Apply the tactic sequence `have hF : ContinuousOn (fun w => fderiv ℝ (g ∘ e.symm) w) e.target := (hg e he).continuousOn_fderiv_of_isOpen e.open_target (by first | simp | exact_mod_cast le_top | norm_num)`. Establish `h0 : ContinuousOn (fun w => wdb n j (g ∘ e.symm) w) e.target`.

Unfold `wdb`. Conclude with `((hF.clm_apply continuousOn_const).add (continuousOn_const.mul (hF.clm_apply continuousOn_const))).div_const 2`. Establish `hW : ContinuousOn (fun y => wdb n j (g ∘ e.symm) (e y)) e.source` using `h0.comp e.continuousOn (fun y hy => e.map_source hy)`. Establish `hc` using `hW.continuousAt (e.open_source.mem_nhds hx)`. Establish `hEv : (fun y => wdb n j (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] fun y => db n z j g y` using `by filter_upwards [e.open_source.mem_nhds hx] with y hy`.

Conclude with `(db_eq_wdb_at_chart_image n z g e he y hy j).symm`. Use `first`. Consider the case `exact hc.congr hEv`. Consider the case `exact hc.congr_of_eventuallyEq hEv.symm`. Consider the case `exact (continuousAt_congr hEv).mp hc`.
-/
private theorem continuous_db_apply_of_smooth {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Smooth n z g) (j : Fin n) :
    Continuous (fun x => db n z j g x) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => by rw [hze]
  have hF : ContinuousOn (fun w => fderiv ℝ (g ∘ e.symm) w) e.target :=
    (hg e he).continuousOn_fderiv_of_isOpen e.open_target (by first | simp | exact_mod_cast le_top | norm_num)
  have h0 : ContinuousOn (fun w => wdb n j (g ∘ e.symm) w) e.target := by
    unfold wdb
    exact ((hF.clm_apply continuousOn_const).add (continuousOn_const.mul
      (hF.clm_apply continuousOn_const))).div_const 2
  have hW : ContinuousOn (fun y => wdb n j (g ∘ e.symm) (e y)) e.source :=
    h0.comp e.continuousOn (fun y hy => e.map_source hy)
  have hc := hW.continuousAt (e.open_source.mem_nhds hx)
  have hEv : (fun y => wdb n j (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] fun y => db n z j g y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact (db_eq_wdb_at_chart_image n z g e he y hy j).symm
  first
  | exact hc.congr hEv
  | exact hc.congr_of_eventuallyEq hEv.symm
  | exact (continuousAt_congr hEv).mp hc

/- English proof (translation)
Use `continuous_iff_continuousAt.mpr fun x => ?_` and prove the remaining obligations. Take `⟨e, hx, hze⟩` from `hz x`. Establish `he : IsChart n z e` using `fun y _ => by rw [hze]`. Establish `hW : ContinuousOn (fun y => (g ∘ e.symm) (e y)) e.source` using `(hg e he).continuousOn.comp e.continuousOn (fun y hy => e.map_source hy)`. Establish `hEv : (fun y => (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] g` using `by filter_upwards [e.open_source.mem_nhds hx] with y hy`.

Simplify using `only [Function.comp_apply, e.left_inv hy]`. Establish `hc` using `hW.continuousAt (e.open_source.mem_nhds hx)`. Use `first`. Consider the case `exact hc.congr hEv`. Consider the case `exact hc.congr_of_eventuallyEq hEv.symm`.

Consider the case `exact (continuousAt_congr hEv).mp hc`.
-/
private theorem continuous_of_smooth_localization {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Smooth n z g) : Continuous g := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => by rw [hze]
  have hW : ContinuousOn (fun y => (g ∘ e.symm) (e y)) e.source :=
    (hg e he).continuousOn.comp e.continuousOn (fun y hy => e.map_source hy)
  have hEv : (fun y => (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] g := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp only [Function.comp_apply, e.left_inv hy]
  have hc := hW.continuousAt (e.open_source.mem_nhds hx)
  first
  | exact hc.congr hEv
  | exact hc.congr_of_eventuallyEq hEv.symm
  | exact (continuousAt_congr hEv).mp hc

/- English proof (translation)
Establish `hsm : Smooth n z (fun y => (η y : ℂ))` using `hη`. Establish `hCC : Continuous (fun y => (η y : ℂ))` using `continuous_of_smooth_localization n z hz _ hsm`. Establish `hz0 : ∀ x, x ∉ tsupport η → η x = 0` using `fun x hx => by`. Assume the negation of the conclusion as `hne`. Conclude with `hx (subset_tsupport η hne)`.

Establish `hev : ∀ x, x ∉ tsupport η → (fun y => (η y : ℂ)) =ᶠ[𝓝 x] fun _ => (0 : ℂ)`. Introduce `x hx`. Use `filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy`. Simplify using `[hz0 y hy]`. Establish `hd0 : ∀ j x, x ∉ tsupport η → d n z j (fun y => (η y : ℂ)) x = 0`.

Introduce `j x hx`. Rewrite using `[loc_d_congr n z hz j _ _ x (hev x hx)]`. Unfold `d wd`. Apply the tactic sequence `split_ifs <;> simp [Function.comp_def]`. Establish `hdb0 : ∀ j x, x ∉ tsupport η → db n z j (fun y => (η y : ℂ)) x = 0`.

Introduce `j x hx`. Rewrite using `[loc_db_congr n z hz j _ _ x (hev x hx)]`. Unfold `db wdb`. Apply the tactic sequence `split_ifs <;> simp [Function.comp_def]`. Establish `hdc : ∀ j, Continuous (fun x => d n z j (fun y => (η y : ℂ)) x)` using `fun j => continuous_d_of_smooth n z hz _ hsm j`.

Establish `hdbc : ∀ j, Continuous (fun x => db n z j (fun y => (η y : ℂ)) x)` using `fun j => continuous_db_apply_of_smooth n z hz _ hsm j`. Establish `hbound : ∀ φ : M → ℂ, Continuous φ → (∀ x, x ∉ tsupport η → φ x = 0) → ∃ C, 0 ≤ C ∧ ∀ x, ‖φ x‖ ≤ C`. Introduce `φ hφ h0`. Establish `hsub : tsupport φ ⊆ tsupport η` using `loc_tsupport_sub φ _ (isClosed_tsupport η) h0`. Establish `hcs : HasCompactSupport φ` using `IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsub`.

Establish `hex : ∃ C, ∀ x, ‖φ x‖ ≤ C` using `by first`. Consider the case `exact hφ.bounded_above_of_compact_support hcs`. Consider the case `(obtain ⟨C, hC⟩ := (hcs.isCompact_range hφ).isBounded.exists_norm_le`. Conclude with `⟨C, fun x => hC _ ⟨x, rfl⟩⟩)`. Take `⟨C, hC⟩` from `hex`.

Conclude with `⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩`. Take `⟨Cη, hCη0, hCη⟩` from `hbound _ hCC (fun x hx => by simp [hz0 x hx])`. Take `⟨K, hK0, hKd, hKdb⟩ : ∃ K : ℝ, 0 ≤ K ∧ (∀ j x, ‖d n z j (fun y => (η y : ℂ)) x‖ ≤ K) ∧ (∀ j x, ‖db n z j (fun y => (η y : ℂ)) x‖ ≤ K)` from `by choose C1 hC10 hC1 using fun j => hbound _ (hdc j) (hd0 j) choose C2 hC20 hC2 using fun j => hbound _ (hdbc j) (hdb0 j)`. Use `⟨∑ j, (C1 j + C2 j), Finset.sum_nonneg fun j _ => add_nonneg (hC10 j) (hC20 j), ?_, ?_⟩` and prove the remaining obligations. Introduce `j x`.

Establish `hs : C1 j + C2 j ≤ ∑ i, (C1 i + C2 i)` using `Finset.single_le_sum (f := fun i => C1 i + C2 i) (fun i _ => add_nonneg (hC10 i) (hC20 i)) (Finset.mem_univ j)`. Combine the linear relations using `[hC1 j x, hC20 j]`. Introduce `j x`. Establish `hs : C1 j + C2 j ≤ ∑ i, (C1 i + C2 i)` using `Finset.single_le_sum (f := fun i => C1 i + C2 i) (fun i _ => add_nonneg (hC10 i) (hC20 i)) (Finset.mem_univ j)`. Combine the linear relations using `[hC2 j x, hC10 j]`.

Establish `hcoord : ∀ (v : V n) (j : Fin n), ‖v j‖ ≤ ‖v‖`. Introduce `v j`. Use `first`. Consider the case `exact PiLp.norm_apply_le v j`. Consider the case `exact PiLp.norm_apply_le_norm v j`.

Consider the case `(rw [EuclideanSpace.norm_eq]`. Conclude with `(le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))))`. Establish `hcoordc : ∀ j : Fin n, Continuous (fun v : V n => v j)`. Introduce `j`. Use `first`.

Consider the case `fun_prop`. Consider the case `exact (EuclideanSpace.proj (𝕜 := ℂ) j).continuous`. Consider the case `exact PiLp.continuous_apply 2 _ j`. Consider the case `continuity`. Establish `hGj : ∀ j : Fin n, AEStronglyMeasurable (fun x => G x j) (vol n z)` using `fun j => (hcoordc j).comp_aestronglyMeasurable hG.1`.

Apply the tactic sequence `have hGm : LocalL2Isometry (vol n z) (locG η G) := by`. Use `locL2_of_le_sum (vol n z) (locG η G) G G Cη hG hG (hCC.aestronglyMeasurable.smul hG.1) fun x => ?_` and prove the remaining obligations. Use `show ‖(η x : ℂ) • G x‖ ≤ Cη * (‖G x‖ + ‖G x‖)`. Rewrite using `[norm_smul]`. Use `mul_le_mul_of_nonneg_right (hCη x) (norm_nonneg (G x))` as an intermediate fact.

Use polynomial arithmetic with `[mul_nonneg hCη0 (norm_nonneg (G x))]`. Establish `hDmeas : AEStronglyMeasurable (locD n z η G D) (vol n z)`. Establish `h2 : AEStronglyMeasurable (fun x => ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j) (vol n z)` using `by first`. Consider the case `exact Finset.aestronglyMeasurable_sum _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)`. Consider the case `exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)`.

Consider the case `exact Finset.aestronglyMeasurable_sum' _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)`. Conclude with `(hCC.aestronglyMeasurable.mul hD.1).add h2`. Apply the tactic sequence `have hDm : LocalL2Isometry (vol n z) (locD n z η G D) := by`. Use `locL2_of_le_sum (vol n z) (locD n z η G D) G D (Cη + (n : ℝ) * K) hG hD hDmeas fun x => ?_` and prove the remaining obligations. Use `show ‖(η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤ (Cη + (n : ℝ) * K) * (‖G x‖ + ‖D x‖)`.

Establish `e1 : ‖(η x : ℂ) * D x‖ ≤ Cη * ‖D x‖`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hCη x) (norm_nonneg _)`. Establish `e2 : ‖∑ j, d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤ (n : ℝ) * K * ‖G x‖`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Establish `hj : ∀ j ∈ Finset.univ, ‖d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤ K * ‖G x‖`. Introduce `j _`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hKd j x) (hcoord (G x) j) (norm_nonneg _) hK0`. Use `(Finset.sum_le_sum hj).trans (le_of_eq ?_)` and prove the remaining obligations.

Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnK : 0 ≤ (n : ℝ) * K` using `mul_nonneg (Nat.cast_nonneg n) hK0`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Use polynomial arithmetic with `[norm_nonneg (G x), norm_nonneg (D x), mul_nonneg hCη0 (norm_nonneg (G x)), mul_nonneg hnK (norm_nonneg (D x))]`.

Establish `hSmeas : AEStronglyMeasurable (locS n z η G S) (vol n z)`. Establish `h1 : AEStronglyMeasurable (fun x => fun l => db n z l (fun y => (η y : ℂ)) x) (vol n z)` using `(continuous_pi fun l => hdbc l).aestronglyMeasurable`. Establish `h2 : AEStronglyMeasurable (fun x => fun l => G x l) (vol n z)` using `(continuous_pi fun l => hcoordc l).comp_aestronglyMeasurable hG.1`. Establish `hpair : AEStronglyMeasurable (fun x => ((fun l => db n z l (fun y => (η y : ℂ)) x), (fun l => G x l))) (vol n z)` using `by first`. Consider the case `exact h1.prodMk h2`.

Consider the case `exact h1.prod_mk h2`. Establish `hW` using `(loc_continuous_wedge n).comp_aestronglyMeasurable hpair`. Conclude with `(hCC.aestronglyMeasurable.smul hS.1).add hW`. Apply the tactic sequence `have hSm : LocalL2Isometry (vol n z) (locS n z η G S) := by`. Use `locL2_of_le_sum (vol n z) (locS n z η G S) G S (Cη + 2 * K) hG hS hSmeas fun x => ?_` and prove the remaining obligations.

Establish `hc0 : 0 ≤ (Cη + 2 * K) * (‖G x‖ + ‖S x‖)` using `mul_nonneg (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _))`. Use `(pi_norm_le_iff_of_nonneg hc0).mpr fun j => (pi_norm_le_iff_of_nonneg hc0).mpr fun k => ?_` and prove the remaining obligations. Use `show ‖(η x : ℂ) * S x j k + wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k‖ ≤ _`. Establish `e1 : ‖(η x : ℂ) * S x j k‖ ≤ Cη * ‖S x‖`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul (hCη x) ((norm_le_pi_norm (S x j) k).trans (norm_le_pi_norm (S x) j)) (norm_nonneg _) hCη0`. Establish `e2 : ‖wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k‖ ≤ 2 * K * ‖G x‖`. Simplify using `only [wedge]`. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`.

Establish `a1` using `mul_le_mul (hKdb j x) (hcoord (G x) k) (norm_nonneg _) hK0`. Establish `a2` using `mul_le_mul (hKdb k x) (hcoord (G x) j) (norm_nonneg _) hK0`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Use polynomial arithmetic with `[norm_nonneg (G x), norm_nonneg (S x), mul_nonneg hCη0 (norm_nonneg (G x)), mul_nonneg hK0 (norm_nonneg (S x))]`.

Establish `hsubG : tsupport (locG η G) ⊆ tsupport η` using `loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by show (η x : ℂ) • G x = 0`. Simplify using `[hz0 x hx]`. Establish `hsubD : tsupport (locD n z η G D) ⊆ tsupport η` using `loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by show (η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j = 0`. Simplify using `[hz0 x hx, fun j => hd0 j x hx]`. Establish `hsubS : tsupport (locS n z η G S) ⊆ tsupport η` using `loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by`.

Use function extensionality and compare the values at `j k`. Use `show (η x : ℂ) * S x j k + wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k = 0`. Simplify using `[hz0 x hx, fun j => hdb0 j x hx, wedge]`. Conclude with `⟨hGm, hDm, hSm, hMD z hz η G D hη hG hD hGD, hMS z hz η G S hη hG hS hGS, IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubG, IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubD, IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubS, hsubG.trans hT, hsub …`.
-/
theorem loc_piece {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (hMD : MultDivStatement n M) (hMS : MultSStatement n M) (η : M → ℝ) (hη : SmoothR n z η)
    (hηc : HasCompactSupport η) (T : Set M) (hT : tsupport η ⊆ T)
    (G : M → V n) (D : M → ℂ) (S : M → Fin n → Fin n → ℂ)
    (hG : LocalL2Isometry (vol n z) G) (hD : LocalL2Isometry (vol n z) D) (hS : LocalL2Isometry (vol n z) S)
    (hGD : IsWeakDiv n z G D) (hGS : IsWeakS n z G S) :
    LocalL2Isometry (vol n z) (locG η G) ∧ LocalL2Isometry (vol n z) (locD n z η G D) ∧
      LocalL2Isometry (vol n z) (locS n z η G S) ∧
      IsWeakDiv n z (locG η G) (locD n z η G D) ∧ IsWeakS n z (locG η G) (locS n z η G S) ∧
      HasCompactSupport (locG η G) ∧ HasCompactSupport (locD n z η G D) ∧
      HasCompactSupport (locS n z η G S) ∧
      tsupport (locG η G) ⊆ T ∧ tsupport (locD n z η G D) ⊆ T ∧
      tsupport (locS n z η G S) ⊆ T := by
  have hsm : Smooth n z (fun y => (η y : ℂ)) := hη
  have hCC : Continuous (fun y => (η y : ℂ)) := continuous_of_smooth_localization n z hz _ hsm
  have hz0 : ∀ x, x ∉ tsupport η → η x = 0 := fun x hx => by
    by_contra hne
    exact hx (subset_tsupport η hne)
  have hev : ∀ x, x ∉ tsupport η → (fun y => (η y : ℂ)) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    intro x hx
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
    simp [hz0 y hy]
  have hd0 : ∀ j x, x ∉ tsupport η → d n z j (fun y => (η y : ℂ)) x = 0 := by
    intro j x hx
    rw [loc_d_congr n z hz j _ _ x (hev x hx)]
    unfold d wd
    split_ifs <;> simp [Function.comp_def]
  have hdb0 : ∀ j x, x ∉ tsupport η → db n z j (fun y => (η y : ℂ)) x = 0 := by
    intro j x hx
    rw [loc_db_congr n z hz j _ _ x (hev x hx)]
    unfold db wdb
    split_ifs <;> simp [Function.comp_def]
  have hdc : ∀ j, Continuous (fun x => d n z j (fun y => (η y : ℂ)) x) := fun j =>
    continuous_d_of_smooth n z hz _ hsm j
  have hdbc : ∀ j, Continuous (fun x => db n z j (fun y => (η y : ℂ)) x) := fun j =>
    continuous_db_apply_of_smooth n z hz _ hsm j
  have hbound : ∀ φ : M → ℂ, Continuous φ → (∀ x, x ∉ tsupport η → φ x = 0) →
      ∃ C, 0 ≤ C ∧ ∀ x, ‖φ x‖ ≤ C := by
    intro φ hφ h0
    have hsub : tsupport φ ⊆ tsupport η := loc_tsupport_sub φ _ (isClosed_tsupport η) h0
    have hcs : HasCompactSupport φ := IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsub
    have hex : ∃ C, ∀ x, ‖φ x‖ ≤ C := by
      first
      | exact hφ.bounded_above_of_compact_support hcs
      | (obtain ⟨C, hC⟩ := (hcs.isCompact_range hφ).isBounded.exists_norm_le
         exact ⟨C, fun x => hC _ ⟨x, rfl⟩⟩)
    obtain ⟨C, hC⟩ := hex
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  obtain ⟨Cη, hCη0, hCη⟩ := hbound _ hCC (fun x hx => by simp [hz0 x hx])
  obtain ⟨K, hK0, hKd, hKdb⟩ : ∃ K : ℝ, 0 ≤ K ∧ (∀ j x, ‖d n z j (fun y => (η y : ℂ)) x‖ ≤ K) ∧
      (∀ j x, ‖db n z j (fun y => (η y : ℂ)) x‖ ≤ K) := by
    choose C1 hC10 hC1 using fun j => hbound _ (hdc j) (hd0 j)
    choose C2 hC20 hC2 using fun j => hbound _ (hdbc j) (hdb0 j)
    refine ⟨∑ j, (C1 j + C2 j), Finset.sum_nonneg fun j _ => add_nonneg (hC10 j) (hC20 j), ?_, ?_⟩
    · intro j x
      have hs : C1 j + C2 j ≤ ∑ i, (C1 i + C2 i) :=
        Finset.single_le_sum (f := fun i => C1 i + C2 i) (fun i _ => add_nonneg (hC10 i) (hC20 i))
          (Finset.mem_univ j)
      linarith [hC1 j x, hC20 j]
    · intro j x
      have hs : C1 j + C2 j ≤ ∑ i, (C1 i + C2 i) :=
        Finset.single_le_sum (f := fun i => C1 i + C2 i) (fun i _ => add_nonneg (hC10 i) (hC20 i))
          (Finset.mem_univ j)
      linarith [hC2 j x, hC10 j]
  have hcoord : ∀ (v : V n) (j : Fin n), ‖v j‖ ≤ ‖v‖ := by
    intro v j
    first
    | exact PiLp.norm_apply_le v j
    | exact PiLp.norm_apply_le_norm v j
    | (rw [EuclideanSpace.norm_eq]
       exact (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
         (fun i _ => sq_nonneg _) (Finset.mem_univ j))))
  have hcoordc : ∀ j : Fin n, Continuous (fun v : V n => v j) := by
    intro j
    first
    | fun_prop
    | exact (EuclideanSpace.proj (𝕜 := ℂ) j).continuous
    | exact PiLp.continuous_apply 2 _ j
    | continuity
  have hGj : ∀ j : Fin n, AEStronglyMeasurable (fun x => G x j) (vol n z) := fun j =>
    (hcoordc j).comp_aestronglyMeasurable hG.1
  have hGm : LocalL2Isometry (vol n z) (locG η G) := by
    refine locL2_of_le_sum (vol n z) (locG η G) G G Cη hG hG (hCC.aestronglyMeasurable.smul hG.1)
      fun x => ?_
    show ‖(η x : ℂ) • G x‖ ≤ Cη * (‖G x‖ + ‖G x‖)
    rw [norm_smul]
    have := mul_le_mul_of_nonneg_right (hCη x) (norm_nonneg (G x))
    nlinarith [mul_nonneg hCη0 (norm_nonneg (G x))]
  have hDmeas : AEStronglyMeasurable (locD n z η G D) (vol n z) := by
    have h2 : AEStronglyMeasurable (fun x => ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j) (vol n z) := by
      first
      | exact Finset.aestronglyMeasurable_sum _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)
      | exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)
      | exact Finset.aestronglyMeasurable_sum' _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)
    exact (hCC.aestronglyMeasurable.mul hD.1).add h2
  have hDm : LocalL2Isometry (vol n z) (locD n z η G D) := by
    refine locL2_of_le_sum (vol n z) (locD n z η G D) G D (Cη + (n : ℝ) * K) hG hD hDmeas fun x => ?_
    show ‖(η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤
      (Cη + (n : ℝ) * K) * (‖G x‖ + ‖D x‖)
    have e1 : ‖(η x : ℂ) * D x‖ ≤ Cη * ‖D x‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hCη x) (norm_nonneg _)
    have e2 : ‖∑ j, d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤ (n : ℝ) * K * ‖G x‖ := by
      refine (norm_sum_le _ _).trans ?_
      have hj : ∀ j ∈ Finset.univ, ‖d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤ K * ‖G x‖ := by
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hKd j x) (hcoord (G x) j) (norm_nonneg _) hK0
      refine (Finset.sum_le_sum hj).trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg (Nat.cast_nonneg n) hK0
    refine (norm_add_le _ _).trans ?_
    nlinarith [norm_nonneg (G x), norm_nonneg (D x), mul_nonneg hCη0 (norm_nonneg (G x)),
      mul_nonneg hnK (norm_nonneg (D x))]
  have hSmeas : AEStronglyMeasurable (locS n z η G S) (vol n z) := by
    have h1 : AEStronglyMeasurable (fun x => fun l => db n z l (fun y => (η y : ℂ)) x) (vol n z) :=
      (continuous_pi fun l => hdbc l).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x => fun l => G x l) (vol n z) :=
      (continuous_pi fun l => hcoordc l).comp_aestronglyMeasurable hG.1
    have hpair : AEStronglyMeasurable
        (fun x => ((fun l => db n z l (fun y => (η y : ℂ)) x), (fun l => G x l))) (vol n z) := by
      first
      | exact h1.prodMk h2
      | exact h1.prod_mk h2
    have hW := (loc_continuous_wedge n).comp_aestronglyMeasurable hpair
    exact (hCC.aestronglyMeasurable.smul hS.1).add hW
  have hSm : LocalL2Isometry (vol n z) (locS n z η G S) := by
    refine locL2_of_le_sum (vol n z) (locS n z η G S) G S (Cη + 2 * K) hG hS hSmeas fun x => ?_
    have hc0 : 0 ≤ (Cη + 2 * K) * (‖G x‖ + ‖S x‖) :=
      mul_nonneg (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    refine (pi_norm_le_iff_of_nonneg hc0).mpr fun j => (pi_norm_le_iff_of_nonneg hc0).mpr fun k => ?_
    show ‖(η x : ℂ) * S x j k + wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k‖ ≤ _
    have e1 : ‖(η x : ℂ) * S x j k‖ ≤ Cη * ‖S x‖ := by
      rw [norm_mul]
      exact mul_le_mul (hCη x) ((norm_le_pi_norm (S x j) k).trans (norm_le_pi_norm (S x) j))
        (norm_nonneg _) hCη0
    have e2 : ‖wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k‖ ≤ 2 * K * ‖G x‖ := by
      simp only [wedge]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have a1 := mul_le_mul (hKdb j x) (hcoord (G x) k) (norm_nonneg _) hK0
      have a2 := mul_le_mul (hKdb k x) (hcoord (G x) j) (norm_nonneg _) hK0
      linarith
    refine (norm_add_le _ _).trans ?_
    nlinarith [norm_nonneg (G x), norm_nonneg (S x), mul_nonneg hCη0 (norm_nonneg (G x)),
      mul_nonneg hK0 (norm_nonneg (S x))]
  have hsubG : tsupport (locG η G) ⊆ tsupport η :=
    loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by
      show (η x : ℂ) • G x = 0
      simp [hz0 x hx]
  have hsubD : tsupport (locD n z η G D) ⊆ tsupport η :=
    loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by
      show (η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j = 0
      simp [hz0 x hx, fun j => hd0 j x hx]
  have hsubS : tsupport (locS n z η G S) ⊆ tsupport η :=
    loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by
      funext j k
      show (η x : ℂ) * S x j k + wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k = 0
      simp [hz0 x hx, fun j => hdb0 j x hx, wedge]
  exact ⟨hGm, hDm, hSm, hMD z hz η G D hη hG hD hGD, hMS z hz η G S hη hG hS hGS,
    IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubG,
    IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubD,
    IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubS,
    hsubG.trans hT, hsubD.trans hT, hsubS.trans hT⟩

/- English proof (translation)
Unfold `sq2`. Use `first`. Consider the case `positivity`. Consider the case `exact div_nonneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (by norm_num)`.
-/
theorem two_form_norm_sq_nonneg (n : ℕ) (σ : Fin n → Fin n → ℂ) : 0 ≤ sq2 n σ := by
  unfold sq2
  first
  | positivity
  | exact div_nonneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (by norm_num)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => hb i), ENNReal.ofReal_natCast]`.
-/
theorem loc_ofReal_le {N : ℕ} (b : Fin N → ℝ) (hb : ∀ i, 0 ≤ b i) (a : ℝ)
    (h : a ≤ N * ∑ i, b i) : ENNReal.ofReal a ≤ N * ∑ i, ENNReal.ofReal (b i) := by
  calc ENNReal.ofReal a ≤ ENNReal.ofReal (N * ∑ i, b i) := ENNReal.ofReal_le_ofReal h
    _ = N * ∑ i, ENNReal.ofReal (b i) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => hb i),
        ENNReal.ofReal_natCast]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N), lintegral_finset_sum' _ (fun i _ => hf i)]`. Use `_ ≤ N * ∑ _i : Fin N, δ' := by gcongr with i`. Conclude with `(hi i).le`. Use `_ = δ' * (N * N) := by`.

Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ < δ := hδ`.
-/
theorem loc_lintegral_sum_lt {M : Type*} [MeasurableSpace M] (μ : Measure M) {N : ℕ}
    (F : M → ℝ≥0∞) (f : Fin N → M → ℝ≥0∞) (hf : ∀ i, AEMeasurable (f i) μ)
    (hle : ∀ x, F x ≤ N * ∑ i, f i x) (δ' δ : ℝ≥0∞) (hi : ∀ i, ∫⁻ x, f i x ∂μ < δ')
    (hδ : δ' * (N * N) < δ) : ∫⁻ x, F x ∂μ < δ := by
  calc ∫⁻ x, F x ∂μ ≤ ∫⁻ x, N * ∑ i, f i x ∂μ := lintegral_mono hle
    _ = N * ∑ i, ∫⁻ x, f i x ∂μ := by
      rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N), lintegral_finset_sum' _ (fun i _ => hf i)]
    _ ≤ N * ∑ _i : Fin N, δ' := by
      gcongr with i
      exact (hi i).le
    _ = δ' * (N * N) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ < δ := hδ

/- English proof (translation)
Simplify using `only [neg_zero, Real.exp_zero, mul_one]`. Conclude with `((continuous_norm.pow 2).comp_aestronglyMeasurable h).aemeasurable.ennreal_ofReal`.
-/
theorem loc_aem {M E : Type*} [MeasurableSpace M] [NormedAddCommGroup E] (μ : Measure M)
    (a : M → E) (h : AEStronglyMeasurable a μ) :
    AEMeasurable (fun x => ENNReal.ofReal (‖a x‖ ^ 2 * Real.exp (-(fun _ : M => (0 : ℝ)) x))) μ := by
  simp only [neg_zero, Real.exp_zero, mul_one]
  exact ((continuous_norm.pow 2).comp_aestronglyMeasurable h).aemeasurable.ennreal_ofReal

/- English proof (translation)
Simplify using `only [neg_zero, Real.exp_zero, mul_one]`. Conclude with `((continuous_two_form_norm_sq n).comp_aestronglyMeasurable h).aemeasurable.ennreal_ofReal`.
-/
theorem aemeasurable_unweighted_two_form {M : Type*} [MeasurableSpace M] {n : ℕ} (μ : Measure M)
    (σ : M → Fin n → Fin n → ℂ) (h : AEStronglyMeasurable σ μ) :
    AEMeasurable (fun x => ENNReal.ofReal (sq2 n (σ x) * Real.exp (-(fun _ : M => (0 : ℝ)) x))) μ := by
  simp only [neg_zero, Real.exp_zero, mul_one]
  exact ((continuous_two_form_norm_sq n).comp_aestronglyMeasurable h).aemeasurable.ennreal_ofReal

end

end ReciprocityTheory.L2DbarEstimates.F

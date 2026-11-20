import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix Filter Topology Set MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.BesselCutLim

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Take `⟨C, hC⟩` from `hρ.bounded_above_of_compact_support hc`. Rewrite using `[← integral_smul]`. Use `tendsto_integral_of_dominated_convergence (fun y => C * ‖f y‖) (fun N => ?_) (hf.norm.const_mul C) (fun N => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Establish `h1 : Continuous fun y : PI.MtM n => (ρ (((N : ℝ) + 1)⁻¹ • Matrix.of y) : ℂ)` using `Complex.continuous_ofReal.comp (hρ.comp ((show Continuous fun y : PI.MtM n => (Matrix.of y : Mat n) from continuous_id).const_smul (((N : ℝ) + 1)⁻¹)))`. Conclude with `h1.aestronglyMeasurable.smul hf.1`.

Rewrite using `[norm_smul, Complex.norm_real]`. Conclude with `mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)`. Use `Tendsto.smul_const ?_ _` and prove the remaining obligations. Use `(Complex.continuous_ofReal.comp hρ).continuousAt.tendsto.comp ?_` and prove the remaining obligations. Establish `h0 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0)`.

Simplify `tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)` using `only [one_div]`. Simplify using `using h0.smul_const (Matrix.of y : Mat n)`.
-/
theorem tendsto_cut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure (PI.MtM n)}
    {f : PI.MtM n → E} (hf : Integrable f μ) {ρ : Mat n → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ) :
    Tendsto (fun N : ℕ => ∫ y : PI.MtM n, (ρ (((N : ℝ) + 1)⁻¹ • Matrix.of y) : ℂ) • f y ∂μ) atTop
      (𝓝 ((ρ 0 : ℂ) • ∫ y, f y ∂μ)) := by
  obtain ⟨C, hC⟩ := hρ.bounded_above_of_compact_support hc
  rw [← integral_smul]
  refine tendsto_integral_of_dominated_convergence (fun y => C * ‖f y‖) (fun N => ?_)
    (hf.norm.const_mul C) (fun N => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · have h1 : Continuous fun y : PI.MtM n => (ρ (((N : ℝ) + 1)⁻¹ • Matrix.of y) : ℂ) :=
      Complex.continuous_ofReal.comp (hρ.comp
        ((show Continuous fun y : PI.MtM n => (Matrix.of y : Mat n) from continuous_id).const_smul
          (((N : ℝ) + 1)⁻¹)))
    exact h1.aestronglyMeasurable.smul hf.1
  · rw [norm_smul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · refine Tendsto.smul_const ?_ _
    refine (Complex.continuous_ofReal.comp hρ).continuousAt.tendsto.comp ?_
    have h0 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h0.smul_const (Matrix.of y : Mat n)

/- English proof (translation)
Establish `hms : MeasurableSet {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G}` using `IsClosed.measurableSet (α := PI.MtM n) hG`. Establish `hg' : ContinuousOn (fun y : PI.MtM n => g (Matrix.of y)) {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G}` using `hg`. Establish `hm` using `hg'.aestronglyMeasurable (μ := μ) hms`. Rewrite `hm` using `[Measure.restrict_eq_self_of_ae_mem (s := {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G}) hae]`. Use `Integrable.mono' (hc.norm.mul_const K) ((Complex.continuous_conj.comp_aestronglyMeasurable hc.1).smul hm) ?_` and prove the remaining obligations.

Use `filter_upwards [hae] with y hy`. Rewrite using `[norm_smul, Complex.norm_conj]`. Conclude with `mul_le_mul_of_nonneg_left (hK _ hy) (norm_nonneg _)`.
-/
theorem integrable_conj_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (Mat n)}
    (hG : IsClosed G) {μ : Measure (PI.MtM n)} (hae : ∀ᵐ y ∂μ, (Matrix.of y : Mat n) ∈ G)
    {c : PI.MtM n → ℂ} (hc : Integrable c μ) {g : Mat n → E} (hg : ContinuousOn g G) {K : ℝ}
    (hK : ∀ x ∈ G, ‖g x‖ ≤ K) : Integrable (fun y => conj (c y) • g (Matrix.of y)) μ := by
  have hms : MeasurableSet {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G} :=
    IsClosed.measurableSet (α := PI.MtM n) hG
  have hg' : ContinuousOn (fun y : PI.MtM n => g (Matrix.of y)) {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G} := hg
  have hm := hg'.aestronglyMeasurable (μ := μ) hms
  rw [Measure.restrict_eq_self_of_ae_mem (s := {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G}) hae] at hm
  refine Integrable.mono' (hc.norm.mul_const K)
    ((Complex.continuous_conj.comp_aestronglyMeasurable hc.1).smul hm) ?_
  filter_upwards [hae] with y hy
  rw [norm_smul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (hK _ hy) (norm_nonneg _)

/- English proof (translation)
Introduce `X hX t` and use `ex_mem_of_lie (hW X hX) t`.
-/
theorem lieW_of {Hm : Mat n} {W : List (Mat n)} (hW : LieWd Hm W) : LieW (UH Hm) W :=
  fun X hX t => ex_mem_of_lie (hW X hX) t

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Hm : Mat n}
  {σ : Mat n → (H →L[ℂ] H)}

/- English proof (translation)
Proceed by induction on `W using List.reverseRecOn with`. Consider the case `nil`. Introduce `_ ρ hρ hc v hv`. Establish `h1` using `integrable_conj_smul hσ.grp.1 hμ.2.2.1 (hi v hv) (g := fun x => σ x w) (SmOn.continuousOn hw) (K := ‖w‖) fun x hx => (hσ.iso x hx w).le`. Establish `h2` using `tendsto_cut h1 hρ.continuous hc`.

Rewrite `h2` using `[hκ v hv]`. Simplify `h2` using `only [dsW, List.foldr_nil, cutI, mul_smul]`. Consider the case `append_singleton W X ih`. Introduce `hWX ρ hρ hc v hv`. Establish `hW : LieWd Hm W` using `fun Y hY => hWX Y (List.mem_append_left _ hY)`.

Establish `hX : Lie Hm X` using `hWX X (by simp)`. Establish `hX' : LieWd Hm [X]` using `fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX`. Establish `hv' : IsSm (UH Hm) σ (ds σ X v)` using `hv.dsW hσ.rep (lieW_of hX')`. Establish `hρ'` using `contDiff_Lx X hρ`. Establish `hc' : HasCompactSupport (Lx X ρ)` using `hasCompactSupport_LW hc [X]`.

Establish `e : ∀ u, dsW σ (W ++ [X]) u = dsW σ W (ds σ X u)` using `fun u => by`. Simplify using `only [dsW, List.foldr_append, List.foldr_cons, List.foldr_nil]`. Establish `h1` using `(ih hW _ hρ' hc' v hv).add (ih hW ρ hρ hc _ hv')`. Establish `h0 : Lx X ρ 0 = 0` using `by simp [Lx]`. Rewrite `h1` using `[h0, Complex.ofReal_zero, zero_smul, zero_add]`.

Rewrite using `[e]`. Use `h1.congr fun N => ?_` and prove the remaining obligations. Establish `hR : (0 : ℝ) < (N : ℝ) + 1` using `by positivity`. Rewrite using `[e, (hD n Hm H σ hσ μ hμ w hw _ hR ρ hρ hc v hv).2 X hX, dsW_add hσ.rep (hD n Hm H σ hσ μ hμ w hw _ hR _ hρ' hc' v hv).1 (hD n Hm H σ hσ μ hμ w hw _ hR ρ hρ hc _ hv').1 (lieW_of hW)]`.
-/
theorem tendsto_dsW (hD : CutDer) (hσ : URep Hm σ) {μ : Measure (PI.MtM n)} (hμ : PI.IsHaarOnM (UH Hm) μ)
    {w : H} (hw : IsSm (UH Hm) σ w)
    (hi : ∀ v, IsSm (UH Hm) σ v → Integrable (fun y : PI.MtM n => ⟪v, σ (Matrix.of y) w⟫_ℂ) μ) {κ : ℂ}
    (hκ : ∀ v, IsSm (UH Hm) σ v →
      ∫ y : PI.MtM n, conj ⟪v, σ (Matrix.of y) w⟫_ℂ • σ (Matrix.of y) w ∂μ = κ • v)
    (W : List (Mat n)) : LieWd Hm W → ∀ ρ : Mat n → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      ∀ v, IsSm (UH Hm) σ v →
      Tendsto (fun N : ℕ => dsW σ W (cutI σ μ w ((N : ℝ) + 1) ρ v)) atTop (𝓝 ((ρ 0 : ℂ) • κ • dsW σ W v)) := by
  induction W using List.reverseRecOn with
  | nil =>
    intro _ ρ hρ hc v hv
    have h1 := integrable_conj_smul hσ.grp.1 hμ.2.2.1 (hi v hv) (g := fun x => σ x w)
      (SmOn.continuousOn hw) (K := ‖w‖) fun x hx => (hσ.iso x hx w).le
    have h2 := tendsto_cut h1 hρ.continuous hc
    rw [hκ v hv] at h2
    simpa only [dsW, List.foldr_nil, cutI, mul_smul] using h2
  | append_singleton W X ih =>
    intro hWX ρ hρ hc v hv
    have hW : LieWd Hm W := fun Y hY => hWX Y (List.mem_append_left _ hY)
    have hX : Lie Hm X := hWX X (by simp)
    have hX' : LieWd Hm [X] := fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
    have hv' : IsSm (UH Hm) σ (ds σ X v) := hv.dsW hσ.rep (lieW_of hX')
    have hρ' := contDiff_Lx X hρ
    have hc' : HasCompactSupport (Lx X ρ) := hasCompactSupport_LW hc [X]
    have e : ∀ u, dsW σ (W ++ [X]) u = dsW σ W (ds σ X u) := fun u => by
      simp only [dsW, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have h1 := (ih hW _ hρ' hc' v hv).add (ih hW ρ hρ hc _ hv')
    have h0 : Lx X ρ 0 = 0 := by simp [Lx]
    rw [h0, Complex.ofReal_zero, zero_smul, zero_add] at h1
    rw [e]
    refine h1.congr fun N => ?_
    have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [e, (hD n Hm H σ hσ μ hμ w hw _ hR ρ hρ hc v hv).2 X hX,
      dsW_add hσ.rep (hD n Hm H σ hσ μ hμ w hw _ hR _ hρ' hc' v hv).1
        (hD n Hm H σ hσ μ hμ w hw _ hR ρ hρ hc _ hv').1 (lieW_of hW)]

/- English proof (translation)
Establish `hG` using `hσ.grp`. Establish `hι` using `CompanionTheory.D.Upq.ModEx.MG.measurableEmbedding_toM (hG := hG)`. Establish `hmap` using `CompanionTheory.D.Upq.Quot.map_comap_toM hG (μ := μ) hμ.2.2.1`. Use `set μ' := μ.comap (CompanionTheory.D.Upq.ModEx.MG.toM (hG := hG)) with hμ'`. Establish `: IsFiniteMeasureOnCompacts μ'` using `⟨fun K hK => by`.

Rewrite using `[hμ', hι.comap_apply]`. Conclude with `CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact hG hμ (hK.image (CompanionTheory.D.Upq.ModEx.MG.continuous_mat (hG := hG)))⟩`. Set `φ : CompanionTheory.D.Upq.ModEx.MG (UH Hm) hG → ℂ` to `fun g => (ρ (R⁻¹ • g.mat) : ℂ) * conj ⟪v, σ g.mat w⟫_ℂ`. Establish `ho : Continuous fun g : CompanionTheory.D.Upq.ModEx.MG (UH Hm) hG => σ g.mat w` using `continuous_orbit hσ.rep hw (W := []) fun _ h => by simp at h`. Establish `hφ : Continuous φ` using `(Complex.continuous_ofReal.comp (hρ.comp (CompanionTheory.D.Upq.ModEx.MG.continuous_mat.const_smul R⁻¹))).mul (Complex.continuous_conj.comp (continuous_const.inner ho))`.

Establish `hcs : HasCompactSupport fun x : Mat n => (ρ (R⁻¹ • x) : ℂ)` using `(hc.comp_smul (inv_ne_zero hR.ne')).comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero`. Establish `hφc : HasCompactSupport φ` using `(hcs.comp_isClosedEmbedding CompanionTheory.D.Upq.ModEx.MG.isClosedEmbedding_mat).mul_right`. Unfold `cutI`. Rewrite using `[← hmap, hι.integrable_map_iff, hι.integral_map, hι.integral_map]`. Conclude with `⟨integrable_csmul hφ hφc (continuous_orbit hσ.rep hw (lieW_of hW)), dsW_integral hσ.rep hw hφ hφc (lieW_of hW)⟩`.
-/
theorem dsW_cutI (hσ : URep Hm σ) {μ : Measure (PI.MtM n)} (hμ : PI.IsHaarOnM (UH Hm) μ)
    {w : H} (hw : IsSm (UH Hm) σ w) {R : ℝ} (hR : 0 < R) {ρ : Mat n → ℝ} (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (v : H) {W : List (Mat n)} (hW : LieWd Hm W) :
    Integrable (fun y : PI.MtM n => ((ρ (R⁻¹ • Matrix.of y) : ℂ) * conj ⟪v, σ (Matrix.of y) w⟫_ℂ) •
      dsW σ W (σ (Matrix.of y) w)) μ ∧
    dsW σ W (cutI σ μ w R ρ v) = ∫ y : PI.MtM n, ((ρ (R⁻¹ • Matrix.of y) : ℂ) * conj ⟪v, σ (Matrix.of y) w⟫_ℂ) •
      dsW σ W (σ (Matrix.of y) w) ∂μ := by
  have hG := hσ.grp
  have hι := CompanionTheory.D.Upq.ModEx.MG.measurableEmbedding_toM (hG := hG)
  have hmap := CompanionTheory.D.Upq.Quot.map_comap_toM hG (μ := μ) hμ.2.2.1
  set μ' := μ.comap (CompanionTheory.D.Upq.ModEx.MG.toM (hG := hG)) with hμ'
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun K hK => by
    rw [hμ', hι.comap_apply]
    exact CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact hG hμ
      (hK.image (CompanionTheory.D.Upq.ModEx.MG.continuous_mat (hG := hG)))⟩
  let φ : CompanionTheory.D.Upq.ModEx.MG (UH Hm) hG → ℂ := fun g =>
    (ρ (R⁻¹ • g.mat) : ℂ) * conj ⟪v, σ g.mat w⟫_ℂ
  have ho : Continuous fun g : CompanionTheory.D.Upq.ModEx.MG (UH Hm) hG => σ g.mat w :=
    continuous_orbit hσ.rep hw (W := []) fun _ h => by simp at h
  have hφ : Continuous φ :=
    (Complex.continuous_ofReal.comp (hρ.comp
      (CompanionTheory.D.Upq.ModEx.MG.continuous_mat.const_smul R⁻¹))).mul
      (Complex.continuous_conj.comp (continuous_const.inner ho))
  have hcs : HasCompactSupport fun x : Mat n => (ρ (R⁻¹ • x) : ℂ) :=
    (hc.comp_smul (inv_ne_zero hR.ne')).comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hφc : HasCompactSupport φ :=
    (hcs.comp_isClosedEmbedding CompanionTheory.D.Upq.ModEx.MG.isClosedEmbedding_mat).mul_right
  unfold cutI
  rw [← hmap, hι.integrable_map_iff, hι.integral_map, hι.integral_map]
  exact ⟨integrable_csmul hφ hφc (continuous_orbit hσ.rep hw (lieW_of hW)),
    dsW_integral hσ.rep hw hφ hφc (lieW_of hW)⟩

/- English proof (translation)
Introduce `n Hm H _ _ _ σ hσ V _ _ _ B hB μ hμ w hw hi κ hκ ⟨K, hK⟩ v hv`. Establish `: CompleteSpace V` using `FiniteDimensional.complete ℂ V`. Take `⟨M, W, β, hW, hBβ⟩` from `hF n Hm H σ hσ V B hB`. Take `⟨ρ, -, hc, hρ, -, hρ1⟩` from `exists_contDiff_tsupport_subset (n := ⊤) (Filter.univ_mem : (univ : Set (Mat n)) ∈ 𝓝 0)`. Establish `hae : ∀ᵐ y ∂μ, (Matrix.of y : Mat n) ∈ UH Hm` using `hμ.2.2.1`.

Establish `h1 : Tendsto (fun N : ℕ => ∑ i, β i (dsW σ (W i) (cutI σ μ w ((N : ℝ) + 1) ρ v))) atTop (𝓝 (∑ i, β i ((ρ 0 : ℂ) • κ • dsW σ (W i) v)))` using `tendsto_finsetSum _ fun i _ => ((β i).continuous.tendsto _).comp (tendsto_dsW hD hσ hμ hw hi hκ (W i) (hW i) ρ hρ hc v hv)`. Establish `hBc : ContinuousOn (fun x => B (σ x w)) (UH Hm)` using `(continuousOn_finsetSum _ fun i _ => (β i).continuous.comp_continuousOn (continuousOn_dsW_orbit hσ.rep hw (lieW_of (hW i)))).congr fun x hx => hBβ _ (hw.apply hσ.rep hx)`. Establish `h2` using `tendsto_cut (integrable_conj_smul hσ.grp.1 hae (hi v hv) hBc hK) hρ.continuous hc`. Rewrite `h1`, `h2` using `[hρ1, Complex.ofReal_one]`. Simplify using `only [one_smul, map_smul] at h1 h2`.

Rewrite `h1` using `[← Finset.smul_sum, ← hBβ v hv]`. Use `tendsto_nhds_unique h1 (h2.congr fun N => ?_)` and prove the remaining obligations. Establish `hR : (0 : ℝ) < (N : ℝ) + 1` using `by positivity`. Establish `h3` using `fun i => dsW_cutI hσ hμ hw hR hρ.continuous hc v (hW i)`. Rewrite using `[Finset.sum_congr rfl fun i _ => by rw [(h3 i).2, ← (β i).integral_comp_comm (h3 i).1], ← integral_finsetSum _ fun i _ => (β i).integrable_comp (h3 i).1]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with y hy`. Rewrite using `[hBβ _ (hw.apply hσ.rep hy)]`. Simplify using `only [map_smul, mul_smul, Finset.smul_sum]`.
-/
theorem cutLim_of (hF : Factor) (hD : CutDer) : CutLim := by
  intro n Hm H _ _ _ σ hσ V _ _ _ B hB μ hμ w hw hi κ hκ ⟨K, hK⟩ v hv
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  obtain ⟨M, W, β, hW, hBβ⟩ := hF n Hm H σ hσ V B hB
  obtain ⟨ρ, -, hc, hρ, -, hρ1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (Filter.univ_mem : (univ : Set (Mat n)) ∈ 𝓝 0)
  have hae : ∀ᵐ y ∂μ, (Matrix.of y : Mat n) ∈ UH Hm := hμ.2.2.1
  have h1 : Tendsto (fun N : ℕ => ∑ i, β i (dsW σ (W i) (cutI σ μ w ((N : ℝ) + 1) ρ v))) atTop
      (𝓝 (∑ i, β i ((ρ 0 : ℂ) • κ • dsW σ (W i) v))) :=
    tendsto_finsetSum _ fun i _ => ((β i).continuous.tendsto _).comp
      (tendsto_dsW hD hσ hμ hw hi hκ (W i) (hW i) ρ hρ hc v hv)
  have hBc : ContinuousOn (fun x => B (σ x w)) (UH Hm) :=
    (continuousOn_finsetSum _ fun i _ => (β i).continuous.comp_continuousOn
      (continuousOn_dsW_orbit hσ.rep hw (lieW_of (hW i)))).congr
      fun x hx => hBβ _ (hw.apply hσ.rep hx)
  have h2 := tendsto_cut (integrable_conj_smul hσ.grp.1 hae (hi v hv) hBc hK) hρ.continuous hc
  rw [hρ1, Complex.ofReal_one] at h1 h2
  simp only [one_smul, map_smul] at h1 h2
  rw [← Finset.smul_sum, ← hBβ v hv] at h1
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h3 := fun i => dsW_cutI hσ hμ hw hR hρ.continuous hc v (hW i)
  rw [Finset.sum_congr rfl fun i _ => by rw [(h3 i).2, ← (β i).integral_comp_comm (h3 i).1],
    ← integral_finsetSum _ fun i _ => (β i).integrable_comp (h3 i).1]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hBβ _ (hw.apply hσ.rep hy)]
  simp only [map_smul, mul_smul, Finset.smul_sum]

end GlobalTheory.CompanionTheory.BesselCutLim

end

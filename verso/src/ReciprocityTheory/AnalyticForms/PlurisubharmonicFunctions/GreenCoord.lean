import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LeviOneEqLaplacianThm
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LogInt

open MeasureTheory
open scoped Laplacian Pointwise

namespace ReciprocityTheory.AnForm.A

noncomputable section

/- English proof (translation)
Use extensionality with `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Take `⟨i, rfl⟩` from `Fin.exists_succAbove_eq hk`.

Simplify using `[Pi.single_apply]`.
-/
theorem insertNth_eq_add {D : ℕ} (j : Fin (D + 1)) (w : Fin D → ℂ) (ζ : ℂ) :
    Fin.insertNth j ζ w = Fin.insertNth j (0 : ℂ) w + (Pi.single j ζ : Fin (D + 1) → ℂ) := by
  ext k
  by_cases hk : k = j
  · subst hk
    simp
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
    simp [Pi.single_apply]

/- English proof (translation)
Use `set A : ℂ →L[ℝ] (Fin (D + 1) → ℂ) := ContinuousLinearMap.single ℝ (fun _ : Fin (D + 1) => ℂ) j with hA`. Use `set c : Fin (D + 1) → ℂ := Fin.insertNth j (0 : ℂ) w with hc`. Establish `hAv : ∀ a : ℂ, A a = Pi.single j a` using `fun a => rfl`. Establish `hf : (fun ζ' : ℂ => u (Fin.insertNth j ζ' w)) = (fun z => u (z + c)) ∘ A`. Use function extensionality and compare the values at `ζ'`.

Use `show u (Fin.insertNth j ζ' w) = u (A ζ' + c)`. Rewrite using `[hAv, add_comm (Pi.single j ζ') c]`. Conclude with `congrArg u (insertNth_eq_add j w ζ')`. Establish `huc : ContDiff ℝ 2 (fun z => u (z + c))` using `hu.comp (contDiff_id.add contDiff_const)`. Establish `hz : A ζ + c = Fin.insertNth j ζ w`.

Rewrite using `[hAv, add_comm (Pi.single j ζ) c]`. Conclude with `(insertNth_eq_add j w ζ).symm`. Establish `h2 : ∀ a : ℂ, iteratedFDeriv ℝ 2 (fun ζ' : ℂ => u (Fin.insertNth j ζ' w)) ζ ![a, a] = fderiv ℝ (fderiv ℝ u) (Fin.insertNth j ζ w) (A a) (A a)`. Introduce `a`. Rewrite using `[hf, ContinuousLinearMap.iteratedFDeriv_comp_right A huc ζ (by norm_num), ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right, iteratedFDeriv_two_apply, hz]`.

Simplify using the standard rewrite rules. Establish `hΔ` using `congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane (fun ζ' : ℂ => u (Fin.insertNth j ζ' w))) ζ`. Rewrite using `[hΔ, h2, h2]`. Establish `hAI : A Complex.I = Complex.I • (Pi.single j 1 : Fin (D + 1) → ℂ)`. Rewrite using `[hAv]`.

Use extensionality with `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`.

Rewrite using `[hAI, hAv]`. Both sides reduce to the same expression.
-/
theorem levi_insertNth {D : ℕ} (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ)
    (hu : ContDiff ℝ 2 u) (w : Fin D → ℂ) (ζ : ℂ) :
    ReciprocityTheory.AnForm.levi u (Fin.insertNth j ζ w) (Pi.single j 1) =
      Δ (fun ζ' => u (Fin.insertNth j ζ' w)) ζ / 4 := by
  set A : ℂ →L[ℝ] (Fin (D + 1) → ℂ) := ContinuousLinearMap.single ℝ (fun _ : Fin (D + 1) => ℂ) j with hA
  set c : Fin (D + 1) → ℂ := Fin.insertNth j (0 : ℂ) w with hc
  have hAv : ∀ a : ℂ, A a = Pi.single j a := fun a => rfl
  have hf : (fun ζ' : ℂ => u (Fin.insertNth j ζ' w)) = (fun z => u (z + c)) ∘ A := by
    funext ζ'
    show u (Fin.insertNth j ζ' w) = u (A ζ' + c)
    rw [hAv, add_comm (Pi.single j ζ') c]
    exact congrArg u (insertNth_eq_add j w ζ')
  have huc : ContDiff ℝ 2 (fun z => u (z + c)) := hu.comp (contDiff_id.add contDiff_const)
  have hz : A ζ + c = Fin.insertNth j ζ w := by
    rw [hAv, add_comm (Pi.single j ζ) c]
    exact (insertNth_eq_add j w ζ).symm
  have h2 : ∀ a : ℂ, iteratedFDeriv ℝ 2 (fun ζ' : ℂ => u (Fin.insertNth j ζ' w)) ζ ![a, a] =
      fderiv ℝ (fderiv ℝ u) (Fin.insertNth j ζ w) (A a) (A a) := by
    intro a
    rw [hf, ContinuousLinearMap.iteratedFDeriv_comp_right A huc ζ (by norm_num),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right,
      iteratedFDeriv_two_apply, hz]
    simp
  have hΔ := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane
    (fun ζ' : ℂ => u (Fin.insertNth j ζ' w))) ζ
  rw [hΔ, h2, h2]
  have hAI : A Complex.I = Complex.I • (Pi.single j 1 : Fin (D + 1) → ℂ) := by
    rw [hAv]
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [hAI, hAv]
  rfl

def uPair {D : ℕ} (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ) (q : ℂ × (Fin D → ℂ)) : ℝ :=
  u (Fin.insertNth j q.1 q.2)

/- English proof (translation)
Use `contDiff_pi.2 fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Establish `e : (fun q : ℂ × (Fin D → ℂ) => (Fin.insertNth k q.1 q.2 : Fin (D + 1) → ℂ) k) = fun q => q.1` using `funext fun q => Fin.insertNth_apply_same _ _ _`. Rewrite using `[e]`.

Conclude with `contDiff_fst`. Take `⟨i, rfl⟩` from `Fin.exists_succAbove_eq hk`. Establish `e : (fun q : ℂ × (Fin D → ℂ) => (Fin.insertNth j q.1 q.2 : Fin (D + 1) → ℂ) (j.succAbove i)) = fun q => q.2 i` using `funext fun q => Fin.insertNth_apply_succAbove _ _ _ _`. Rewrite using `[e]`. Conclude with `(contDiff_apply ℝ ℂ i).comp contDiff_snd`.
-/
theorem contDiff_insertNth_pair {D : ℕ} (j : Fin (D + 1)) :
    ContDiff ℝ 2 (fun q : ℂ × (Fin D → ℂ) => (Fin.insertNth j q.1 q.2 : Fin (D + 1) → ℂ)) := by
  refine contDiff_pi.2 fun k => ?_
  by_cases hk : k = j
  · subst hk
    have e : (fun q : ℂ × (Fin D → ℂ) => (Fin.insertNth k q.1 q.2 : Fin (D + 1) → ℂ) k) =
        fun q => q.1 := funext fun q => Fin.insertNth_apply_same _ _ _
    rw [e]
    exact contDiff_fst
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
    have e : (fun q : ℂ × (Fin D → ℂ) => (Fin.insertNth j q.1 q.2 : Fin (D + 1) → ℂ) (j.succAbove i)) =
        fun q => q.2 i := funext fun q => Fin.insertNth_apply_succAbove _ _ _ _
    rw [e]
    exact (contDiff_apply ℝ ℂ i).comp contDiff_snd

/- English proof (translation)
Conclude with `hu.comp (contDiff_insertNth_pair j)`.
-/
theorem uPair_contDiff {D : ℕ} (j : Fin (D + 1)) {u : (Fin (D + 1) → ℂ) → ℝ}
    (hu : ContDiff ℝ 2 u) : ContDiff ℝ 2 (uPair j u) := by
  exact hu.comp (contDiff_insertNth_pair j)

/- English proof (translation)
Set `h : ℂ × (Fin D → ℂ) ≃ₜ (Fin (D + 1) → ℂ)` to `{ toEquiv := Fin.insertNthEquiv (fun _ : Fin (D + 1) => ℂ) j continuous_toFun := (contDiff_insertNth_pair j).continuous continuous_invFun := by`. Express the relevant statement in the definitionally equal form `Continuous fun z : Fin (D + 1) → ℂ => (z j, fun i => z (j.succAbove i))`. Conclude with `(continuous_apply j).prodMk (continuous_pi fun i => continuous_apply _) }`. Conclude with `hs.comp_homeomorph h`.
-/
theorem uPair_hasCompactSupport {D : ℕ} (j : Fin (D + 1)) {u : (Fin (D + 1) → ℂ) → ℝ}
    (hs : HasCompactSupport u) : HasCompactSupport (uPair j u) := by
  let h : ℂ × (Fin D → ℂ) ≃ₜ (Fin (D + 1) → ℂ) :=
    { toEquiv := Fin.insertNthEquiv (fun _ : Fin (D + 1) => ℂ) j
      continuous_toFun := (contDiff_insertNth_pair j).continuous
      continuous_invFun := by
        change Continuous fun z : Fin (D + 1) → ℂ => (z j, fun i => z (j.succAbove i))
        exact (continuous_apply j).prodMk (continuous_pi fun i => continuous_apply _) }
  exact hs.comp_homeomorph h

/- English proof (translation)
Rewrite using `[ddcCoordDens, levi_insertNth j u hu w ζ]`. Simplify using `only [uPair]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ddcCoordDens_insertNth {D : ℕ} (j : Fin (D + 1)) {u : (Fin (D + 1) → ℂ) → ℝ}
    (hu : ContDiff ℝ 2 u) (w : Fin D → ℂ) (ζ : ℂ) :
    ddcCoordDens j u (Fin.insertNth j ζ w) =
      (1 / (2 * Real.pi)) * Δ (fun ζ' => uPair j u (ζ', w)) ζ := by
  rw [ddcCoordDens, levi_insertNth j u hu w ζ]
  simp only [uPair]
  ring

/- English proof (translation)
Introduce `D j u hu hs`. Take `⟨hI, hE⟩` from `greenParam_thm (Fin D → ℂ) (volume : Measure (Fin D → ℂ)) (uPair j u) (uPair_contDiff j hu) (uPair_hasCompactSupport j hs)`. Establish `hπ : Real.pi ≠ 0` using `Real.pi_ne_zero`. Establish `hmp` using `(volume_preserving_piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) j).symm`. Use `set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) j with he_def`.

Establish `he : ∀ q : ℂ × (Fin D → ℂ), e.symm q = Fin.insertNth j q.1 q.2` using `fun q => by`. Rewrite using `[he_def, MeasurableEquiv.piFinSuccAbove_symm_apply]`. Both sides reduce to the same expression. Establish `hg : (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) ∘ e.symm = fun q => (1 / (2 * Real.pi)) * (Real.log ‖q.1‖ * Δ (fun w' : ℂ => uPair j u (w', q.2)) q.1)`. Use function extensionality and compare the values at `q`.

Simplify using `only [Function.comp_apply, he]`. Rewrite using `[Fin.insertNth_apply_same, ddcCoordDens_insertNth j hu]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hmp.integrable_comp_emb e.symm.measurableEmbedding, hg, Measure.volume_eq_prod]`.

Conclude with `hI.const_mul _`. Establish `h1` using `hmp.integral_comp' (f := e.symm) (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z)`. Rewrite using `[← h1]`. Establish `h2 : (fun q => (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) (e.symm q)) = fun q => (1 / (2 * Real.pi)) * (Real.log ‖q.1‖ * Δ (fun w' : ℂ => uPair j u (w', q.2)) q.1)` using `hg`. Rewrite using `[h2, Measure.volume_eq_prod, integral_const_mul, hE]`.

Simplify using `only [uPair]`. Clear the denominators using the available nonvanishing facts.
-/
theorem greenCoord_thm : GreenCoordStatement := by
  intro D j u hu hs
  obtain ⟨hI, hE⟩ := greenParam_thm (Fin D → ℂ) (volume : Measure (Fin D → ℂ)) (uPair j u)
    (uPair_contDiff j hu) (uPair_hasCompactSupport j hs)
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) j).symm
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) j with he_def
  have he : ∀ q : ℂ × (Fin D → ℂ), e.symm q = Fin.insertNth j q.1 q.2 := fun q => by
    rw [he_def, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hg : (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) ∘ e.symm =
      fun q => (1 / (2 * Real.pi)) * (Real.log ‖q.1‖ * Δ (fun w' : ℂ => uPair j u (w', q.2)) q.1) := by
    funext q
    simp only [Function.comp_apply, he]
    rw [Fin.insertNth_apply_same, ddcCoordDens_insertNth j hu]
    ring
  refine ⟨?_, ?_⟩
  · rw [← hmp.integrable_comp_emb e.symm.measurableEmbedding, hg, Measure.volume_eq_prod]
    exact hI.const_mul _
  · have h1 := hmp.integral_comp' (f := e.symm)
      (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z)
    rw [← h1]
    have h2 : (fun q => (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) (e.symm q)) =
        fun q => (1 / (2 * Real.pi)) * (Real.log ‖q.1‖ * Δ (fun w' : ℂ => uPair j u (w', q.2)) q.1) := hg
    rw [h2, Measure.volume_eq_prod, integral_const_mul, hE]
    simp only [uPair]
    field_simp

/- English proof (translation)
Establish `hl : LocallyIntegrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖) volume` using `locallyIntegrable_comp_eval_fin j logNormLocIntC_thm`. Simplify `hl.integrable_smul_right_of_hasCompactSupport hφ hs` using `only [smul_eq_mul]`.
-/
theorem integrable_log_coord_mul {D : ℕ} (j : Fin (D + 1)) {φ : (Fin (D + 1) → ℂ) → ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * φ z) := by
  have hl : LocallyIntegrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖) volume :=
    locallyIntegrable_comp_eval_fin j logNormLocIntC_thm
  simpa only [smul_eq_mul] using hl.integrable_smul_right_of_hasCompactSupport hφ hs

/- English proof (translation)
Use `set f : (Fin (D + 1) → ℂ) → ℝ := fun z => Real.log ‖z j‖ with hf`. Establish `hfl : LocallyIntegrable f volume` using `logCoordLocInt_thm (D + 1) j`. Establish `hfm : AEStronglyMeasurable f volume` using `hfl.aestronglyMeasurable`. Establish `hgc : Continuous g` using `hg.continuous`. Establish `hg' : Continuous (fderiv ℝ g)` using `hg.continuous_fderiv one_ne_zero`.

Establish `hdiff : Differentiable ℝ g` using `hg.differentiable one_ne_zero`. Establish `hfs : HasCompactSupport (fderiv ℝ g)` using `hs.fderiv ℝ`. Take `⟨C, hC⟩` from `(hg'.clm_apply continuous_const : Continuous fun z => fderiv ℝ g z x ).bounded_above_of_compact_support (hs.fderiv_apply ℝ x)`. Use `set K : Set (Fin (D + 1) → ℂ) := tsupport (fderiv ℝ g) + Metric.closedBall (0 : Fin (D + 1) → ℂ) ‖x‖ with hKdef`. Establish `hK : IsCompact K` using `hfs.isCompact.add (isCompact_closedBall _ _)`.

Use `set F : ℝ → (Fin (D + 1) → ℂ) → ℝ := fun t z => f z * g (z + t • x) with hF`. Use `set F' : ℝ → (Fin (D + 1) → ℂ) → ℝ := fun t z => f z * fderiv ℝ g (z + t • x) x with hF'`. Establish `hconst : ∀ t, ∫ z, F t z = ∫ z, f z * g z`. Introduce `t`. Establish `h : ∀ z, F t z = (fun z => f z * g z) (z + t • x)`.

Introduce `z`. Simplify using `[hF, hf, hx]`. Repeatedly rewrite using `[h]`. Conclude with `integral_add_right_eq_self (fun z => f z * g z) (t • x)`. Establish `hmeas : ∀ᶠ t in nhds (0 : ℝ), AEStronglyMeasurable (F t) volume` using `Filter.Eventually.of_forall fun t => hfm.mul (hgc.comp (continuous_id.add continuous_const)).aestronglyMeasurable`.

Establish `hint : Integrable (F 0) volume`. Simplify `integrable_log_coord_mul j hgc hs` using `[hF]`. Establish `hmeas' : AEStronglyMeasurable (F' 0) volume` using `hfm.mul (((hg'.comp (continuous_id.add continuous_const)).clm_apply continuous_const).aestronglyMeasurable)`. Establish `hbound : ∀ᵐ z ∂(volume : Measure (Fin (D + 1) → ℂ)), ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t z‖ ≤ K.indicator (fun z => C * ‖f z‖) z`. Use `Filter.Eventually.of_forall fun z t ht => ?_` and prove the remaining obligations.

Distinguish the cases in `hz : z ∈ K`. Rewrite using `[Set.indicator_of_mem hz, hF', norm_mul, mul_comm C]`. Conclude with `mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)`. Rewrite using `[Set.indicator_of_notMem hz]`. Establish `h0 : fderiv ℝ g (z + t • x) = 0`.

Apply `image_eq_zero_of_notMem_tsupport` to reduce the goal to its premises. Introduce `hmem`. Apply `hz` to reduce the goal to its premises. Use `Set.mem_add.2 ⟨z + t • x, hmem, -(t • x), ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, dist_zero_right, norm_neg, norm_smul]`.

Establish `ht' : ‖t‖ < 1` using `by simpa using ht`. Use polynomial arithmetic with `[norm_nonneg x, norm_nonneg t]`. Simplify using `[hF', h0]`. Establish `hboundint : Integrable (K.indicator fun z => C * ‖f z‖) volume` using `(integrable_indicator_iff hK.measurableSet).2 ((hfl.integrableOn_isCompact hK).norm.const_mul C)`. Establish `hd : ∀ᵐ z ∂(volume : Measure (Fin (D + 1) → ℂ)), ∀ t ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (fun t => F t z) (F' t z) t`.

Use `Filter.Eventually.of_forall fun z t _ => ?_` and prove the remaining obligations. Establish `h1 : HasDerivAt (fun t : ℝ => z + t • x) x t`. Simplify using `using ((hasDerivAt_id t).smul_const x).const_add z`. Establish `h2` using `(hdiff (z + t • x)).hasFDerivAt.comp_hasDerivAt t h1`. Conclude with `h2.const_mul (f z)`.

Take `⟨-, hder⟩` from `hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds (0 : ℝ) one_pos) hmeas hint hmeas' hbound hboundint hd`. Establish `hc : HasDerivAt (fun t => ∫ z, F t z) 0 0`. Repeatedly rewrite using `[hconst]`. Conclude with `hasDerivAt_const _ _`. Use `hder.unique hc` as an intermediate fact.

Simplify `this` using `[hF']`.
-/
theorem integral_log_coord_mul_fderiv {D : ℕ} (j : Fin (D + 1)) {g : (Fin (D + 1) → ℂ) → ℝ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) {x : Fin (D + 1) → ℂ} (hx : x j = 0) :
    ∫ z, Real.log ‖z j‖ * fderiv ℝ g z x = 0 := by
  set f : (Fin (D + 1) → ℂ) → ℝ := fun z => Real.log ‖z j‖ with hf
  have hfl : LocallyIntegrable f volume := logCoordLocInt_thm (D + 1) j
  have hfm : AEStronglyMeasurable f volume := hfl.aestronglyMeasurable
  have hgc : Continuous g := hg.continuous
  have hg' : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hfs : HasCompactSupport (fderiv ℝ g) := hs.fderiv ℝ
  obtain ⟨C, hC⟩ := (hg'.clm_apply continuous_const : Continuous fun z => fderiv ℝ g z x
    ).bounded_above_of_compact_support (hs.fderiv_apply ℝ x)
  set K : Set (Fin (D + 1) → ℂ) := tsupport (fderiv ℝ g) + Metric.closedBall (0 : Fin (D + 1) → ℂ) ‖x‖ with hKdef
  have hK : IsCompact K := hfs.isCompact.add (isCompact_closedBall _ _)
  set F : ℝ → (Fin (D + 1) → ℂ) → ℝ := fun t z => f z * g (z + t • x) with hF
  set F' : ℝ → (Fin (D + 1) → ℂ) → ℝ := fun t z => f z * fderiv ℝ g (z + t • x) x with hF'
  have hconst : ∀ t, ∫ z, F t z = ∫ z, f z * g z := by
    intro t
    have h : ∀ z, F t z = (fun z => f z * g z) (z + t • x) := by
      intro z; simp [hF, hf, hx]
    simp_rw [h]
    exact integral_add_right_eq_self (fun z => f z * g z) (t • x)
  have hmeas : ∀ᶠ t in nhds (0 : ℝ), AEStronglyMeasurable (F t) volume :=
    Filter.Eventually.of_forall fun t =>
      hfm.mul (hgc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hint : Integrable (F 0) volume := by
    simpa [hF] using integrable_log_coord_mul j hgc hs
  have hmeas' : AEStronglyMeasurable (F' 0) volume :=
    hfm.mul (((hg'.comp (continuous_id.add continuous_const)).clm_apply
      continuous_const).aestronglyMeasurable)
  have hbound : ∀ᵐ z ∂(volume : Measure (Fin (D + 1) → ℂ)), ∀ t ∈ Metric.ball (0 : ℝ) 1,
      ‖F' t z‖ ≤ K.indicator (fun z => C * ‖f z‖) z := by
    refine Filter.Eventually.of_forall fun z t ht => ?_
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz, hF', norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hz]
      have h0 : fderiv ℝ g (z + t • x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        apply hz
        refine Set.mem_add.2 ⟨z + t • x, hmem, -(t • x), ?_, by simp⟩
        rw [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_smul]
        have ht' : ‖t‖ < 1 := by simpa using ht
        nlinarith [norm_nonneg x, norm_nonneg t]
      simp [hF', h0]
  have hboundint : Integrable (K.indicator fun z => C * ‖f z‖) volume :=
    (integrable_indicator_iff hK.measurableSet).2 ((hfl.integrableOn_isCompact hK).norm.const_mul C)
  have hd : ∀ᵐ z ∂(volume : Measure (Fin (D + 1) → ℂ)), ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t => F t z) (F' t z) t := by
    refine Filter.Eventually.of_forall fun z t _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => z + t • x) x t := by
      simpa using ((hasDerivAt_id t).smul_const x).const_add z
    have h2 := (hdiff (z + t • x)).hasFDerivAt.comp_hasDerivAt t h1
    exact h2.const_mul (f z)
  obtain ⟨-, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) hmeas hint hmeas' hbound hboundint hd
  have hc : HasDerivAt (fun t => ∫ z, F t z) 0 0 := by
    simp_rw [hconst]; exact hasDerivAt_const _ _
  have := hder.unique hc
  simpa [hF'] using this

/- English proof (translation)
Establish `hu1 : ContDiff ℝ 1 (fderiv ℝ u)` using `hu.fderiv_right (by norm_num)`. Establish `hH : Continuous (fderiv ℝ (fderiv ℝ u))` using `hu1.continuous_fderiv one_ne_zero`. Use `⟨integrable_log_coord_mul j ((hH.clm_apply continuous_const).clm_apply continuous_const) (((hs.fderiv ℝ).fderiv_apply ℝ v).comp_left (g := fun L : (Fin (D + 1) → ℂ) →L[ℝ] ℝ => L w) (by simp)), ?_⟩` and prove the remaining obligations. Establish `key : ∀ v w : Fin (D + 1) → ℂ, v j = 0 → ∫ z, Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z v w = 0`. Introduce `v w hv`.

Establish `hg : ContDiff ℝ 1 (fun z => fderiv ℝ u z w)` using `hu1.clm_apply contDiff_const`. Establish `hgs : HasCompactSupport (fun z => fderiv ℝ u z w)` using `hs.fderiv_apply ℝ w`. Rewrite using `[← integral_log_coord_mul_fderiv j hg hgs hv]`. Use `congr 1`. Use function extensionality and compare the values at `z`.

Use `congr 1`. Rewrite using `[fderiv_clm_apply ((hu1.differentiable one_ne_zero) z) (differentiableAt_const w)]`. Simplify using the standard rewrite rules. Break down `h with hv | hw` into its components or cases. Conclude with `key v w hv`.

Establish `hsym : ∀ z, fderiv ℝ (fderiv ℝ u) z v w = fderiv ℝ (fderiv ℝ u) z w v` using `fun z => (hu.contDiffAt.isSymmSndFDerivAt (by simp)) v w`. Repeatedly rewrite using `[hsym]`. Conclude with `key w v hw`.
-/
theorem log_coord_mul_hess {D : ℕ} (j : Fin (D + 1)) {u : (Fin (D + 1) → ℂ) → ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u) (v w : Fin (D + 1) → ℂ)
    (h : v j = 0 ∨ w j = 0) :
    Integrable (fun z => Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z v w) ∧
      ∫ z, Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z v w = 0 := by
  have hu1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hH : Continuous (fderiv ℝ (fderiv ℝ u)) := hu1.continuous_fderiv one_ne_zero
  refine ⟨integrable_log_coord_mul j ((hH.clm_apply continuous_const).clm_apply continuous_const)
    (((hs.fderiv ℝ).fderiv_apply ℝ v).comp_left
      (g := fun L : (Fin (D + 1) → ℂ) →L[ℝ] ℝ => L w) (by simp)), ?_⟩
  have key : ∀ v w : Fin (D + 1) → ℂ, v j = 0 →
      ∫ z, Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z v w = 0 := by
    intro v w hv
    have hg : ContDiff ℝ 1 (fun z => fderiv ℝ u z w) := hu1.clm_apply contDiff_const
    have hgs : HasCompactSupport (fun z => fderiv ℝ u z w) := hs.fderiv_apply ℝ w
    rw [← integral_log_coord_mul_fderiv j hg hgs hv]
    congr 1; funext z; congr 1
    rw [fderiv_clm_apply ((hu1.differentiable one_ne_zero) z) (differentiableAt_const w)]
    simp
  rcases h with hv | hw
  · exact key v w hv
  · have hsym : ∀ z, fderiv ℝ (fderiv ℝ u) z v w = fderiv ℝ (fderiv ℝ u) z w v :=
      fun z => (hu.contDiffAt.isSymmSndFDerivAt (by simp)) v w
    simp_rw [hsym]
    exact key w v hw

/- English proof (translation)
Introduce `D j a b u hu hs hab`. Establish `hcase : ((Pi.single a 1 : Fin (D + 1) → ℂ) j = 0 ∧ (Complex.I • (Pi.single a 1 : Fin (D + 1) → ℂ)) j = 0) ∨ ((Pi.single b 1 : Fin (D + 1) → ℂ) j = 0 ∧ (Complex.I • (Pi.single b 1 : Fin (D + 1) → ℂ)) j = 0)`. Distinguish the cases in `ha : j = a`. Substitute `ha` using the available equality. Establish `hb : j ≠ b` using `fun h => hab (by rw [← h])`.

Use `right`. Simplify using `[Pi.single_eq_of_ne hb]`. Use `left`. Simplify using `[Pi.single_eq_of_ne ha]`. Establish `hvw : ∀ v w : Fin (D + 1) → ℂ, (v = Pi.single a 1 ∨ v = Complex.I • Pi.single a 1) → (w = Pi.single b 1 ∨ w = Complex.I • Pi.single b 1) → v j = 0 ∨ w j = 0`.

Apply the tactic sequence `rintro v w (rfl | rfl) (rfl | rfl) <;> tauto`. Take `⟨i1, e1⟩` from `log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inl rfl) (Or.inl rfl))`. Take `⟨i2, e2⟩` from `log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inr rfl) (Or.inr rfl))`. Take `⟨i3, e3⟩` from `log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inl rfl) (Or.inr rfl))`. Take `⟨i4, e4⟩` from `log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inr rfl) (Or.inl rfl))`.

Establish `hfun : (fun z : Fin (D + 1) → ℂ => (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b) = fun z => (((Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z (Pi.single a 1) (Pi.single b 1) + Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z (Complex.I • Pi.single a 1) (Complex.I • Pi.single b …`. Use function extensionality and compare the values at `z`. Simplify using `only [ReciprocityTheory.AnForm.hessC]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hfun]`. Use `⟨((i1.add i2).div_const 4).ofReal.add (((i3.sub i4).div_const 4).ofReal.const_mul _), ?_⟩` and prove the remaining obligations. Rewrite using `[integral_add ((i1.add i2).div_const 4).ofReal (((i3.sub i4).div_const 4).ofReal.const_mul _), integral_const_mul, integral_complex_ofReal, integral_complex_ofReal, integral_div, integral_div, integral_add i1 i2, integral_sub i3 i4, e1, e2, e3, e4]`. Simplify using the standard rewrite rules.
-/
theorem greenMixed_thm : GreenMixedStatement := by
  intro D j a b u hu hs hab
  have hcase : ((Pi.single a 1 : Fin (D + 1) → ℂ) j = 0 ∧
        (Complex.I • (Pi.single a 1 : Fin (D + 1) → ℂ)) j = 0) ∨
      ((Pi.single b 1 : Fin (D + 1) → ℂ) j = 0 ∧
        (Complex.I • (Pi.single b 1 : Fin (D + 1) → ℂ)) j = 0) := by
    by_cases ha : j = a
    · subst ha
      have hb : j ≠ b := fun h => hab (by rw [← h])
      right; simp [Pi.single_eq_of_ne hb]
    · left; simp [Pi.single_eq_of_ne ha]
  have hvw : ∀ v w : Fin (D + 1) → ℂ,
      (v = Pi.single a 1 ∨ v = Complex.I • Pi.single a 1) →
      (w = Pi.single b 1 ∨ w = Complex.I • Pi.single b 1) → v j = 0 ∨ w j = 0 := by
    rintro v w (rfl | rfl) (rfl | rfl) <;> tauto
  obtain ⟨i1, e1⟩ := log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inl rfl) (Or.inl rfl))
  obtain ⟨i2, e2⟩ := log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inr rfl) (Or.inr rfl))
  obtain ⟨i3, e3⟩ := log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inl rfl) (Or.inr rfl))
  obtain ⟨i4, e4⟩ := log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inr rfl) (Or.inl rfl))
  have hfun : (fun z : Fin (D + 1) → ℂ =>
      (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b) = fun z =>
      (((Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z (Pi.single a 1) (Pi.single b 1) +
        Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z (Complex.I • Pi.single a 1)
          (Complex.I • Pi.single b 1)) / 4 : ℝ) : ℂ) +
      Complex.I * (((Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z (Pi.single a 1)
          (Complex.I • Pi.single b 1) -
        Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z (Complex.I • Pi.single a 1)
          (Pi.single b 1)) / 4 : ℝ) : ℂ) := by
    funext z
    simp only [ReciprocityTheory.AnForm.hessC]
    push_cast
    ring
  rw [hfun]
  refine ⟨((i1.add i2).div_const 4).ofReal.add (((i3.sub i4).div_const 4).ofReal.const_mul _), ?_⟩
  rw [integral_add ((i1.add i2).div_const 4).ofReal
      (((i3.sub i4).div_const 4).ofReal.const_mul _), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, integral_div, integral_div, integral_add i1 i2, integral_sub i3 i4, e1, e2,
    e3, e4]
  simp

end

end ReciprocityTheory.AnForm.A

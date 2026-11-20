import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
import Mathlib

open MeasureTheory Set Filter Topology

noncomputable section

namespace MainStatements.WeightKernel.PClosedGraph

variable {Ω I : Type} [MeasurableSpace Ω] {m : Measure Ω} {u : I → Ω → ℂ}

/- English proof (translation)
Establish `h` using `(memℓp_gen_iff (p := (1 : ENNReal)) (by norm_num)).1 (lp.memℓp a)`. Simplify using `using h`.
-/
lemma summable_norm_lp (a : lp (fun _ : I => ℂ) 1) : Summable (fun i => ‖a i‖) := by
  have h := (memℓp_gen_iff (p := (1 : ENNReal)) (by norm_num)).1 (lp.memℓp a)
  simpa using h

/- English proof (translation)
Rewrite using `[lp.norm_eq_tsum_rpow (by norm_num)]`. Simplify using the standard rewrite rules.
-/
lemma norm_lp_eq (a : lp (fun _ : I => ℂ) 1) : ‖a‖ = ∑' i, ‖a i‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

/- English proof (translation)
Use `Summable.of_norm_bounded (ha.mul_right M) fun i => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)`.
-/
lemma summable_mul {x : Ω} {M : ℝ} (hM : ∀ i, ‖u i x‖ ≤ M) (a : I → ℂ) (ha : Summable fun i => ‖a i‖) :
    Summable (fun i => a i * u i x) := by
  refine Summable.of_norm_bounded (ha.mul_right M) fun i => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)

/- English proof (translation)
Establish `ha` using `summable_norm_lp a`. Establish `hs` using `summable_mul hM a ha`. Combine the equalities or inequalities in the displayed calculation. Use `Summable.tsum_le_tsum (fun i => ?_) hs.norm (ha.mul_right M)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)`. Use `_ = ‖a‖ * M := by rw [tsum_mul_right, norm_lp_eq]`.
-/
lemma norm_tsum_mul_le {x : Ω} {M : ℝ} (hM : ∀ i, ‖u i x‖ ≤ M) (a : lp (fun _ : I => ℂ) 1) :
    ‖∑' i, a i * u i x‖ ≤ ‖a‖ * M := by
  have ha := summable_norm_lp a
  have hs := summable_mul hM a ha
  calc ‖∑' i, a i * u i x‖ ≤ ∑' i, ‖a i * u i x‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' i, ‖a i‖ * M := by
        refine Summable.tsum_le_tsum (fun i => ?_) hs.norm (ha.mul_right M)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)
    _ = ‖a‖ * M := by rw [tsum_mul_right, norm_lp_eq]

/- English proof (translation)
Rewrite using `[tsum_eq_single i]`. Simplify using `[lp.single_apply]`. Introduce `j hj`. Simplify using `[lp.single_apply, Pi.single_apply, hj]`.
-/
lemma tsum_single [DecidableEq I] (i : I) (x : Ω) : ∑' j, (lp.single 1 i (1 : ℂ) : lp (fun _ : I => ℂ) 1) j * u j x = u i x := by
  rw [tsum_eq_single i]
  · simp [lp.single_apply]
  · intro j hj
    simp [lp.single_apply, Pi.single_apply, hj]

end MainStatements.WeightKernel.PClosedGraph

open MainStatements.WeightKernel.PClosedGraph in
/- English proof (translation)
Introduce `Ω I _ m u hbd hint`. Use `choose M hM using hbd`. Set `Tf : lp (fun _ : I => ℂ) 1 → Ω → ℂ` to `fun a x => ∑' i, a i * u i x`. Establish `hTi : ∀ a : lp (fun _ : I => ℂ) 1, Integrable (Tf a) m` using `fun a => hint a (summable_norm_lp a)`. Establish `hadd : ∀ a b : lp (fun _ : I => ℂ) 1, Tf (a + b) = Tf a + Tf b`.

Introduce `a b`. Use function extensionality and compare the values at `x`. Simplify using `only [Tf, Pi.add_apply, lp.coeFn_add, add_mul]`. Conclude with `Summable.tsum_add (summable_mul (hM x) a (summable_norm_lp a)) (summable_mul (hM x) b (summable_norm_lp b))`. Establish `hsmul : ∀ (c : ℂ) (a : lp (fun _ : I => ℂ) 1), Tf (c • a) = fun x => c • Tf a x`.

Introduce `c a`. Use function extensionality and compare the values at `x`. Simplify using `only [Tf, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `tsum_mul_left`. Set `T : lp (fun _ : I => ℂ) 1 →ₗ[ℂ] Lp ℂ 1 m` to `{ toFun := fun a => Integrable.toL1 (Tf a) (hTi a) map_add' := by`.

Introduce `a b`. Rewrite using `[← Integrable.toL1_add, Integrable.toL1_eq_toL1_iff]`. Conclude with `Filter.Eventually.of_forall (congrFun (hadd a b))`. Use the proof step `map_smul' := by`. Introduce `c a`.

Simplify using `only [RingHom.id_apply]`. Rewrite using `[← Integrable.toL1_smul, Integrable.toL1_eq_toL1_iff]`. Conclude with `Filter.Eventually.of_forall (congrFun (hsmul c a)) }`. Establish `hTapp : ∀ a, T a = Integrable.toL1 (Tf a) (hTi a)` using `fun a => rfl`. Establish `hcont : Continuous T`.

Use `T.continuous_of_seq_closed_graph fun s a y hs hy => ?_` and prove the remaining obligations. Establish `hmeas` using `tendstoInMeasure_of_tendsto_Lp hy`. Take `⟨ns, hns, hae⟩` from `hmeas.exists_seq_tendsto_ae`. Apply `Lp.ext` to reduce the goal to its premises. Use `filter_upwards [hae, (hTi a).coeFn_toL1, ae_all_iff.2 (fun n => (hTi (s n)).coeFn_toL1)] with x hx1 hx2 hx3`.

Rewrite using `[hTapp a, hx2]`. Establish `hpt : Tendsto (fun n => Tf (s n) x) atTop (𝓝 (Tf a x))`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `hlim : Tendsto (fun n => ‖s n - a‖ * M x) atTop (𝓝 0)`. Establish `h0 : Tendsto (fun n => ‖s n - a‖) atTop (𝓝 0)`.

Rewrite using `[← tendsto_iff_norm_sub_tendsto_zero]`. Conclude with `hs`. Simplify using `using h0.mul_const (M x)`. Use `squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim` and prove the remaining obligations. Establish `e : Tf (s n) x - Tf a x = Tf (s n - a) x`.

Use `congrFun (hadd (s n - a) a) x` as an intermediate fact. Simplify using `only [sub_add_cancel, Pi.add_apply] at this`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `norm_tsum_mul_le (hM x) (s n - a)`. Establish `hsub` using `hpt.comp hns.tendsto_atTop`. Use `tendsto_nhds_unique hx1 ?_` and prove the remaining obligations. Use `hsub.congr fun n => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[hTapp, hx3]`. Set `T' : lp (fun _ : I => ℂ) 1 →L[ℂ] Lp ℂ 1 m` to `⟨T, hcont⟩`. Use `⟨‖T'‖, fun i => ?_⟩` and prove the remaining obligations. Set `e : lp (fun _ : I => ℂ) 1` to `lp.single 1 i (1 : ℂ)`. Establish `hTe : Tf e = u i` using `funext fun x => tsum_single i x`.

Establish `hint_i : Integrable (u i) m` using `hTe ▸ hTi e`. Use `⟨hint_i, ?_⟩` and prove the remaining obligations. Establish `hn : ‖T e‖ = ∫ x, ‖u i x‖ ∂m`. Rewrite using `[L1.norm_eq_integral_norm]`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [(hTi e).coeFn_toL1] with x hx`. Rewrite using `[hTapp, hx, hTe]`. Establish `hle : ‖T' e‖ ≤ ‖T'‖ * ‖e‖` using `T'.le_opNorm e`. Establish `he : ‖e‖ = 1`. Rewrite using `[lp.norm_single (by norm_num)]`.

Simplify using the standard rewrite rules. Rewrite using `[← hn]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem MainStatements.WeightKernel.closedGraph : MainStatements.WeightKernel.ClosedGraph := by
  intro Ω I _ m u hbd hint
  choose M hM using hbd
  let Tf : lp (fun _ : I => ℂ) 1 → Ω → ℂ := fun a x => ∑' i, a i * u i x
  have hTi : ∀ a : lp (fun _ : I => ℂ) 1, Integrable (Tf a) m := fun a => hint a (summable_norm_lp a)
  have hadd : ∀ a b : lp (fun _ : I => ℂ) 1, Tf (a + b) = Tf a + Tf b := by
    intro a b
    funext x
    simp only [Tf, Pi.add_apply, lp.coeFn_add, add_mul]
    exact Summable.tsum_add (summable_mul (hM x) a (summable_norm_lp a))
      (summable_mul (hM x) b (summable_norm_lp b))
  have hsmul : ∀ (c : ℂ) (a : lp (fun _ : I => ℂ) 1), Tf (c • a) = fun x => c • Tf a x := by
    intro c a
    funext x
    simp only [Tf, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact tsum_mul_left
  let T : lp (fun _ : I => ℂ) 1 →ₗ[ℂ] Lp ℂ 1 m :=
    { toFun := fun a => Integrable.toL1 (Tf a) (hTi a)
      map_add' := by
        intro a b
        rw [← Integrable.toL1_add, Integrable.toL1_eq_toL1_iff]
        exact Filter.Eventually.of_forall (congrFun (hadd a b))
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply]
        rw [← Integrable.toL1_smul, Integrable.toL1_eq_toL1_iff]
        exact Filter.Eventually.of_forall (congrFun (hsmul c a)) }
  have hTapp : ∀ a, T a = Integrable.toL1 (Tf a) (hTi a) := fun a => rfl
  have hcont : Continuous T := by
    refine T.continuous_of_seq_closed_graph fun s a y hs hy => ?_
    have hmeas := tendstoInMeasure_of_tendsto_Lp hy
    obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
    apply Lp.ext
    filter_upwards [hae, (hTi a).coeFn_toL1, ae_all_iff.2 (fun n => (hTi (s n)).coeFn_toL1)]
      with x hx1 hx2 hx3
    rw [hTapp a, hx2]
    have hpt : Tendsto (fun n => Tf (s n) x) atTop (𝓝 (Tf a x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n => ‖s n - a‖ * M x) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n => ‖s n - a‖) atTop (𝓝 0) := by
          rw [← tendsto_iff_norm_sub_tendsto_zero]
          exact hs
        simpa using h0.mul_const (M x)
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      have e : Tf (s n) x - Tf a x = Tf (s n - a) x := by
        have := congrFun (hadd (s n - a) a) x
        simp only [sub_add_cancel, Pi.add_apply] at this
        rw [this]
        ring
      rw [e]
      exact norm_tsum_mul_le (hM x) (s n - a)
    have hsub := hpt.comp hns.tendsto_atTop
    refine tendsto_nhds_unique hx1 ?_
    refine hsub.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hTapp, hx3]
  let T' : lp (fun _ : I => ℂ) 1 →L[ℂ] Lp ℂ 1 m := ⟨T, hcont⟩
  refine ⟨‖T'‖, fun i => ?_⟩
  classical
  let e : lp (fun _ : I => ℂ) 1 := lp.single 1 i (1 : ℂ)
  have hTe : Tf e = u i := funext fun x => tsum_single i x
  have hint_i : Integrable (u i) m := hTe ▸ hTi e
  refine ⟨hint_i, ?_⟩
  have hn : ‖T e‖ = ∫ x, ‖u i x‖ ∂m := by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [(hTi e).coeFn_toL1] with x hx
    rw [hTapp, hx, hTe]
  have hle : ‖T' e‖ ≤ ‖T'‖ * ‖e‖ := T'.le_opNorm e
  have he : ‖e‖ = 1 := by
    rw [lp.norm_single (by norm_num)]
    simp
  rw [← hn]
  calc ‖T e‖ = ‖T' e‖ := rfl
    _ ≤ ‖T'‖ * ‖e‖ := hle
    _ = ‖T'‖ := by rw [he, mul_one]

import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExtB

open Metric Real Filter Topology MeasureTheory

namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension

section
open ReciprocityTheory.AnForm.A

variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C κ : ℝ}

/- English proof (translation)
Establish `: coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0}`. Use extensionality with `z`. Simplify using `[coordDiv]`. Rewrite using `[this]`. Conclude with `isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const`.
-/
theorem coordDiv_closed (S : Finset (Fin D)) : IsClosed (coordDiv S) := by
  have : coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0} := by
    ext z; simp [coordDiv]
  rw [this]
  exact isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const

/- English proof (translation)
Establish `hT : Tendsto (fun t : ℝ => z + (t : ℂ) • (fun _ => (1 : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 z)`. Establish `: Continuous (fun t : ℝ => z + (t : ℂ) • (fun _ => (1 : ℂ)))` using `by fun_prop`. Simplify using `using (this.tendsto 0).mono_left nhdsWithin_le_nhds`. Establish `hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), z + (t : ℂ) • (fun _ => (1 : ℂ)) ∈ U \ coordDiv S`. Establish `h1` using `hT.eventually (hU.mem_nhds hz)`.

Establish `h2 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ i ∈ S, z i + (t : ℂ) ≠ 0`. Rewrite using `[eventually_all_finset]`. Introduce `i _`. Distinguish the cases in `hzi : z i = 0`. Use `filter_upwards [self_mem_nhdsWithin] with t ht`.

Rewrite using `[hzi, zero_add]`. Conclude with `(ne_of_gt ht)` after adjusting the coercions. Establish `hc : Tendsto (fun t : ℝ => z i + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (z i))`. Establish `: Continuous (fun t : ℝ => z i + (t : ℂ))` using `by fun_prop`. Simplify using `using (this.tendsto 0).mono_left nhdsWithin_le_nhds`.

Conclude with `hc.eventually_ne hzi`. Use `filter_upwards [h1, h2] with t ht1 ht2`. Use `⟨ht1, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨i, hi, h0⟩`. Apply `ht2 i hi` to reduce the goal to its premises.

Simplify using `using h0`. Conclude with `(tendsto_nhdsWithin_iff.2 ⟨hT, hev⟩).neBot`.
-/
theorem nebot_diff (hU : IsOpen U) {z : Fin D → ℂ} (hz : z ∈ U) :
    (𝓝[U \ coordDiv S] z).NeBot := by
  have hT : Tendsto (fun t : ℝ => z + (t : ℂ) • (fun _ => (1 : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have : Continuous (fun t : ℝ => z + (t : ℂ) • (fun _ => (1 : ℂ))) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), z + (t : ℂ) • (fun _ => (1 : ℂ)) ∈ U \ coordDiv S := by
    have h1 := hT.eventually (hU.mem_nhds hz)
    have h2 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ i ∈ S, z i + (t : ℂ) ≠ 0 := by
      rw [eventually_all_finset]
      intro i _
      by_cases hzi : z i = 0
      · filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hzi, zero_add]
        exact_mod_cast (ne_of_gt ht)
      · have hc : Tendsto (fun t : ℝ => z i + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (z i)) := by
          have : Continuous (fun t : ℝ => z i + (t : ℂ)) := by fun_prop
          simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
        exact hc.eventually_ne hzi
    filter_upwards [h1, h2] with t ht1 ht2
    refine ⟨ht1, ?_⟩
    rintro ⟨i, hi, h0⟩
    apply ht2 i hi
    simpa using h0
  exact (tendsto_nhdsWithin_iff.2 ⟨hT, hev⟩).neBot

def trunc (u : (Fin D → ℂ) → ℝ) (κ : ℝ) : (Fin D → ℂ) → ℝ := fun z => max (u z) (-κ)

noncomputable def vext (U : Set (Fin D → ℂ)) (S : Finset (Fin D)) (u : (Fin D → ℂ) → ℝ) (κ : ℝ) :
    (Fin D → ℂ) → ℝ :=
  limsupExt U (coordDiv S) (trunc u κ)

/- English proof (translation)
Unfold `vext limsupExt`. Rewrite using `[if_neg hz]`. Both sides reduce to the same expression.
-/
theorem vext_of_not {z : Fin D → ℂ} (hz : z ∉ coordDiv S) : vext U S u κ z = max (u z) (-κ) := by
  unfold vext limsupExt
  rw [if_neg hz]
  rfl

/- English proof (translation)
Unfold `vext limsupExt`. Rewrite using `[if_pos hz]`.
-/
theorem vext_of_mem {z : Fin D → ℂ} (hz : z ∈ coordDiv S) :
    vext U S u κ z = limsup (trunc u κ) (𝓝[U \ coordDiv S] z) := by
  unfold vext limsupExt
  rw [if_pos hz]

/- English proof (translation)
The claim follows from `continuous_const.add ((continuous_circleMap 0 r).smul continuous_const)`.
-/
theorem cont_circ (x w : Fin D → ℂ) (r : ℝ) : Continuous (fun θ : ℝ => x + circleMap 0 r θ • w) :=
  continuous_const.add ((continuous_circleMap 0 r).smul continuous_const)

section partB

variable (hU : IsOpen U) (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹))
include hU hU1 hc hpsh hg

/- English proof (translation)
Take `⟨ρ, hρ, M, hM⟩` from `local_bound hU hU1 hc hpsh hg hz`. Use `isBoundedUnder_of_eventually_le (a := max M (-κ)) ?_` and prove the remaining obligations. Use `filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z hρ), self_mem_nhdsWithin] with y hy hyV`. Conclude with `max_le_max (hM y ⟨hy, hyV.2⟩) le_rfl`.
-/
theorem trunc_bdd {z : Fin D → ℂ} (hz : z ∈ U) :
    IsBoundedUnder (· ≤ ·) (𝓝[U \ coordDiv S] z) (trunc u κ) := by
  obtain ⟨ρ, hρ, M, hM⟩ := local_bound hU hU1 hc hpsh hg hz
  refine isBoundedUnder_of_eventually_le (a := max M (-κ)) ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z hρ), self_mem_nhdsWithin]
    with y hy hyV
  exact max_le_max (hM y ⟨hy, hyV.2⟩) le_rfl

/- English proof (translation)
Use `nebot_diff (S := S) hU hz` as an intermediate fact. Conclude with `isCoboundedUnder_le_of_le _ (fun y => le_max_right (u y) (-κ))`.
-/
theorem trunc_cobdd {z : Fin D → ℂ} (hz : z ∈ U) :
    IsCoboundedUnder (· ≤ ·) (𝓝[U \ coordDiv S] z) (trunc u κ) := by
  have := nebot_diff (S := S) hU hz
  exact isCoboundedUnder_le_of_le _ (fun y => le_max_right (u y) (-κ))

/- English proof (translation)
Distinguish the cases in `hA : z ∈ coordDiv S`. Rewrite using `[vext_of_mem hA]`. Use `nebot_diff (S := S) hU hz` as an intermediate fact. Use `le_limsup_of_le (trunc_bdd hU hU1 hc hpsh hg hz) (fun b hb => ?_)` and prove the remaining obligations. Take `⟨y, hy⟩` from `hb.exists`.

Conclude with `(le_max_right (u y) (-κ)).trans hy`. Rewrite using `[vext_of_not hA]`. Conclude with `le_max_right _ _`.
-/
theorem vext_ge {z : Fin D → ℂ} (hz : z ∈ U) : -κ ≤ vext U S u κ z := by
  by_cases hA : z ∈ coordDiv S
  · rw [vext_of_mem hA]
    have := nebot_diff (S := S) hU hz
    refine le_limsup_of_le (trunc_bdd hU hU1 hc hpsh hg hz) (fun b hb => ?_)
    obtain ⟨y, hy⟩ := hb.exists
    exact (le_max_right (u y) (-κ)).trans hy
  · rw [vext_of_not hA]; exact le_max_right _ _

/- English proof (translation)
Establish `hVo : IsOpen (U \ coordDiv S)` using `hU.sdiff (coordDiv_closed S)`. Introduce `z hz b hb`. Distinguish the cases in `hA : z ∈ coordDiv S`. Rewrite `hb` using `[vext_of_mem hA]`. Take `⟨c, hc1, hc2⟩` from `exists_between hb`.

Establish `h1` using `eventually_lt_of_limsup_lt hc1 (trunc_bdd hU hU1 hc hpsh hg hz)`. Rewrite `h1` using `[eventually_nhdsWithin_iff]`. Establish `h2` using `h1.eventually_nhds`. Use `filter_upwards [eventually_nhdsWithin_of_eventually_nhds h2, self_mem_nhdsWithin] with y hy hyU`. Distinguish the cases in `hyA : y ∈ coordDiv S`.

Rewrite using `[vext_of_mem hyA]`. Use `lt_of_le_of_lt (limsup_le_of_le (trunc_cobdd hU hU1 hc hpsh hg hyU) ?_) hc2` and prove the remaining obligations. Rewrite using `[eventually_nhdsWithin_iff]`. Conclude with `hy.mono fun y' hy' hy'V => (hy' hy'V).le`. Rewrite using `[vext_of_not hyA]`.

Conclude with `lt_trans (hy.self_of_nhds ⟨hyU, hyA⟩) hc2`. Rewrite `hb` using `[vext_of_not hA]`. Establish `hcz : ContinuousAt (fun x => max (u x) (-κ)) z` using `(hc.sup continuousOn_const).continuousAt (hVo.mem_nhds ⟨hz, hA⟩)`. Establish `h1` using `hcz.eventually (gt_mem_nhds hb)`. Use `filter_upwards [eventually_nhdsWithin_of_eventually_nhds h1, mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds ⟨hz, hA⟩)] with y hy hyV`.

Rewrite using `[vext_of_not hyV.2]`. Conclude with `hy`.
-/
theorem vext_usc : UpperSemicontinuousOn (vext U S u κ) U := by
  have hVo : IsOpen (U \ coordDiv S) := hU.sdiff (coordDiv_closed S)
  intro z hz b hb
  by_cases hA : z ∈ coordDiv S
  · rw [vext_of_mem hA] at hb
    obtain ⟨c, hc1, hc2⟩ := exists_between hb
    have h1 := eventually_lt_of_limsup_lt hc1 (trunc_bdd hU hU1 hc hpsh hg hz)
    rw [eventually_nhdsWithin_iff] at h1
    have h2 := h1.eventually_nhds
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h2, self_mem_nhdsWithin] with y hy hyU
    by_cases hyA : y ∈ coordDiv S
    · rw [vext_of_mem hyA]
      refine lt_of_le_of_lt (limsup_le_of_le (trunc_cobdd hU hU1 hc hpsh hg hyU) ?_) hc2
      rw [eventually_nhdsWithin_iff]
      exact hy.mono fun y' hy' hy'V => (hy' hy'V).le
    · rw [vext_of_not hyA]
      exact lt_trans (hy.self_of_nhds ⟨hyU, hyA⟩) hc2
  · rw [vext_of_not hA] at hb
    have hcz : ContinuousAt (fun x => max (u x) (-κ)) z :=
      (hc.sup continuousOn_const).continuousAt (hVo.mem_nhds ⟨hz, hA⟩)
    have h1 := hcz.eventually (gt_mem_nhds hb)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h1,
      mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds ⟨hz, hA⟩)] with y hy hyV
    rw [vext_of_not hyV.2]
    exact hy

/- English proof (translation)
Take `⟨M, hM⟩` from `UpperSemicontinuousOn.bddAbove_of_isCompact hK ((vext_usc hU hU1 hc hpsh hg).mono hKU)`. Conclude with `⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩`.
-/
theorem vext_bdd {K : Set (Fin D → ℂ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M, ∀ y ∈ K, vext U S u κ y ≤ M := by
  obtain ⟨M, hM⟩ := UpperSemicontinuousOn.bddAbove_of_isCompact hK
    ((vext_usc hU hU1 hc hpsh hg).mono hKU)
  exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩

/- English proof (translation)
The claim follows from `(upperSemicontinuousOn_univ_iff.1 ((vext_usc hU hU1 hc hpsh hg).comp hP.continuousOn (fun θ _ => hPU θ))).measurable`.
-/
theorem vext_circ_meas {P : ℝ → Fin D → ℂ} (hP : Continuous P) (hPU : ∀ θ, P θ ∈ U) :
    Measurable (fun θ => vext U S u κ (P θ)) :=
  (upperSemicontinuousOn_univ_iff.1 ((vext_usc hU hU1 hc hpsh hg).comp hP.continuousOn
    (fun θ _ => hPU θ))).measurable

/- English proof (translation)
Use `set Fs : Finset ℂ := (S.filter (fun i => w i ≠ 0)).image (fun i => -z i / w i) with hFs`. Establish `hnotA : ∀ ζ : ℂ, ζ ∉ Fs → z + ζ • w ∉ coordDiv S`. Introduce and unpack `ζ hζ ⟨i, hi, h0⟩`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0`. Distinguish the cases in `hw : w i = 0`.

Rewrite `h0` using `[hw, mul_zero, add_zero]`. Conclude with `hzA ⟨i, hi, h0⟩`. Apply `hζ` to reduce the goal to its premises. Rewrite using `[hFs, Finset.mem_image]`. Conclude with `⟨i, Finset.mem_filter.2 ⟨hi, hw⟩, (div_eq_iff hw).2 (by linear_combination -h0)⟩`.

Establish `h0F : (0 : ℂ) ∉ Fs`. Rewrite using `[hFs, Finset.mem_image]`. Introduce and unpack `⟨i, hi, h0⟩`. Take `⟨hiS, hw⟩` from `Finset.mem_filter.1 hi`. Rewrite `h0` using `[div_eq_zero_iff, neg_eq_zero]`.

Break down `h0 with h0 | h0` into its components or cases. Conclude with `hzA ⟨i, hiS, h0⟩`. Conclude with `hw h0`. Use `set g : ℂ → ℝ := fun ζ => vext U S u κ (z + ζ • w) with hgdef`. Use `set Dk := (fun ζ : ℂ => z + ζ • w) '' closedBall 0 1 with hDkdef`.

Establish `hDk : IsCompact Dk` using `(isCompact_closedBall _ _).image (by fun_prop)`. Establish `hDkU : Dk ⊆ U`. Introduce and unpack `_ ⟨ζ, hζ, rfl⟩`. Conclude with `hD ζ (mem_closedBall_zero_iff.1 hζ)`. Take `⟨M, hM⟩` from `vext_bdd (κ := κ) hU hU1 hc hpsh hg hDk hDkU`.

Establish `hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r ∧ r < 1 ∧ ∀ f ∈ Fs, ‖f‖ < r ∨ 1 ≤ ‖f‖`. Establish `h1 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r` using `eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds one_pos)`. Establish `h2 : ∀ᶠ r in 𝓝[<] (1 : ℝ), r < 1` using `self_mem_nhdsWithin`. Establish `h3 : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ f ∈ Fs, ‖f‖ < r ∨ 1 ≤ ‖f‖`. Rewrite using `[eventually_all_finset]`.

Introduce `f _`. Distinguish the cases in `hf : ‖f‖ < 1`. Conclude with `(eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds hf)).mono fun r hr => Or.inl hr`. Conclude with `Eventually.of_forall fun r => Or.inr (not_lt.1 hf)`. Use `filter_upwards [h1, h2, h3] with r a b c using ⟨a, b, c⟩`.

Establish `hsm : ∀ r, 0 < r → r < 1 → (∀ f ∈ Fs, ‖f‖ < r ∨ 1 ≤ ‖f‖) → g 0 ≤ circleAverage g 0 r`. Introduce `r hr0 hr1 hrF`. Use `set F := Fs.filter (fun f => ‖f‖ < r) with hF`. Establish `hinV : ∀ ζ ∈ closedBall (0 : ℂ) r, ζ ∉ F → z + ζ • w ∈ U \ coordDiv S`. Introduce `ζ hζ hζF`.

Establish `hζn` using `mem_closedBall_zero_iff.1 hζ`. Use `⟨hD ζ (by linarith), hnotA ζ fun hζs => ?_⟩` and prove the remaining obligations. Break down `hrF ζ hζs with h | h` into its components or cases. Conclude with `hζF (Finset.mem_filter.2 ⟨hζs, h⟩)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hgeq : ∀ ζ ∈ closedBall (0 : ℂ) r, ζ ∉ F → g ζ = max (u (z + ζ • w)) (-κ)`. Introduce `ζ hζ hζF`. Simplify using `only [hgdef]`. Conclude with `vext_of_not (hinV ζ hζ hζF).2`. Establish `hcont : ContinuousOn g (closedBall 0 r \ ↑F)`.

Establish `: ContinuousOn (fun ζ : ℂ => max (u (z + ζ • w)) (-κ)) (closedBall 0 r \ ↑F)` using `(hc.comp (by fun_prop : Continuous fun ζ : ℂ => z + ζ • w).continuousOn (fun ζ hζ => hinV ζ hζ.1 hζ.2)).sup continuousOn_const`. Conclude with `this.congr fun ζ hζ => hgeq ζ hζ.1 hζ.2`. Establish `hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑F → g a ≤ circleAverage g a s`. Introduce `a s hs hsub'`. Establish `hin : ∀ ζ ∈ closedBall a s, z + ζ • w ∈ U \ coordDiv S` using `fun ζ hζ => hinV ζ (ball_subset_closedBall (hsub' hζ).1) (hsub' hζ).2`.

Take `⟨hi, hm⟩` from `psh_line hpsh z w hs hin`. Establish `hgc : CircleIntegrable g a s`. Use `ContinuousOn.circleIntegrable hs.le (hcont.mono fun ζ hζ => ?_)` and prove the remaining obligations. Use `hsub' (sphere_subset_closedBall hζ)` as an intermediate fact. Conclude with `⟨ball_subset_closedBall this.1, this.2⟩`.

Establish `ha` using `hsub' (mem_closedBall_self hs.le)`. Rewrite using `[hgeq a (ball_subset_closedBall ha.1) ha.2]`. Use `max_le (hm.trans (circleAverage_mono hi hgc fun ζ hζ => ?_)) ?_` and prove the remaining obligations. Rewrite `hζ` using `[abs_of_pos hs]`. Use `hsub' (sphere_subset_closedBall hζ)` as an intermediate fact.

Rewrite using `[hgeq ζ (ball_subset_closedBall this.1) this.2]`. Conclude with `le_max_left _ _`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hζ` using `[abs_of_pos hs]`. Use `hsub' (sphere_subset_closedBall hζ)` as an intermediate fact.

Rewrite using `[hgeq ζ (ball_subset_closedBall this.1) this.2]`. Conclude with `le_max_right _ _`. Use `smg hr0 ?_ ?_ hcont ⟨M, fun ζ hζ => hM _ ⟨ζ, ?_, rfl⟩⟩ hsub` and prove the remaining obligations. Introduce `h`. Conclude with `h0F (Finset.mem_filter.1 h).1`.

Introduce `f hf`. Conclude with `mem_ball_zero_iff.2 (Finset.mem_filter.1 hf).2`. Use `mem_closedBall_zero_iff.1 hζ.1` as an intermediate fact. Conclude with `mem_closedBall_zero_iff.2 (by linarith)`. Apply `le_of_forall_pos_le_add` to reduce the goal to its premises.

Introduce `ε hε`. Establish `hPK : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ θ, z + circleMap 0 r θ • w ∈ Dk` using `by filter_upwards [hev] with r hr θ`. Use `⟨circleMap 0 r θ, mem_closedBall_zero_iff.2 ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[norm_circleMap_zero, abs_of_pos hr.1]`. Conclude with `hr.2.1.le`.

Establish `hP0K : ∀ θ, z + circleMap 0 1 θ • w ∈ Dk` using `fun θ => ⟨circleMap 0 1 θ, mem_closedBall_zero_iff.2 (by rw [norm_circleMap_zero]; simp), rfl⟩`. Establish `hlimP : ∀ θ, Tendsto (fun r : ℝ => z + circleMap 0 r θ • w) (𝓝[<] 1) (𝓝 (z + circleMap 0 1 θ • w))`. Introduce `θ`. Establish `hc1 : Continuous fun r : ℝ => circleMap 0 r θ` using `by show Continuous fun r : ℝ => (0 : ℂ) + (r : ℂ) * Complex.exp (θ * Complex.I) fun_prop`. Conclude with `((continuous_const.add (hc1.smul continuous_const)).tendsto 1).mono_left nhdsWithin_le_nhds`.

Establish `hlim` using `avg_lim (vext_usc (κ := κ) hU hU1 hc hpsh hg) hDkU (fun y hy => vext_ge hU hU1 hc hpsh hg (hDkU hy)) hM (fun r θ => z + circleMap 0 r θ • w) (fun θ => z + circleMap 0 1 θ • w) (Eventually.of_forall fun r => cont_circ z w r) (cont_circ z w 1) hPK hP0K hlimP (ε := 2 * π * ε) (by po …`. Take `⟨r, h1, h2⟩` from `(hlim.and hev).exists`. Establish `key : ∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 r θ) ≤ (∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 1 θ)) + 2 * π * ε` using `h1`. Establish `hs` using `hsm r h2.1 h2.2.1 h2.2.2`. Establish `e0 : g 0 = vext U S u κ z` using `by simp [hgdef]`.

Rewrite `hs` using `[e0, circleAverage_def, smul_eq_mul]`. Rewrite using `[circleAverage_def, smul_eq_mul]`. Establish `hpi : 0 < (2 * π)⁻¹` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_add]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem good {z w : Fin D → ℂ} (hzA : z ∉ coordDiv S)
    (hD : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ U) :
    vext U S u κ z ≤ circleAverage (fun ζ => vext U S u κ (z + ζ • w)) 0 1 := by
  set Fs : Finset ℂ := (S.filter (fun i => w i ≠ 0)).image (fun i => -z i / w i) with hFs
  have hnotA : ∀ ζ : ℂ, ζ ∉ Fs → z + ζ • w ∉ coordDiv S := by
    rintro ζ hζ ⟨i, hi, h0⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
    by_cases hw : w i = 0
    · rw [hw, mul_zero, add_zero] at h0
      exact hzA ⟨i, hi, h0⟩
    · apply hζ
      rw [hFs, Finset.mem_image]
      exact ⟨i, Finset.mem_filter.2 ⟨hi, hw⟩, (div_eq_iff hw).2 (by linear_combination -h0)⟩
  have h0F : (0 : ℂ) ∉ Fs := by
    rw [hFs, Finset.mem_image]
    rintro ⟨i, hi, h0⟩
    obtain ⟨hiS, hw⟩ := Finset.mem_filter.1 hi
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact hzA ⟨i, hiS, h0⟩
    · exact hw h0
  set g : ℂ → ℝ := fun ζ => vext U S u κ (z + ζ • w) with hgdef
  set Dk := (fun ζ : ℂ => z + ζ • w) '' closedBall 0 1 with hDkdef
  have hDk : IsCompact Dk := (isCompact_closedBall _ _).image (by fun_prop)
  have hDkU : Dk ⊆ U := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hD ζ (mem_closedBall_zero_iff.1 hζ)
  obtain ⟨M, hM⟩ := vext_bdd (κ := κ) hU hU1 hc hpsh hg hDk hDkU
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r ∧ r < 1 ∧ ∀ f ∈ Fs, ‖f‖ < r ∨ 1 ≤ ‖f‖ := by
    have h1 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r :=
      eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds one_pos)
    have h2 : ∀ᶠ r in 𝓝[<] (1 : ℝ), r < 1 := self_mem_nhdsWithin
    have h3 : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ f ∈ Fs, ‖f‖ < r ∨ 1 ≤ ‖f‖ := by
      rw [eventually_all_finset]
      intro f _
      by_cases hf : ‖f‖ < 1
      · exact (eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds hf)).mono fun r hr => Or.inl hr
      · exact Eventually.of_forall fun r => Or.inr (not_lt.1 hf)
    filter_upwards [h1, h2, h3] with r a b c using ⟨a, b, c⟩
  have hsm : ∀ r, 0 < r → r < 1 → (∀ f ∈ Fs, ‖f‖ < r ∨ 1 ≤ ‖f‖) →
      g 0 ≤ circleAverage g 0 r := by
    intro r hr0 hr1 hrF
    set F := Fs.filter (fun f => ‖f‖ < r) with hF
    have hinV : ∀ ζ ∈ closedBall (0 : ℂ) r, ζ ∉ F → z + ζ • w ∈ U \ coordDiv S := by
      intro ζ hζ hζF
      have hζn := mem_closedBall_zero_iff.1 hζ
      refine ⟨hD ζ (by linarith), hnotA ζ fun hζs => ?_⟩
      rcases hrF ζ hζs with h | h
      · exact hζF (Finset.mem_filter.2 ⟨hζs, h⟩)
      · linarith
    have hgeq : ∀ ζ ∈ closedBall (0 : ℂ) r, ζ ∉ F → g ζ = max (u (z + ζ • w)) (-κ) := by
      intro ζ hζ hζF
      simp only [hgdef]
      exact vext_of_not (hinV ζ hζ hζF).2
    have hcont : ContinuousOn g (closedBall 0 r \ ↑F) := by
      have : ContinuousOn (fun ζ : ℂ => max (u (z + ζ • w)) (-κ)) (closedBall 0 r \ ↑F) :=
        (hc.comp (by fun_prop : Continuous fun ζ : ℂ => z + ζ • w).continuousOn
          (fun ζ hζ => hinV ζ hζ.1 hζ.2)).sup continuousOn_const
      exact this.congr fun ζ hζ => hgeq ζ hζ.1 hζ.2
    have hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑F →
        g a ≤ circleAverage g a s := by
      intro a s hs hsub'
      have hin : ∀ ζ ∈ closedBall a s, z + ζ • w ∈ U \ coordDiv S := fun ζ hζ =>
        hinV ζ (ball_subset_closedBall (hsub' hζ).1) (hsub' hζ).2
      obtain ⟨hi, hm⟩ := psh_line hpsh z w hs hin
      have hgc : CircleIntegrable g a s := by
        refine ContinuousOn.circleIntegrable hs.le (hcont.mono fun ζ hζ => ?_)
        have := hsub' (sphere_subset_closedBall hζ)
        exact ⟨ball_subset_closedBall this.1, this.2⟩
      have ha := hsub' (mem_closedBall_self hs.le)
      rw [hgeq a (ball_subset_closedBall ha.1) ha.2]
      refine max_le (hm.trans (circleAverage_mono hi hgc fun ζ hζ => ?_)) ?_
      · rw [abs_of_pos hs] at hζ
        have := hsub' (sphere_subset_closedBall hζ)
        rw [hgeq ζ (ball_subset_closedBall this.1) this.2]
        exact le_max_left _ _
      · calc -κ = circleAverage (fun _ => -κ) a s := (circleAverage_const _ _ _).symm
          _ ≤ circleAverage g a s := circleAverage_mono
              (continuousOn_const.circleIntegrable hs.le) hgc fun ζ hζ => by
              rw [abs_of_pos hs] at hζ
              have := hsub' (sphere_subset_closedBall hζ)
              rw [hgeq ζ (ball_subset_closedBall this.1) this.2]
              exact le_max_right _ _
    refine smg hr0 ?_ ?_ hcont ⟨M, fun ζ hζ => hM _ ⟨ζ, ?_, rfl⟩⟩ hsub
    · intro h; exact h0F (Finset.mem_filter.1 h).1
    · intro f hf; exact mem_ball_zero_iff.2 (Finset.mem_filter.1 hf).2
    · have := mem_closedBall_zero_iff.1 hζ.1
      exact mem_closedBall_zero_iff.2 (by linarith)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hPK : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ θ, z + circleMap 0 r θ • w ∈ Dk := by
    filter_upwards [hev] with r hr θ
    refine ⟨circleMap 0 r θ, mem_closedBall_zero_iff.2 ?_, rfl⟩
    rw [norm_circleMap_zero, abs_of_pos hr.1]
    exact hr.2.1.le
  have hP0K : ∀ θ, z + circleMap 0 1 θ • w ∈ Dk := fun θ =>
    ⟨circleMap 0 1 θ, mem_closedBall_zero_iff.2 (by rw [norm_circleMap_zero]; simp), rfl⟩
  have hlimP : ∀ θ, Tendsto (fun r : ℝ => z + circleMap 0 r θ • w) (𝓝[<] 1)
      (𝓝 (z + circleMap 0 1 θ • w)) := by
    intro θ
    have hc1 : Continuous fun r : ℝ => circleMap 0 r θ := by
      show Continuous fun r : ℝ => (0 : ℂ) + (r : ℂ) * Complex.exp (θ * Complex.I)
      fun_prop
    exact ((continuous_const.add (hc1.smul continuous_const)).tendsto 1).mono_left
      nhdsWithin_le_nhds
  have hlim := avg_lim (vext_usc (κ := κ) hU hU1 hc hpsh hg) hDkU
    (fun y hy => vext_ge hU hU1 hc hpsh hg (hDkU hy)) hM
    (fun r θ => z + circleMap 0 r θ • w) (fun θ => z + circleMap 0 1 θ • w)
    (Eventually.of_forall fun r => cont_circ z w r) (cont_circ z w 1) hPK hP0K hlimP
    (ε := 2 * π * ε) (by positivity)
  obtain ⟨r, h1, h2⟩ := (hlim.and hev).exists
  have key : ∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 r θ) ≤
      (∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 1 θ)) + 2 * π * ε := h1
  have hs := hsm r h2.1 h2.2.1 h2.2.2
  have e0 : g 0 = vext U S u κ z := by simp [hgdef]
  rw [e0, circleAverage_def, smul_eq_mul] at hs
  rw [circleAverage_def, smul_eq_mul]
  have hpi : 0 < (2 * π)⁻¹ := by positivity
  calc vext U S u κ z ≤ _ := hs
    _ ≤ (2 * π)⁻¹ * ((∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 1 θ)) + 2 * π * ε) :=
        mul_le_mul_of_nonneg_left key hpi.le
    _ = _ := by
        rw [mul_add]
        congr 1
        field_simp

/- English proof (translation)
Use `set Dk := (fun ζ : ℂ => z + ζ • w) '' closedBall 0 1 with hDkdef`. Establish `hDk : IsCompact Dk` using `(isCompact_closedBall _ _).image (by fun_prop)`. Establish `hDkU : Dk ⊆ U`. Introduce and unpack `_ ⟨ζ, hζ, rfl⟩`. Conclude with `hD ζ (mem_closedBall_zero_iff.1 hζ)`.

Take `⟨δ, hδ, hth⟩` from `hDk.exists_thickening_subset_open hU hDkU`. Use `set K2 := (fun p : (Fin D → ℂ) × ℂ => p.1 + p.2 • w) '' (closedBall z (δ / 2) ×ˢ closedBall 0 1) with hK2def`. Establish `hK2 : IsCompact K2` using `((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (by fun_prop)`. Establish `hmem : ∀ x ∈ closedBall z (δ / 2), ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → x + ζ • w ∈ K2` using `fun x hx ζ hζ => ⟨(x, ζ), ⟨hx, mem_closedBall_zero_iff.2 hζ⟩, rfl⟩`. Establish `hK2U : K2 ⊆ U`.

Introduce and unpack `_ ⟨⟨x, ζ⟩, ⟨hx, hζ⟩, rfl⟩`. Apply `hth` to reduce the goal to its premises. Rewrite using `[mem_thickening_iff]`. Use `⟨z + ζ • w, ⟨ζ, hζ, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e : dist (x + ζ • w) (z + ζ • w) = dist x z` using `dist_add_right _ _ _`.

Use `show dist (x + ζ • w) (z + ζ • w) < δ`. Rewrite using `[e]`. Use `mem_closedBall.1 hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨M, hM⟩` from `vext_bdd (κ := κ) hU hU1 hc hpsh hg hK2 hK2U`.

Apply `le_of_forall_pos_le_add` to reduce the goal to its premises. Introduce `ε hε`. Establish `hPK : ∀ᶠ x in 𝓝 z, ∀ θ, x + circleMap 0 1 θ • w ∈ K2` using `by filter_upwards [closedBall_mem_nhds z (half_pos hδ)] with x hx θ`. Conclude with `hmem x hx _ (by rw [norm_circleMap_zero]; simp)`. Establish `hP0K : ∀ θ, z + circleMap 0 1 θ • w ∈ K2` using `fun θ => hmem z (mem_closedBall_self (half_pos hδ).le) _ (by rw [norm_circleMap_zero]; simp)`.

Establish `hlim` using `avg_lim (vext_usc (κ := κ) hU hU1 hc hpsh hg) hK2U (fun y hy => vext_ge hU hU1 hc hpsh hg (hK2U hy)) hM (fun x θ => x + circleMap 0 1 θ • w) (fun θ => z + circleMap 0 1 θ • w) (Eventually.of_forall fun x => cont_circ x w 1) (cont_circ z w 1) hPK hP0K (fun θ => (continuous_add_con …`. Rewrite using `[vext_of_mem hzA]`. Use `limsup_le_of_le (trunc_cobdd hU hU1 hc hpsh hg hzU) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_nhdsWithin_of_eventually_nhds hlim, eventually_nhdsWithin_of_eventually_nhds (closedBall_mem_nhds z (half_pos hδ)), self_mem_nhdsWithin] with x h1 hx hxV`. Establish `hg0` using `good hU hU1 hc hpsh hg (κ := κ) hxV.2 (w := w) (fun ζ hζ => hK2U (hmem x hx ζ hζ))`.

Rewrite `hg0` using `[vext_of_not hxV.2]`. Establish `key : ∫ θ in (0 : ℝ)..2 * π, vext U S u κ (x + circleMap 0 1 θ • w) ≤ (∫ θ in (0 : ℝ)..2 * π, vext U S u κ (z + circleMap 0 1 θ • w)) + 2 * π * ε` using `h1`. Rewrite `hg0` using `[circleAverage_def, smul_eq_mul]`. Rewrite using `[circleAverage_def, smul_eq_mul]`. Establish `hpi : 0 < (2 * π)⁻¹` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_add]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem bad {z w : Fin D → ℂ} (hzU : z ∈ U) (hzA : z ∈ coordDiv S)
    (hD : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ U) :
    vext U S u κ z ≤ circleAverage (fun ζ => vext U S u κ (z + ζ • w)) 0 1 := by
  set Dk := (fun ζ : ℂ => z + ζ • w) '' closedBall 0 1 with hDkdef
  have hDk : IsCompact Dk := (isCompact_closedBall _ _).image (by fun_prop)
  have hDkU : Dk ⊆ U := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hD ζ (mem_closedBall_zero_iff.1 hζ)
  obtain ⟨δ, hδ, hth⟩ := hDk.exists_thickening_subset_open hU hDkU
  set K2 := (fun p : (Fin D → ℂ) × ℂ => p.1 + p.2 • w) '' (closedBall z (δ / 2) ×ˢ closedBall 0 1)
    with hK2def
  have hK2 : IsCompact K2 :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (by fun_prop)
  have hmem : ∀ x ∈ closedBall z (δ / 2), ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → x + ζ • w ∈ K2 := fun x hx ζ hζ =>
    ⟨(x, ζ), ⟨hx, mem_closedBall_zero_iff.2 hζ⟩, rfl⟩
  have hK2U : K2 ⊆ U := by
    rintro _ ⟨⟨x, ζ⟩, ⟨hx, hζ⟩, rfl⟩
    apply hth
    rw [mem_thickening_iff]
    refine ⟨z + ζ • w, ⟨ζ, hζ, rfl⟩, ?_⟩
    have e : dist (x + ζ • w) (z + ζ • w) = dist x z := dist_add_right _ _ _
    show dist (x + ζ • w) (z + ζ • w) < δ
    rw [e]
    have := mem_closedBall.1 hx
    linarith
  obtain ⟨M, hM⟩ := vext_bdd (κ := κ) hU hU1 hc hpsh hg hK2 hK2U
  apply le_of_forall_pos_le_add
  intro ε hε
  have hPK : ∀ᶠ x in 𝓝 z, ∀ θ, x + circleMap 0 1 θ • w ∈ K2 := by
    filter_upwards [closedBall_mem_nhds z (half_pos hδ)] with x hx θ
    exact hmem x hx _ (by rw [norm_circleMap_zero]; simp)
  have hP0K : ∀ θ, z + circleMap 0 1 θ • w ∈ K2 := fun θ =>
    hmem z (mem_closedBall_self (half_pos hδ).le) _ (by rw [norm_circleMap_zero]; simp)
  have hlim := avg_lim (vext_usc (κ := κ) hU hU1 hc hpsh hg) hK2U
    (fun y hy => vext_ge hU hU1 hc hpsh hg (hK2U hy)) hM
    (fun x θ => x + circleMap 0 1 θ • w) (fun θ => z + circleMap 0 1 θ • w)
    (Eventually.of_forall fun x => cont_circ x w 1) (cont_circ z w 1) hPK hP0K
    (fun θ => (continuous_add_const _).tendsto z) (ε := 2 * π * ε) (by positivity)
  rw [vext_of_mem hzA]
  refine limsup_le_of_le (trunc_cobdd hU hU1 hc hpsh hg hzU) ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hlim,
    eventually_nhdsWithin_of_eventually_nhds (closedBall_mem_nhds z (half_pos hδ)),
    self_mem_nhdsWithin] with x h1 hx hxV
  have hg0 := good hU hU1 hc hpsh hg (κ := κ) hxV.2 (w := w)
    (fun ζ hζ => hK2U (hmem x hx ζ hζ))
  rw [vext_of_not hxV.2] at hg0
  have key : ∫ θ in (0 : ℝ)..2 * π, vext U S u κ (x + circleMap 0 1 θ • w) ≤
      (∫ θ in (0 : ℝ)..2 * π, vext U S u κ (z + circleMap 0 1 θ • w)) + 2 * π * ε := h1
  rw [circleAverage_def, smul_eq_mul] at hg0
  rw [circleAverage_def, smul_eq_mul]
  have hpi : 0 < (2 * π)⁻¹ := by positivity
  calc trunc u κ x = max (u x) (-κ) := rfl
    _ ≤ _ := hg0
    _ ≤ (2 * π)⁻¹ * ((∫ θ in (0 : ℝ)..2 * π, vext U S u κ (z + circleMap 0 1 θ • w)) +
          2 * π * ε) := mul_le_mul_of_nonneg_left key hpi.le
    _ = _ := by
        rw [mul_add]
        congr 1
        field_simp

/- English proof (translation)
Use `⟨vext_usc hU hU1 hc hpsh hg, fun z w hD => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `set Dk := (fun ζ : ℂ => z + ζ • w) '' closedBall 0 1 with hDkdef`. Establish `hDk : IsCompact Dk` using `(isCompact_closedBall _ _).image (by fun_prop)`. Establish `hDkU : Dk ⊆ U`. Introduce and unpack `_ ⟨ζ, hζ, rfl⟩`.

Conclude with `hD ζ (mem_closedBall_zero_iff.1 hζ)`. Take `⟨M, hM⟩` from `vext_bdd (κ := κ) hU hU1 hc hpsh hg hDk hDkU`. Establish `hin : ∀ θ, z + circleMap 0 1 θ • w ∈ Dk` using `fun θ => ⟨circleMap 0 1 θ, mem_closedBall_zero_iff.2 (by rw [norm_circleMap_zero]; simp), rfl⟩`. Use `show IntervalIntegrable (fun θ => vext U S u κ (z + circleMap 0 1 θ • w)) volume 0 (2 * π)`. Use `ii_of_bdd (vext_circ_meas hU hU1 hc hpsh hg (cont_circ z w 1) (fun θ => hDkU (hin θ))) (max |M| |κ|) (fun θ => ?_) _ _` and prove the remaining obligations.

Establish `h1` using `hM _ (hin θ)`. Establish `h2` using `vext_ge (κ := κ) hU hU1 hc hpsh hg (hDkU (hin θ))`. Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion. Use `neg_abs_le κ` as an intermediate fact.

Use `le_abs_self κ` as an intermediate fact. Use `le_max_right |M| |κ|` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_abs_self M` as an intermediate fact. Use `le_max_left |M| |κ|` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzU : z ∈ U` using `by simpa using hD 0 (by simp)`. Distinguish the cases in `hzA : z ∈ coordDiv S`. Conclude with `bad hU hU1 hc hpsh hg hzU hzA hD`. Conclude with `good hU hU1 hc hpsh hg hzA hD`.
-/
theorem vext_isPsh : IsPsh U (vext U S u κ) := by
  refine ⟨vext_usc hU hU1 hc hpsh hg, fun z w hD => ⟨?_, ?_⟩⟩
  · set Dk := (fun ζ : ℂ => z + ζ • w) '' closedBall 0 1 with hDkdef
    have hDk : IsCompact Dk := (isCompact_closedBall _ _).image (by fun_prop)
    have hDkU : Dk ⊆ U := by
      rintro _ ⟨ζ, hζ, rfl⟩
      exact hD ζ (mem_closedBall_zero_iff.1 hζ)
    obtain ⟨M, hM⟩ := vext_bdd (κ := κ) hU hU1 hc hpsh hg hDk hDkU
    have hin : ∀ θ, z + circleMap 0 1 θ • w ∈ Dk := fun θ =>
      ⟨circleMap 0 1 θ, mem_closedBall_zero_iff.2 (by rw [norm_circleMap_zero]; simp), rfl⟩
    show IntervalIntegrable (fun θ => vext U S u κ (z + circleMap 0 1 θ • w)) volume 0 (2 * π)
    refine ii_of_bdd (vext_circ_meas hU hU1 hc hpsh hg (cont_circ z w 1)
      (fun θ => hDkU (hin θ))) (max |M| |κ|) (fun θ => ?_) _ _
    have h1 := hM _ (hin θ)
    have h2 := vext_ge (κ := κ) hU hU1 hc hpsh hg (hDkU (hin θ))
    rw [abs_le]
    constructor
    · have := neg_abs_le κ
      have := le_abs_self κ
      have := le_max_right |M| |κ|
      linarith
    · have := le_abs_self M
      have := le_max_left |M| |κ|
      linarith
  · have hzU : z ∈ U := by simpa using hD 0 (by simp)
    by_cases hzA : z ∈ coordDiv S
    · exact bad hU hU1 hc hpsh hg hzU hzA hD
    · exact good hU hU1 hc hpsh hg hzA hD

end partB

end

end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension

namespace ReciprocityTheory.AnForm.A

/- English proof (translation)
Introduce `D S U u C hU hU1 hc hpsh hg`. Conclude with `⟨PlurisubharmonicExtension.part_a hU hU1 hc hpsh hg, fun κ => PlurisubharmonicExtension.vext_isPsh hU hU1 hc hpsh hg⟩`.
-/
theorem pshExtension_thm : PshExtensionStatement := by
  intro D S U u C hU hU1 hc hpsh hg
  exact ⟨PlurisubharmonicExtension.part_a hU hU1 hc hpsh hg, fun κ => PlurisubharmonicExtension.vext_isPsh hU hU1 hc hpsh hg⟩

end ReciprocityTheory.AnForm.A

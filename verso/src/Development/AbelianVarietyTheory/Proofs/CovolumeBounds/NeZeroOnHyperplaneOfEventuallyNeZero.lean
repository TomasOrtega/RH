import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Matrix Set
open scoped ComplexOrder MatrixOrder
namespace GlobalTheory

section

open Filter Metric Function
open scoped Topology

/- English proof (translation)
Introduce `z₀ hz₀`. Use `haveI : ProperSpace E := FiniteDimensional.proper ℂ E`. Take `⟨K, hK, hKU, hc⟩` from `local_compact_nhds (hU.mem_nhds hz₀)`. Establish `hA : Continuous fun p : E × ℝ => L p.2 p.1` using `(hL.comp continuous_snd).clm_apply continuous_fst`. Establish `hM : MapsTo (fun p : E × ℝ => L p.2 p.1) (U ×ˢ Icc 0 1) U` using `fun p hp => hLU _ hp.2 hp.1`.

Establish `h1 : ContinuousOn (fun p : E × ℝ => h (L p.2 p.1)) (U ×ˢ Icc 0 1)` using `hh.continuousOn.comp hA.continuousOn hM`. Establish `h2 : ContinuousOn (fun p : E × ℝ => (fderiv ℂ h (L p.2 p.1)).comp (L p.2)) (U ×ˢ Icc 0 1)` using `((SCV.differentiableOn_fderiv hU hh).continuousOn.comp hA.continuousOn hM).clm_comp (hL.comp continuous_snd).continuousOn`. Establish `hI : Set.uIoc (0 : ℝ) 1 ⊆ Icc 0 1`. Rewrite using `[uIoc_of_le zero_le_one]`. Conclude with `Ioc_subset_Icc_self`.

Establish `h3 : ∀ z ∈ U, ContinuousOn (fun s => h (L s z)) (Icc 0 1)` using `fun z hz => h1.comp (Continuous.prodMk_right z).continuousOn fun s hs => ⟨hz, hs⟩`. Take `⟨C, hC⟩` from `(hc.prod isCompact_Icc).exists_bound_of_continuousOn (h2.mono (prod_mono hKU Subset.rfl))`. Use `(intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (F := fun z s => h (L s z)) (F' := fun z s => (fderiv ℂ h (L s z)).comp (L s)) (bound := fun _ => C) hK ?_ ?_ ?_ ?_ ?_ ?_).differentiableAt.differentiableWithinAt` and prove the remaining obligations. Use `filter_upwards [hU.mem_nhds hz₀] with z hz`. Conclude with `((h3 z hz).mono hI).aestronglyMeasurable measurableSet_uIoc`.

Conclude with `ContinuousOn.intervalIntegrable_of_Icc zero_le_one (h3 z₀ hz₀)`. Conclude with `((h2.comp (Continuous.prodMk_right z₀).continuousOn fun s hs => ⟨hz₀, hs⟩).mono hI).aestronglyMeasurable measurableSet_uIoc`. Conclude with `Eventually.of_forall fun s hs z hz => hC (z, s) ⟨hz, hI hs⟩`. Conclude with `intervalIntegrable_const`. Conclude with `Eventually.of_forall fun s hs z hz => (hh.differentiableAt (hU.mem_nhds (hLU s (hI hs) (hKU hz)))).hasFDerivAt.comp z (L s).hasFDerivAt`.
-/
theorem differentiableOn_intervalIntegral_comp_clm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) {h : E → ℂ}
    (hh : DifferentiableOn ℂ h U) {L : ℝ → E →L[ℂ] E} (hL : Continuous L)
    (hLU : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (L s) U U) :
    DifferentiableOn ℂ (fun z => ∫ s in (0 : ℝ)..1, h (L s z)) U := by
  intro z₀ hz₀
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨K, hK, hKU, hc⟩ := local_compact_nhds (hU.mem_nhds hz₀)
  have hA : Continuous fun p : E × ℝ => L p.2 p.1 := (hL.comp continuous_snd).clm_apply continuous_fst
  have hM : MapsTo (fun p : E × ℝ => L p.2 p.1) (U ×ˢ Icc 0 1) U := fun p hp => hLU _ hp.2 hp.1
  have h1 : ContinuousOn (fun p : E × ℝ => h (L p.2 p.1)) (U ×ˢ Icc 0 1) :=
    hh.continuousOn.comp hA.continuousOn hM
  have h2 : ContinuousOn (fun p : E × ℝ => (fderiv ℂ h (L p.2 p.1)).comp (L p.2)) (U ×ˢ Icc 0 1) :=
    ((SCV.differentiableOn_fderiv hU hh).continuousOn.comp hA.continuousOn hM).clm_comp
      (hL.comp continuous_snd).continuousOn
  have hI : Set.uIoc (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have h3 : ∀ z ∈ U, ContinuousOn (fun s => h (L s z)) (Icc 0 1) := fun z hz =>
    h1.comp (Continuous.prodMk_right z).continuousOn fun s hs => ⟨hz, hs⟩
  obtain ⟨C, hC⟩ := (hc.prod isCompact_Icc).exists_bound_of_continuousOn
    (h2.mono (prod_mono hKU Subset.rfl))
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (F := fun z s => h (L s z)) (F' := fun z s => (fderiv ℂ h (L s z)).comp (L s))
    (bound := fun _ => C) hK ?_ ?_ ?_ ?_ ?_ ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [hU.mem_nhds hz₀] with z hz
    exact ((h3 z hz).mono hI).aestronglyMeasurable measurableSet_uIoc
  · exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one (h3 z₀ hz₀)
  · exact ((h2.comp (Continuous.prodMk_right z₀).continuousOn fun s hs => ⟨hz₀, hs⟩).mono
      hI).aestronglyMeasurable measurableSet_uIoc
  · exact Eventually.of_forall fun s hs z hz => hC (z, s) ⟨hz, hI hs⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun s hs z hz =>
      (hh.differentiableAt (hU.mem_nhds (hLU s (hI hs) (hKU hz)))).hasFDerivAt.comp z
        (L s).hasFDerivAt

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ}

omit [Fintype ι] in

/- English proof (translation)
Introduce `j _`. Break down `eq_or_ne j i with rfl | hj` into its components or cases. Simplify using `using ht`. Simplify `hz j trivial` using `[hj]`.
-/
theorem update_mem_polydisc {z : ι → ℂ} (hz : z ∈ univ.pi fun j => ball (0 : ℂ) (r j)) {i : ι}
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) (r i)) : update z i t ∈ univ.pi fun j => ball (0 : ℂ) (r j) := by
  intro j _
  rcases eq_or_ne j i with rfl | hj
  · simpa using ht
  · simpa [hj] using hz j trivial

/- English proof (translation)
Establish `hU : IsOpen (univ.pi fun j => ball (0 : ℂ) (r j))` using `isOpen_set_pi finite_univ fun _ _ => isOpen_ball`. Set `e : ι → ℂ` to `Pi.single i 1`. Set `L : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)` to `fun s => ContinuousLinearMap.id ℂ _ + ((s : ℂ) - 1) • (ContinuousLinearMap.proj i).smulRight e`. Establish `hL : ∀ s z, L s z = z + ((s : ℂ) - 1) • z i • e` using `fun s z => rfl`. Establish `hL' : ∀ (s : ℝ) z, L s z = update z i (s * z i)`.

Introduce `s z`. Use extensionality with `j`. Break down `eq_or_ne j i with rfl | hj` into its components or cases. Simplify using `[hL, e]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hL, e, hj]`. Establish `hLU : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (L s) (univ.pi fun j => ball (0 : ℂ) (r j)) (univ.pi fun j => ball (0 : ℂ) (r j))`. Introduce `s hs z hz`. Rewrite using `[hL']`. Use `update_mem_polydisc hz ?_` and prove the remaining obligations.

Use `hz i trivial` as an intermediate fact. Rewrite `this`, the goal using `[mem_ball_zero_iff]`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hs.2).trans_lt this`. Establish `hLc : Continuous L` using `by fun_prop`.

Establish `hd` using `SCV.differentiableOn_fderiv_apply hU hf e`. Use `⟨_, differentiableOn_intervalIntegral_comp_clm hU hd hLc hLU, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hc : ContinuousOn (fun s => fderiv ℂ f (L s z) e) (Icc 0 1)` using `hd.continuousOn.comp (hLc.clm_apply continuous_const).continuousOn fun s hs => hLU s hs hz`. Rewrite using `[← intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => f (L s z))]`. Simplify using `[hL', h0 z hz]`.

Introduce `s hs`. Rewrite `hs` using `[uIcc_of_le zero_le_one]`. Establish `h1 : HasDerivAt (fun t : ℂ => z + (t - 1) • z i • e) (z i • e) s`. Simplify using `using (((hasDerivAt_id (s : ℂ)).sub_const 1).smul_const (z i • e)).const_add z`. Establish `h2 : HasFDerivAt f (fderiv ℂ f (L s z)) (z + ((s : ℂ) - 1) • z i • e)` using `(hf.differentiableAt (hU.mem_nhds (hLU s hs hz))).hasFDerivAt`.

Establish `h3` using `(h2.comp_hasDerivAt (s : ℂ) h1).comp_ofReal`. Rewrite `h3` using `[map_smul, smul_eq_mul]`. Conclude with `h3`. Conclude with `ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_const.mul hc)`.
-/
theorem exists_eq_coord_mul_of_vanishing {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (univ.pi fun j => ball 0 (r j))) (i : ι)
    (h0 : ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), f (update z i 0) = 0) :
    ∃ g : (ι → ℂ) → ℂ, DifferentiableOn ℂ g (univ.pi fun j => ball 0 (r j)) ∧
      ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), f z = z i * g z := by
  have hU : IsOpen (univ.pi fun j => ball (0 : ℂ) (r j)) :=
    isOpen_set_pi finite_univ fun _ _ => isOpen_ball
  let e : ι → ℂ := Pi.single i 1
  let L : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ) := fun s =>
    ContinuousLinearMap.id ℂ _ + ((s : ℂ) - 1) • (ContinuousLinearMap.proj i).smulRight e
  have hL : ∀ s z, L s z = z + ((s : ℂ) - 1) • z i • e := fun s z => rfl
  have hL' : ∀ (s : ℝ) z, L s z = update z i (s * z i) := by
    intro s z
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp [hL, e]; ring
    · simp [hL, e, hj]
  have hLU : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (L s) (univ.pi fun j => ball (0 : ℂ) (r j))
      (univ.pi fun j => ball (0 : ℂ) (r j)) := by
    intro s hs z hz
    rw [hL']
    refine update_mem_polydisc hz ?_
    have := hz i trivial
    rw [mem_ball_zero_iff] at this ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans_lt this
  have hLc : Continuous L := by fun_prop
  have hd := SCV.differentiableOn_fderiv_apply hU hf e
  refine ⟨_, differentiableOn_intervalIntegral_comp_clm hU hd hLc hLU, fun z hz => ?_⟩
  have hc : ContinuousOn (fun s => fderiv ℂ f (L s z) e) (Icc 0 1) :=
    hd.continuousOn.comp (hLc.clm_apply continuous_const).continuousOn fun s hs => hLU s hs hz
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => f (L s z))]
  · simp [hL', h0 z hz]
  · intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 : HasDerivAt (fun t : ℂ => z + (t - 1) • z i • e) (z i • e) s := by
      simpa using (((hasDerivAt_id (s : ℂ)).sub_const 1).smul_const (z i • e)).const_add z
    have h2 : HasFDerivAt f (fderiv ℂ f (L s z)) (z + ((s : ℂ) - 1) • z i • e) :=
      (hf.differentiableAt (hU.mem_nhds (hLU s hs hz))).hasFDerivAt
    have h3 := (h2.comp_hasDerivAt (s : ℂ) h1).comp_ofReal
    rw [map_smul, smul_eq_mul] at h3
    exact h3
  · exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_const.mul hc)

/- English proof (translation)
The claim follows from `hf.comp (fun t _ => (hasDerivAt_update z i t).differentiableAt.differentiableWithinAt) fun _ ht => update_mem_polydisc hz ht`.
-/
theorem differentiableOn_comp_update_polydisc {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (univ.pi fun j => ball 0 (r j))) (i : ι) {z : ι → ℂ}
    (hz : z ∈ univ.pi fun j => ball (0 : ℂ) (r j)) :
    DifferentiableOn ℂ (fun t => f (update z i t)) (ball 0 (r i)) :=
  hf.comp (fun t _ => (hasDerivAt_update z i t).differentiableAt.differentiableWithinAt)
    fun _ ht => update_mem_polydisc hz ht

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hr : ball (0 : ℂ) (r i) ∈ 𝓝 0` using `ball_mem_nhds _ (pos_of_mem_ball (ha i trivial))`. Establish `key : ∀ m : ℕ, ∃ g : (ι → ℂ) → ℂ, DifferentiableOn ℂ g (univ.pi fun j => ball 0 (r j)) ∧ ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), f z = z i ^ m * g z`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => exact ⟨f, hf, fun z _ => by simp⟩`. Consider the case `succ m ih`. Take `⟨g, hg, hfg⟩` from `ih`. Take `⟨g', hg', hgg'⟩` from `exists_eq_coord_mul_of_vanishing hg i (hcon m g hg hfg)`.

Conclude with `⟨g', hg', fun z hz => by rw [hfg z hz, hgg' z hz, pow_succ, mul_assoc]⟩`. Establish `hA` using `(differentiableOn_comp_update_polydisc hf i ha).analyticAt hr`. Establish `htop : analyticOrderAt (fun t => f (update a i t)) 0 = ⊤`. Use `ENat.eq_top_iff_forall_ge.2 fun m => (natCast_le_analyticOrderAt hA).2 ?_` and prove the remaining obligations. Take `⟨g, hg, hfg⟩` from `key m`.

Use `⟨_, (differentiableOn_comp_update_polydisc hg i ha).analyticAt hr, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hr] with t ht`. Simplify using `[hfg _ (update_mem_polydisc ha ht)]`. Rewrite `htop` using `[analyticOrderAt_eq_top]`. Take `⟨t, ht0, ht1, ht2⟩` from `((eventually_mem_nhdsWithin (a := (0 : ℂ)) (s := {0}ᶜ)).and ((htop.and hr).filter_mono nhdsWithin_le_nhds)).exists`.

Conclude with `h0 t ht2 ht0 ht1`.
-/
theorem exists_eq_coord_pow_mul {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (univ.pi fun j => ball 0 (r j))) (i : ι) {a : ι → ℂ}
    (ha : a ∈ univ.pi fun j => ball (0 : ℂ) (r j))
    (h0 : ∀ t ∈ ball (0 : ℂ) (r i), t ≠ 0 → f (update a i t) ≠ 0) :
    ∃ (m : ℕ) (g : (ι → ℂ) → ℂ), DifferentiableOn ℂ g (univ.pi fun j => ball 0 (r j)) ∧
      (∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), f z = z i ^ m * g z) ∧
      ∃ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), g (update z i 0) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hr : ball (0 : ℂ) (r i) ∈ 𝓝 0 := ball_mem_nhds _ (pos_of_mem_ball (ha i trivial))
  have key : ∀ m : ℕ, ∃ g : (ι → ℂ) → ℂ, DifferentiableOn ℂ g (univ.pi fun j => ball 0 (r j)) ∧
      ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), f z = z i ^ m * g z := by
    intro m
    induction m with
    | zero => exact ⟨f, hf, fun z _ => by simp⟩
    | succ m ih =>
      obtain ⟨g, hg, hfg⟩ := ih
      obtain ⟨g', hg', hgg'⟩ := exists_eq_coord_mul_of_vanishing hg i (hcon m g hg hfg)
      exact ⟨g', hg', fun z hz => by rw [hfg z hz, hgg' z hz, pow_succ, mul_assoc]⟩
  have hA := (differentiableOn_comp_update_polydisc hf i ha).analyticAt hr
  have htop : analyticOrderAt (fun t => f (update a i t)) 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.2 fun m => (natCast_le_analyticOrderAt hA).2 ?_
    obtain ⟨g, hg, hfg⟩ := key m
    refine ⟨_, (differentiableOn_comp_update_polydisc hg i ha).analyticAt hr, ?_⟩
    filter_upwards [hr] with t ht
    simp [hfg _ (update_mem_polydisc ha ht)]
  rw [analyticOrderAt_eq_top] at htop
  obtain ⟨t, ht0, ht1, ht2⟩ := ((eventually_mem_nhdsWithin (a := (0 : ℂ)) (s := {0}ᶜ)).and
    ((htop.and hr).filter_mono nhdsWithin_le_nhds)).exists
  exact h0 t ht2 ht0 ht1

/- English proof (translation)
Establish `hU : IsOpen (univ.pi fun j => ball (0 : ℂ) (r j))` using `isOpen_set_pi finite_univ fun _ _ => isOpen_ball`. Establish `hr : 0 < r i` using `pos_of_mem_ball (ha i trivial)`. Establish `hp : DifferentiableOn ℂ (fun z => g (update z i 0)) (univ.pi fun j => ball 0 (r j))`. Use `hg.comp (Differentiable.differentiableOn (differentiable_pi.2 fun j => ?_)) fun z hz => update_mem_polydisc hz (mem_ball_self hr)` and prove the remaining obligations. Break down `eq_or_ne j i with rfl | hj` into its components or cases.

Simplify using the standard rewrite rules. Simplify `differentiable_apply j` using `[hj]`. Establish `hfr : ∃ᶠ z in 𝓝 a, g (update z i 0) ≠ 0`. Introduce `hev`. Take `⟨z, hz, hz'⟩` from `h1`.

Conclude with `hz' (SCV.eqOn_of_eventuallyEq hU (convex_pi fun j _ => convex_ball (0 : ℂ) (r j)).isPreconnected hp (differentiableOn_const 0) ha (hev.mono fun z hz => not_not.1 hz) hz)`. Establish `hsub : closedBall (0 : ℂ) (r i / 2) ⊆ ball 0 (r i)` using `closedBall_subset_ball (by linarith)`. Establish `hsub' : sphere (0 : ℂ) (r i / 2) ⊆ ball 0 (r i)` using `sphere_subset_closedBall.trans hsub`. Establish `hne : ∀ t ∈ sphere (0 : ℂ) (r i / 2), t ≠ 0` using `fun t ht => ne_of_mem_sphere ht (by linarith)`. Take `⟨t₀, ht₀, hmin⟩` from `(isCompact_sphere (0 : ℂ) (r i / 2)).exists_isMinOn (NormedSpace.sphere_nonempty.2 (by linarith)) ((differentiableOn_comp_update_polydisc hg i ha).continuousOn.mono hsub').norm`.

Establish `hc : 0 < ‖g (update a i t₀)‖` using `norm_pos_iff.2 (h0.self_of_nhds t₀ (hsub' ht₀) (hne t₀ ht₀))`. Use `set c := ‖g (update a i t₀)‖ / 2 with hcdef`. Establish `hc0 : 0 < c` using `by positivity`. Establish `h2 : ∀ᶠ z in 𝓝 a, ∀ t ∈ sphere (0 : ℂ) (r i / 2), c < ‖g (update z i t)‖`. Use `(isCompact_sphere _ _).eventually_forall_of_forall_eventually fun t ht => ?_` and prove the remaining obligations.

Establish `h3 : ContinuousAt (fun p : (ι → ℂ) × ℂ => ‖g (update p.1 i p.2)‖) (a, t)`. Use `ContinuousAt.norm (ContinuousAt.comp (g := g) ?_ (continuous_fst.update i continuous_snd).continuousAt)` and prove the remaining obligations. Conclude with `(hg.differentiableAt (hU.mem_nhds (update_mem_polydisc ha (hsub' ht)))).continuousAt`. Use `h3.eventually (lt_mem_nhds ?_)` and prove the remaining obligations. Conclude with `(half_lt_self hc).trans_le (hmin ht)`.

Establish `h4 : ∃ᶠ z in 𝓝 a, c ≤ ‖g (update z i 0)‖`. Use `(hfr.and_eventually (h0.and (h2.and (hU.mem_nhds ha)))).mono ?_` and prove the remaining obligations. Introduce and unpack `z ⟨hz1, hz2, hz3, hz4⟩`. Establish `h5 : DifferentiableOn ℂ (fun t => (g (update z i t))⁻¹) (ball 0 (r i))`. Use `(differentiableOn_comp_update_polydisc hg i hz4).inv fun t ht => ?_` and prove the remaining obligations.

Break down `eq_or_ne t 0 with rfl | ht0` into its components or cases. Use `exacts [hz1, hz2 t ht ht0]`. Establish `h6 : ‖(g (update z i 0))⁻¹‖ ≤ c⁻¹`. Use `Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball (h5.diffContOnCl_ball hsub) (fun t ht => ?_) (subset_closure (mem_ball_self (by linarith)))` and prove the remaining obligations. Rewrite `ht` using `[frontier_ball _ (by linarith)]`.

Rewrite using `[norm_inv]`. Conclude with `inv_anti₀ hc0 (hz3 t ht).le`. Rewrite `h6` using `[norm_inv, inv_le_inv₀ (norm_pos_iff.2 hz1) hc0]`. Then use the resulting hypothesis. Establish `h7 : c ≤ ‖g (update a i 0)‖` using `ge_of_tendsto_of_frequently (hp.differentiableAt (hU.mem_nhds ha)).continuousAt.norm h4`. Conclude with `norm_pos_iff.1 (hc0.trans_le h7)`.
-/
theorem ne_zero_on_hyperplane_of_eventually_ne_zero {g : (ι → ℂ) → ℂ}
    (hg : DifferentiableOn ℂ g (univ.pi fun j => ball 0 (r j))) (i : ι)
    (h1 : ∃ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), g (update z i 0) ≠ 0) {a : ι → ℂ}
    (ha : a ∈ univ.pi fun j => ball (0 : ℂ) (r j))
    (h0 : ∀ᶠ z in 𝓝 a, ∀ t ∈ ball (0 : ℂ) (r i), t ≠ 0 → g (update z i t) ≠ 0) :
    g (update a i 0) ≠ 0 := by
  have hU : IsOpen (univ.pi fun j => ball (0 : ℂ) (r j)) :=
    isOpen_set_pi finite_univ fun _ _ => isOpen_ball
  have hr : 0 < r i := pos_of_mem_ball (ha i trivial)
  have hp : DifferentiableOn ℂ (fun z => g (update z i 0)) (univ.pi fun j => ball 0 (r j)) := by
    refine hg.comp (Differentiable.differentiableOn (differentiable_pi.2 fun j => ?_))
      fun z hz => update_mem_polydisc hz (mem_ball_self hr)
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simpa [hj] using differentiable_apply j
  have hfr : ∃ᶠ z in 𝓝 a, g (update z i 0) ≠ 0 := by
    intro hev
    obtain ⟨z, hz, hz'⟩ := h1
    exact hz' (SCV.eqOn_of_eventuallyEq hU
      (convex_pi fun j _ => convex_ball (0 : ℂ) (r j)).isPreconnected hp
      (differentiableOn_const 0) ha (hev.mono fun z hz => not_not.1 hz) hz)
  have hsub : closedBall (0 : ℂ) (r i / 2) ⊆ ball 0 (r i) := closedBall_subset_ball (by linarith)
  have hsub' : sphere (0 : ℂ) (r i / 2) ⊆ ball 0 (r i) := sphere_subset_closedBall.trans hsub
  have hne : ∀ t ∈ sphere (0 : ℂ) (r i / 2), t ≠ 0 := fun t ht => ne_of_mem_sphere ht (by linarith)
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_sphere (0 : ℂ) (r i / 2)).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 (by linarith))
    ((differentiableOn_comp_update_polydisc hg i ha).continuousOn.mono hsub').norm
  have hc : 0 < ‖g (update a i t₀)‖ :=
    norm_pos_iff.2 (h0.self_of_nhds t₀ (hsub' ht₀) (hne t₀ ht₀))
  set c := ‖g (update a i t₀)‖ / 2 with hcdef
  have hc0 : 0 < c := by positivity
  have h2 : ∀ᶠ z in 𝓝 a, ∀ t ∈ sphere (0 : ℂ) (r i / 2), c < ‖g (update z i t)‖ := by
    refine (isCompact_sphere _ _).eventually_forall_of_forall_eventually fun t ht => ?_
    have h3 : ContinuousAt (fun p : (ι → ℂ) × ℂ => ‖g (update p.1 i p.2)‖) (a, t) := by
      refine ContinuousAt.norm (ContinuousAt.comp (g := g) ?_
        (continuous_fst.update i continuous_snd).continuousAt)
      exact (hg.differentiableAt (hU.mem_nhds (update_mem_polydisc ha (hsub' ht)))).continuousAt
    refine h3.eventually (lt_mem_nhds ?_)
    exact (half_lt_self hc).trans_le (hmin ht)
  have h4 : ∃ᶠ z in 𝓝 a, c ≤ ‖g (update z i 0)‖ := by
    refine (hfr.and_eventually (h0.and (h2.and (hU.mem_nhds ha)))).mono ?_
    rintro z ⟨hz1, hz2, hz3, hz4⟩
    have h5 : DifferentiableOn ℂ (fun t => (g (update z i t))⁻¹) (ball 0 (r i)) := by
      refine (differentiableOn_comp_update_polydisc hg i hz4).inv fun t ht => ?_
      rcases eq_or_ne t 0 with rfl | ht0
      exacts [hz1, hz2 t ht ht0]
    have h6 : ‖(g (update z i 0))⁻¹‖ ≤ c⁻¹ := by
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        (h5.diffContOnCl_ball hsub) (fun t ht => ?_) (subset_closure (mem_ball_self (by linarith)))
      rw [frontier_ball _ (by linarith)] at ht
      rw [norm_inv]
      exact inv_anti₀ hc0 (hz3 t ht).le
    rwa [norm_inv, inv_le_inv₀ (norm_pos_iff.2 hz1) hc0] at h6
  have h7 : c ≤ ‖g (update a i 0)‖ := ge_of_tendsto_of_frequently
    (hp.differentiableAt (hU.mem_nhds ha)).continuousAt.norm h4
  exact norm_pos_iff.1 (hc0.trans_le h7)

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on generalizing f with`. Consider the case `empty => exact ⟨f, 0, hf, fun z hz => ⟨h0 z hz (by simp), by simp⟩⟩`. Consider the case `insert i S hi ih`. Break down `(univ.pi fun j => ball (0 : ℂ) (r j)).eq_empty_or_nonempty with he | ⟨b, hb⟩` into its components or cases. Conclude with `⟨f, 0, hf, by simp [he]⟩`.

Establish `hr : ∀ j, 0 < r j` using `fun j => pos_of_mem_ball (hb j trivial)`. Establish `hup : ∀ z : ι → ℂ, (∀ j ∈ S, z j ≠ 0) → ∀ t : ℂ, t ≠ 0 → ∀ j ∈ insert i S, update z i t j ≠ 0`. Introduce `z hz t ht j hj`. Break down `eq_or_ne j i with rfl | hji` into its components or cases. Simplify using `using ht`.

Simplify `hz j ((Finset.mem_insert.1 hj).resolve_left hji)` using `[hji]`. Establish `ha : (fun j => ((r j / 2 : ℝ) : ℂ)) ∈ univ.pi fun j => ball (0 : ℂ) (r j)`. Introduce `j _`. Rewrite using `[mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos (hr j)).le]`. Conclude with `half_lt_self (hr j)`.

Take `⟨k, g, hg, hfg, hg1⟩` from `exists_eq_coord_pow_mul hf i ha fun t ht ht0 => h0 _ (update_mem_polydisc ha ht) (hup _ (fun j _ => Complex.ofReal_ne_zero.2 (half_pos (hr j)).ne') t ht0)`. Establish `hg0 : ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), (∀ j ∈ S, z j ≠ 0) → ∀ t ∈ ball (0 : ℂ) (r i), t ≠ 0 → g (update z i t) ≠ 0`. Introduce `z hz hz' t ht ht0`. Use `h0 _ (update_mem_polydisc hz ht) (hup z hz' t ht0)` as an intermediate fact. Rewrite `this` using `[hfg _ (update_mem_polydisc hz ht)]`.

Conclude with `right_ne_zero_of_mul this`. Take `⟨u, m, hu, hu'⟩` from `ih hg fun z hz hz' => by`. Rewrite using `[← update_eq_self i z]`. Break down `eq_or_ne (z i) 0 with hzi | hzi` into its components or cases. Rewrite using `[hzi]`.

Use `ne_zero_on_hyperplane_of_eventually_ne_zero hg i hg1 hz ?_` and prove the remaining obligations. Establish `h2 : ∀ᶠ y in 𝓝 z, ∀ j ∈ S, y j ≠ 0` using `(Filter.eventually_all_finset S).2 fun j hj => (continuous_apply j).continuousAt.eventually_ne (hz' j hj)`. Use `filter_upwards [h2, (isOpen_set_pi finite_univ fun _ _ => isOpen_ball).mem_nhds hz] with y hy1 hy2 using hg0 y hy2 hy1`. Conclude with `hg0 z hz hz' _ (hz i trivial) hzi`. Use `⟨u, update m i k, hu, fun z hz => ⟨(hu' z hz).1, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hfg z hz, (hu' z hz).2, Finset.prod_insert hi, update_self, mul_left_comm]`. Use `congr 2`. Conclude with `Finset.prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]`.
-/
theorem exists_eq_unit_mul_monomial (S : Finset ι) {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (univ.pi fun j => ball 0 (r j)))
    (h0 : ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), (∀ j ∈ S, z j ≠ 0) → f z ≠ 0) :
    ∃ (u : (ι → ℂ) → ℂ) (m : ι → ℕ), DifferentiableOn ℂ u (univ.pi fun j => ball 0 (r j)) ∧
      ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), u z ≠ 0 ∧ f z = u z * ∏ i ∈ S, z i ^ m i := by
  induction S using Finset.induction_on generalizing f with
  | empty => exact ⟨f, 0, hf, fun z hz => ⟨h0 z hz (by simp), by simp⟩⟩
  | insert i S hi ih =>
    rcases (univ.pi fun j => ball (0 : ℂ) (r j)).eq_empty_or_nonempty with he | ⟨b, hb⟩
    · exact ⟨f, 0, hf, by simp [he]⟩
    have hr : ∀ j, 0 < r j := fun j => pos_of_mem_ball (hb j trivial)
    have hup : ∀ z : ι → ℂ, (∀ j ∈ S, z j ≠ 0) → ∀ t : ℂ, t ≠ 0 →
        ∀ j ∈ insert i S, update z i t j ≠ 0 := by
      intro z hz t ht j hj
      rcases eq_or_ne j i with rfl | hji
      · simpa using ht
      · simpa [hji] using hz j ((Finset.mem_insert.1 hj).resolve_left hji)
    have ha : (fun j => ((r j / 2 : ℝ) : ℂ)) ∈ univ.pi fun j => ball (0 : ℂ) (r j) := by
      intro j _
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos (hr j)).le]
      exact half_lt_self (hr j)
    obtain ⟨k, g, hg, hfg, hg1⟩ := exists_eq_coord_pow_mul hf i ha fun t ht ht0 =>
      h0 _ (update_mem_polydisc ha ht)
        (hup _ (fun j _ => Complex.ofReal_ne_zero.2 (half_pos (hr j)).ne') t ht0)
    have hg0 : ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), (∀ j ∈ S, z j ≠ 0) →
        ∀ t ∈ ball (0 : ℂ) (r i), t ≠ 0 → g (update z i t) ≠ 0 := by
      intro z hz hz' t ht ht0
      have := h0 _ (update_mem_polydisc hz ht) (hup z hz' t ht0)
      rw [hfg _ (update_mem_polydisc hz ht)] at this
      exact right_ne_zero_of_mul this
    obtain ⟨u, m, hu, hu'⟩ := ih hg fun z hz hz' => by
      rw [← update_eq_self i z]
      rcases eq_or_ne (z i) 0 with hzi | hzi
      · rw [hzi]
        refine ne_zero_on_hyperplane_of_eventually_ne_zero hg i hg1 hz ?_
        have h2 : ∀ᶠ y in 𝓝 z, ∀ j ∈ S, y j ≠ 0 := (Filter.eventually_all_finset S).2 fun j hj =>
          (continuous_apply j).continuousAt.eventually_ne (hz' j hj)
        filter_upwards [h2, (isOpen_set_pi finite_univ fun _ _ => isOpen_ball).mem_nhds hz]
          with y hy1 hy2 using hg0 y hy2 hy1
      · exact hg0 z hz hz' _ (hz i trivial) hzi
    refine ⟨u, update m i k, hu, fun z hz => ⟨(hu' z hz).1, ?_⟩⟩
    rw [hfg z hz, (hu' z hz).2, Finset.prod_insert hi, update_self, mul_left_comm]
    congr 2
    exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]

end

/- English proof (translation)
Introduce `j hj`. Take `⟨u, m, hu, hu'⟩` from `exists_eq_unit_mul_monomial S' (hv j hj) fun z hz hz' => notMem_coordDivisor.1 (h0 z hz (notMem_coordDivisor.2 hz')) j hj`. Conclude with `⟨u, m, hu.continuousOn, hu'⟩`.
-/
theorem isUnitMulMonomialOn_of_ne_zero {ι κ : Type*} [Fintype ι] {S' : Finset ι} {r : ι → ℝ}
    {S : Finset κ} {v : (ι → ℂ) → κ → ℂ}
    (hv : ∀ j ∈ S, DifferentiableOn ℂ (fun z => v z j) (univ.pi fun i => Metric.ball 0 (r i)))
    (h0 : ∀ z ∈ univ.pi fun i => Metric.ball (0 : ℂ) (r i),
      z ∉ coordDivisor S' id → z ∉ coordDivisor S v) :
    IsUnitMulMonomialOn S v S' id (univ.pi fun i => Metric.ball 0 (r i)) := by
  classical
  intro j hj
  obtain ⟨u, m, hu, hu'⟩ := exists_eq_unit_mul_monomial S' (hv j hj) fun z hz hz' =>
    notMem_coordDivisor.1 (h0 z hz (notMem_coordDivisor.2 hz')) j hj
  exact ⟨u, m, hu.continuousOn, hu'⟩

end GlobalTheory

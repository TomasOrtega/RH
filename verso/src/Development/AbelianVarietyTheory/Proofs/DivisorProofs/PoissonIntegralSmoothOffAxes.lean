import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff Convolution

noncomputable section
namespace GlobalTheory.CirclePoissonParam

open Real

/- English proof (translation)
Use `contDiff_pi.2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Function.update_self]`. Conclude with `(contDiff_circleMap 0 r).comp contDiff_snd`.

Simplify using `only [Function.update_of_ne hj]`. Conclude with `(contDiff_apply ℝ ℂ j).comp contDiff_fst`.
-/
lemma contDiff_update_circleMap {e : ℕ} (i : Fin e) (r : ℝ) :
    ContDiff ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => Function.update q.1 i (circleMap 0 r q.2)) := by
  refine contDiff_pi.2 fun j => ?_
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    exact (contDiff_circleMap 0 r).comp contDiff_snd
  · simp only [Function.update_of_ne hj]
    exact (contDiff_apply ℝ ℂ j).comp contDiff_fst

/- English proof (translation)
Use `set V := {z : Fin e → ℂ | z ∈ Metric.ball c r ∧ ∀ k ∈ S, z k ≠ 0} with hV`. Use `set U := {z : Fin e → ℂ | z ∈ Metric.ball c R ∧ ∀ k ∈ insert i S, z k ≠ 0} with hU`. Establish `hVopen : IsOpen V`. Establish `: V = ball c r ∩ ⋂ k ∈ S, {z | z k ≠ 0}` using `by ext z; simp [V]`. Rewrite using `[this]`.

Use `isOpen_ball.inter (isOpen_biInter_finset fun k _ => ?_)` and prove the remaining obligations. Conclude with `isOpen_ne_fun (continuous_apply k) continuous_const`. Establish `hzi : ∀ z ∈ V, ‖z i‖ < r`. Introduce `z hz`. Establish `h1 : dist (z i) (c i) ≤ dist z c` using `dist_le_pi_dist z c i`.

Establish `h2 : dist z c < r` using `hz.1`. Rewrite `h1` using `[hci, dist_zero_right]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set F : (Fin e → ℂ) × ℝ → ℝ := fun q => poissonKernel 0 (q.1 i) (circleMap 0 r q.2) * f (Function.update q.1 i (circleMap 0 r q.2)) with hF`. Establish `hFsm : ContDiffOn ℝ ∞ F (V ×ˢ univ)`.

Establish `hmaps : MapsTo (fun q : (Fin e → ℂ) × ℝ => Function.update q.1 i (circleMap 0 r q.2)) (V ×ˢ univ) U`. Introduce and unpack `⟨z, θ⟩ ⟨hz, -⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, dist_pi_lt_iff (hr.trans hrR)]`. Introduce `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Function.update_self, hci, dist_zero_right, norm_circleMap_zero, abs_of_pos hr]`. Conclude with `hrR`. Simplify using `only [Function.update_of_ne hj]`.

Conclude with `(dist_le_pi_dist z c j).trans_lt (hz.1.trans hrR)`. Introduce `k hk`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Simplify using `only [Function.update_self]`.

Rewrite using `[← norm_pos_iff, norm_circleMap_zero, abs_of_pos hr]`. Conclude with `hr`. Simplify using `only [Function.update_of_ne hki]`. Conclude with `hz.2 k ((Finset.mem_insert.1 hk).resolve_left hki)`. Establish `h2 : ContDiffOn ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => f (Function.update q.1 i (circleMap 0 r q.2))) (V ×ˢ univ)` using `hf.comp (contDiff_update_circleMap i r).contDiffOn hmaps`.

Establish `h1 : ContDiffOn ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => poissonKernel 0 (q.1 i) (circleMap 0 r q.2)) (V ×ˢ univ)`. Simplify using `only [poissonKernel_def, sub_zero]`. Establish `hζ : ContDiff ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => circleMap 0 r q.2)` using `(contDiff_circleMap 0 r).comp contDiff_snd`. Establish `hw : ContDiff ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => q.1 i)` using `(contDiff_apply ℝ ℂ i).comp contDiff_fst`. Use `ContDiffOn.div ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `((contDiff_norm_sq ℝ).comp hζ |>.sub ((contDiff_norm_sq ℝ).comp hw)).contDiffOn`. Conclude with `((contDiff_norm_sq ℝ).comp (hζ.sub hw)).contDiffOn`. Introduce and unpack `⟨z, θ⟩ ⟨hz, -⟩`. Establish `hne : circleMap 0 r θ - z i ≠ 0`. Introduce `h0`.

Use `hzi z hz` as an intermediate fact. Rewrite `h0` using `[sub_eq_zero]`. Rewrite `this` using `[← h0, norm_circleMap_zero, abs_of_pos hr]`. Conclude with `lt_irrefl _ this`. Conclude with `pow_ne_zero 2 (norm_ne_zero_iff.2 hne)`.

Conclude with `h1.mul h2`. Set `b : ContDiffBump (-π : ℝ)` to `⟨π, 2 * π, Real.pi_pos, by linarith [Real.pi_pos]⟩`. Use `set g : (Fin e → ℂ) → ℝ → ℝ := fun z y => b y * F (z, -y) with hg`. Establish `hgsm : ContDiffOn ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => g q.1 q.2) (V ×ˢ univ)`. Establish `hb : ContDiff ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => b q.2)` using `b.contDiff.comp contDiff_snd`.

Establish `hmap : MapsTo (fun q : (Fin e → ℂ) × ℝ => (q.1, -q.2)) (V ×ˢ univ) (V ×ˢ univ)` using `fun q hq => ⟨hq.1, mem_univ _⟩`. Use `hFsm.comp (contDiff_fst.prodMk contDiff_snd.neg).contDiffOn hmap` as an intermediate fact. Conclude with `hb.contDiffOn.mul this`. Establish `hgs : ∀ p, ∀ x, p ∈ V → x ∉ tsupport b → g p x = 0`. Introduce `p x _ hx`.

Simplify using `only [g, mul_eq_zero]`. Conclude with `Or.inl (image_eq_zero_of_notMem_tsupport hx)`. Establish `hloc : LocallyIntegrable ((Ioc (0:ℝ) (2 * π)).indicator (fun _ => (1:ℝ))) volume` using `(locallyIntegrable_const (1:ℝ)).indicator measurableSet_Ioc`. Establish `hconv` using `contDiffOn_convolution_right_with_param (𝕜 := ℝ) (μ := volume) (n := ⊤) (ContinuousLinearMap.lsmul ℝ ℝ) hVopen b.hasCompactSupport.isCompact hgs hloc hgsm`. Establish `hpair : ContDiff ℝ ∞ (fun z : Fin e → ℂ => (z, (0:ℝ)))` using `contDiff_id.prodMk contDiff_const`.

Establish `hcomp` using `hconv.comp hpair.contDiffOn (fun z hz => ⟨hz, mem_univ _⟩)`. Establish `key : ∀ z ∈ V, ((Ioc (0:ℝ) (2 * π)).indicator (fun _ => (1:ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g z) 0 = ∫ θ in (0:ℝ)..2 * π, F (z, θ)`. Introduce `z _`. Rewrite using `[convolution_def, intervalIntegral.integral_of_le (by positivity), ← integral_indicator measurableSet_Ioc]`. Use `congr 1`.

Use extensionality with `t`. Distinguish the cases in `ht : t ∈ Ioc 0 (2 * π)`. Rewrite using `[indicator_of_mem ht, indicator_of_mem ht]`. Simplify using `only [ContinuousLinearMap.lsmul_apply, one_smul, zero_sub, neg_neg, g]`. Rewrite using `[b.one_of_mem_closedBall, one_mul]`.

Rewrite using `[Metric.mem_closedBall, Real.dist_eq, show b.rIn = π from rfl, abs_le]`. Apply the tactic sequence `constructor <;> linarith [ht.1, ht.2]`. Rewrite using `[indicator_of_notMem ht, indicator_of_notMem ht]`. Simplify using the standard rewrite rules. Use `(hcomp.const_smul (2 * π)⁻¹).congr ?_` and prove the remaining obligations.

Introduce `z hz`. Simplify using `only [Function.comp_apply, Pi.smul_apply]`. Rewrite using `[key z hz]`. Both sides reduce to the same expression.
-/
theorem poissonInt_update_contDiffOn (e : ℕ) (S : Finset (Fin e)) (i : Fin e) (c : Fin e → ℂ)
    (R r : ℝ) (f : (Fin e → ℂ) → ℝ) (hr : 0 < r) (hrR : r < R) (hci : c i = 0)
    (hf : ContDiffOn ℝ ∞ f {z | z ∈ Metric.ball c R ∧ ∀ k ∈ insert i S, z k ≠ 0}) :
    ContDiffOn ℝ ∞ (fun z => ReciprocityTheory.AnForm.A.poissonInt (fun ζ => f (Function.update z i ζ)) r (z i))
      {z | z ∈ Metric.ball c r ∧ ∀ k ∈ S, z k ≠ 0} := by
  set V := {z : Fin e → ℂ | z ∈ Metric.ball c r ∧ ∀ k ∈ S, z k ≠ 0} with hV
  set U := {z : Fin e → ℂ | z ∈ Metric.ball c R ∧ ∀ k ∈ insert i S, z k ≠ 0} with hU
  have hVopen : IsOpen V := by
    have : V = ball c r ∩ ⋂ k ∈ S, {z | z k ≠ 0} := by ext z; simp [V]
    rw [this]
    refine isOpen_ball.inter (isOpen_biInter_finset fun k _ => ?_)
    exact isOpen_ne_fun (continuous_apply k) continuous_const
  have hzi : ∀ z ∈ V, ‖z i‖ < r := by
    intro z hz
    have h1 : dist (z i) (c i) ≤ dist z c := dist_le_pi_dist z c i
    have h2 : dist z c < r := hz.1
    rw [hci, dist_zero_right] at h1
    linarith
  set F : (Fin e → ℂ) × ℝ → ℝ := fun q => poissonKernel 0 (q.1 i) (circleMap 0 r q.2) *
    f (Function.update q.1 i (circleMap 0 r q.2)) with hF
  have hFsm : ContDiffOn ℝ ∞ F (V ×ˢ univ) := by
    have hmaps : MapsTo (fun q : (Fin e → ℂ) × ℝ => Function.update q.1 i (circleMap 0 r q.2))
        (V ×ˢ univ) U := by
      rintro ⟨z, θ⟩ ⟨hz, -⟩
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_pi_lt_iff (hr.trans hrR)]
        intro j
        by_cases hj : j = i
        · subst hj
          simp only [Function.update_self, hci, dist_zero_right, norm_circleMap_zero, abs_of_pos hr]
          exact hrR
        · simp only [Function.update_of_ne hj]
          exact (dist_le_pi_dist z c j).trans_lt (hz.1.trans hrR)
      · intro k hk
        by_cases hki : k = i
        · subst hki
          simp only [Function.update_self]
          rw [← norm_pos_iff, norm_circleMap_zero, abs_of_pos hr]; exact hr
        · simp only [Function.update_of_ne hki]
          exact hz.2 k ((Finset.mem_insert.1 hk).resolve_left hki)
    have h2 : ContDiffOn ℝ ∞
        (fun q : (Fin e → ℂ) × ℝ => f (Function.update q.1 i (circleMap 0 r q.2))) (V ×ˢ univ) :=
      hf.comp (contDiff_update_circleMap i r).contDiffOn hmaps
    have h1 : ContDiffOn ℝ ∞
        (fun q : (Fin e → ℂ) × ℝ => poissonKernel 0 (q.1 i) (circleMap 0 r q.2)) (V ×ˢ univ) := by
      simp only [poissonKernel_def, sub_zero]
      have hζ : ContDiff ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => circleMap 0 r q.2) :=
        (contDiff_circleMap 0 r).comp contDiff_snd
      have hw : ContDiff ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => q.1 i) :=
        (contDiff_apply ℝ ℂ i).comp contDiff_fst
      refine ContDiffOn.div ?_ ?_ ?_
      · exact ((contDiff_norm_sq ℝ).comp hζ |>.sub ((contDiff_norm_sq ℝ).comp hw)).contDiffOn
      · exact ((contDiff_norm_sq ℝ).comp (hζ.sub hw)).contDiffOn
      · rintro ⟨z, θ⟩ ⟨hz, -⟩
        have hne : circleMap 0 r θ - z i ≠ 0 := by
          intro h0
          have := hzi z hz
          rw [sub_eq_zero] at h0
          rw [← h0, norm_circleMap_zero, abs_of_pos hr] at this
          exact lt_irrefl _ this
        exact pow_ne_zero 2 (norm_ne_zero_iff.2 hne)
    exact h1.mul h2
  let b : ContDiffBump (-π : ℝ) := ⟨π, 2 * π, Real.pi_pos, by linarith [Real.pi_pos]⟩
  set g : (Fin e → ℂ) → ℝ → ℝ := fun z y => b y * F (z, -y) with hg
  have hgsm : ContDiffOn ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => g q.1 q.2) (V ×ˢ univ) := by
    have hb : ContDiff ℝ ∞ (fun q : (Fin e → ℂ) × ℝ => b q.2) := b.contDiff.comp contDiff_snd
    have hmap : MapsTo (fun q : (Fin e → ℂ) × ℝ => (q.1, -q.2)) (V ×ˢ univ) (V ×ˢ univ) :=
      fun q hq => ⟨hq.1, mem_univ _⟩
    have := hFsm.comp (contDiff_fst.prodMk contDiff_snd.neg).contDiffOn hmap
    exact hb.contDiffOn.mul this
  have hgs : ∀ p, ∀ x, p ∈ V → x ∉ tsupport b → g p x = 0 := by
    intro p x _ hx
    simp only [g, mul_eq_zero]
    exact Or.inl (image_eq_zero_of_notMem_tsupport hx)
  have hloc : LocallyIntegrable ((Ioc (0:ℝ) (2 * π)).indicator (fun _ => (1:ℝ))) volume :=
    (locallyIntegrable_const (1:ℝ)).indicator measurableSet_Ioc
  have hconv := contDiffOn_convolution_right_with_param (𝕜 := ℝ) (μ := volume) (n := ⊤)
    (ContinuousLinearMap.lsmul ℝ ℝ) hVopen b.hasCompactSupport.isCompact hgs hloc hgsm
  have hpair : ContDiff ℝ ∞ (fun z : Fin e → ℂ => (z, (0:ℝ))) := contDiff_id.prodMk contDiff_const
  have hcomp := hconv.comp hpair.contDiffOn (fun z hz => ⟨hz, mem_univ _⟩)
  have key : ∀ z ∈ V, ((Ioc (0:ℝ) (2 * π)).indicator (fun _ => (1:ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g z) 0
      = ∫ θ in (0:ℝ)..2 * π, F (z, θ) := by
    intro z _
    rw [convolution_def, intervalIntegral.integral_of_le (by positivity),
      ← integral_indicator measurableSet_Ioc]
    congr 1; ext t
    by_cases ht : t ∈ Ioc 0 (2 * π)
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      simp only [ContinuousLinearMap.lsmul_apply, one_smul, zero_sub, neg_neg, g]
      rw [b.one_of_mem_closedBall, one_mul]
      rw [Metric.mem_closedBall, Real.dist_eq, show b.rIn = π from rfl, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]; simp
  refine (hcomp.const_smul (2 * π)⁻¹).congr ?_
  intro z hz
  simp only [Function.comp_apply, Pi.smul_apply]
  rw [key z hz]
  rfl

end GlobalTheory.CirclePoissonParam

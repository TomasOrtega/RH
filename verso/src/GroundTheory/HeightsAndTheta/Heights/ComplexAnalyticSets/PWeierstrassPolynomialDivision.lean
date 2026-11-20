import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeierstrassPolynomialDivision
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParametricCircleIntegralAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MonicDifferenceQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

namespace WeierstrassPolynomialDivision

/- English proof (translation)
Proceed by induction on `u using Finset.induction_on with`. Consider the case `empty => simp [circleIntegral]`. Consider the case `insert a u ha ih`. Simplify using `only [Finset.sum_insert ha]`. Rewrite using `[circleIntegral.integral_add ((hf a (by simp)).circleIntegrable hR) ((continuousOn_finsetSum u fun i hi => hf i (by simp [hi])).circleIntegrable hR), ih fun i hi => hf i (by simp [hi])]`.
-/
theorem circleIntegral_finset_sum {ι : Type} (u : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ i ∈ u, ContinuousOn (f i) (sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ u, f i z) = ∑ i ∈ u, ∮ z in C(c, R), f i z := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a u ha ih =>
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add ((hf a (by simp)).circleIntegrable hR)
      ((continuousOn_finsetSum u fun i hi => hf i (by simp [hi])).circleIntegrable hR),
      ih fun i hi => hf i (by simp [hi])]

/- English proof (translation)
Use function extensionality and compare the values at `o`. Apply the tactic sequence `cases o <;> rfl`.
-/
theorem pointWithLast_eta {σ : Type} (x : Option σ → ℂ) : pointWithLast (fun i => x (some i)) (x none) = x := by
  funext o
  cases o <;> rfl

/- English proof (translation)
Rewrite using `[differentiable_pi]`. Introduce `o`. Consider the cases of `o with`. Consider the case `none => exact differentiable_snd`. Consider the case `some i => show Differentiable ℂ fun p : (σ → ℂ) × ℂ => p.1 i fun_prop`.
-/
theorem differentiable_pointWithLast {σ : Type} [Fintype σ] :
    Differentiable ℂ (fun p : (σ → ℂ) × ℂ => pointWithLast p.1 p.2) := by
  rw [differentiable_pi]
  intro o
  cases o with
  | none => exact differentiable_snd
  | some i =>
    show Differentiable ℂ fun p : (σ → ℂ) × ℂ => p.1 i
    fun_prop

/- English proof (translation)
Rewrite using `[pi_norm_lt_iff hε]`. Introduce `o`. Consider the cases of `o with`. Consider the case `none => exact hs`. Consider the case `some i => exact (norm_le_pi_norm z i).trans_lt hz`.
-/
theorem norm_pointWithLast_lt {σ : Type} [Fintype σ] {z : σ → ℂ} {s : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : ‖z‖ < ε)
    (hs : ‖s‖ < ε) : ‖pointWithLast z s‖ < ε := by
  rw [pi_norm_lt_iff hε]
  intro o
  cases o with
  | none => exact hs
  | some i => exact (norm_le_pi_norm z i).trans_lt hz

end WeierstrassPolynomialDivision

open WeierstrassPolynomialDivision in

/- English proof (translation)
Introduce `σ _ d c g hc hc0 hg`. Take `⟨εg, hεg, hgan⟩` from `hg.exists_ball_analyticOnNhd`. Take `⟨εc, hεc, hcan⟩` from `Metric.eventually_nhds_iff_ball.1 (Filter.eventually_all.2 fun j => (hc j).eventually_analyticAt)`. Use `set ε := min εg εc with hε_def`. Establish `hε : 0 < ε` using `lt_min hεg hεc`.

Use `set r := ε / 2 with hr_def`. Establish `hr : 0 < r` using `half_pos hε`. Establish `hrε : r < ε` using `half_lt_self hε`. Set `G : (σ → ℂ) × ℂ → ℂ` to `fun p => g (pointWithLast p.1 p.2)`. Set `F : (σ → ℂ) × ℂ → ℂ` to `fun p => weierstrassPolynomial c (pointWithLast p.1 p.2)`.

Set `A : Set ((σ → ℂ) × ℂ)` to `ball 0 ε ×ˢ ball 0 ε`. Establish `hcd : ∀ z ∈ ball (0 : σ → ℂ) ε, ∀ j, DifferentiableAt ℂ (c j) z` using `fun z hz j => (hcan z (mem_ball_zero_iff.2 ((mem_ball_zero_iff.1 hz).trans_le (min_le_right _ _))) j).differentiableAt`. Establish `hGd : ∀ p ∈ A, DifferentiableAt ℂ G p`. Introduce `p hp`. Establish `hp' : pointWithLast p.1 p.2 ∈ ball (0 : Option σ → ℂ) εg` using `mem_ball_zero_iff.2 (norm_pointWithLast_lt hεg ((mem_ball_zero_iff.1 hp.1).trans_le (min_le_left _ _)) ((mem_ball_zero_iff.1 hp.2).trans_le (min_le_left _ _)))`.

Conclude with `(hgan _ hp').differentiableAt.comp p (differentiable_pointWithLast p)`. Establish `hFd : ∀ p ∈ A, DifferentiableAt ℂ F p`. Introduce `p hp`. Use `show DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ d + ∑ j : Fin d, c j p.1 * p.2 ^ (j : ℕ)) p`. Conclude with `(differentiableAt_snd.pow d).add (DifferentiableAt.fun_sum fun j _ => ((hcd p.1 hp.1 j).comp p differentiableAt_fst).mul (differentiableAt_snd.pow _))`.

Establish `hFne : ∀ᶠ z in 𝓝 (0 : σ → ℂ), ∀ s ∈ sphere (0 : ℂ) r, F (z, s) ≠ 0`. Use `(isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun s hs => ?_` and prove the remaining obligations. Establish `hsn : ‖s‖ = r` using `mem_sphere_zero_iff_norm.1 hs`. Establish `hA : ((0 : σ → ℂ), s) ∈ A` using `⟨mem_ball_self hε, mem_ball_zero_iff.2 (hsn ▸ hrε)⟩`. Establish `h0 : F (0, s) ≠ 0` using `by show weierstrassPolynomial c (pointWithLast 0 s) ≠ 0`.

Rewrite using `[weierstrassPolynomial_pointWithLast_zero c hc0]`. Conclude with `pow_ne_zero _ (norm_ne_zero_iff.1 (hsn ▸ hr.ne'))`. Conclude with `(hFd _ hA).continuousAt.eventually_ne h0`. Take `⟨δ, hδ, hδF⟩` from `Metric.eventually_nhds_iff_ball.1 (hFne.and (ball_mem_nhds (0 : σ → ℂ) hε))`. Set `O₀ : Set ((σ → ℂ) × ℂ)` to `A ∩ F ⁻¹' {0}ᶜ`.

Establish `hO₀ : IsOpen O₀` using `ContinuousOn.isOpen_inter_preimage (fun p hp => (hFd p hp).continuousAt.continuousWithinAt) (isOpen_ball.prod isOpen_ball) isOpen_compl_singleton`. Establish `hmem₀ : ∀ z ∈ ball (0 : σ → ℂ) δ, ∀ s ∈ sphere (0 : ℂ) r, (z, s) ∈ O₀` using `fun z hz s hs => ⟨⟨(hδF z hz).2, mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hs).trans_lt hrε)⟩, (hδF z hz).1 s hs⟩`. Set `μ : (Option σ → ℂ) × ℂ → (σ → ℂ) × ℂ` to `fun p => ((fun i => p.1 (some i)), p.2)`. Establish `hμ : Differentiable ℂ μ` using `(differentiable_pi.2 fun i => by fun_prop).prodMk differentiable_snd`. Set `Φq : (Option σ → ℂ) × ℂ → ℂ` to `fun p => G (μ p) / (F (μ p) * (p.2 - p.1 none))`.

Set `Oq : Set ((Option σ → ℂ) × ℂ)` to `μ ⁻¹' O₀ ∩ {p | p.2 - p.1 none ≠ 0}`. Establish `hOq : IsOpen Oq` using `(hO₀.preimage hμ.continuous).inter (isOpen_ne_fun (by fun_prop) continuous_const)`. Set `Uq : Set (Option σ → ℂ)` to `(fun x : Option σ → ℂ => fun i => x (some i)) ⁻¹' ball (0 : σ → ℂ) δ ∩ (fun x : Option σ → ℂ => x none) ⁻¹' ball (0 : ℂ) r`. Establish `hUq : IsOpen Uq` using `(isOpen_ball.preimage (by fun_prop)).inter (isOpen_ball.preimage (continuous_apply none))`. Establish `hΦq : DifferentiableOn ℂ Φq Oq`.

Introduce and unpack `p ⟨⟨hA, hF⟩, hne⟩`. Establish `hden : DifferentiableAt ℂ (fun p : (Option σ → ℂ) × ℂ => F (μ p) * (p.2 - p.1 none)) p` using `((hFd _ hA).comp p (hμ p)).mul (differentiableAt_snd.sub (by fun_prop : DifferentiableAt ℂ (fun p : (Option σ → ℂ) × ℂ => p.1 none) p))`. Rewrite using `[show Φq = fun p => G (μ p) * (F (μ p) * (p.2 - p.1 none))⁻¹ from funext fun _ => div_eq_mul_inv _ _]`. Conclude with `(((hGd _ hA).comp p (hμ p)).mul (hden.inv (mul_ne_zero hF hne))).differentiableWithinAt`. Establish `hmemq : ∀ x ∈ Uq, ∀ s ∈ sphere (0 : ℂ) r, (x, s) ∈ Oq`.

Introduce `x hx s hs`. Use `⟨hmem₀ _ hx.1 s hs, ?_⟩` and prove the remaining obligations. Use `show s - x none ≠ 0`. Introduce `h`. Establish `h1` using `mem_sphere_zero_iff_norm.1 hs`.

Establish `h2` using `mem_ball_zero_iff.1 hx.2`. Rewrite `h1` using `[sub_eq_zero.1 h]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0q : (0 : Option σ → ℂ) ∈ Uq` using `⟨mem_ball_self hδ, mem_ball_self hr⟩`. Establish `hqan` using `hC (Option σ) Φq Oq Uq 0 r hr.le hOq hUq hΦq hmemq`.

Set `Φa : Fin d → (σ → ℂ) × ℂ → ℂ` to `fun j p => G p * monicDifferenceCoeff (fun k => c k p.1) p.2 j / F p`. Establish `hΦa : ∀ j, DifferentiableOn ℂ (Φa j) O₀`. Introduce `j p hp`. Establish `hP : DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => monicDifferenceCoeff (fun k => c k p.1) p.2 j) p` using `by show DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ (d - 1 - (j : ℕ)) + ∑ k ∈ Finset.univ.filter (fun k : Fin d => (j : ℕ) < k), c k p.1 * p.2 ^ ((k : ℕ) - 1 - j)) p`. Conclude with `(differentiableAt_snd.pow _).add (DifferentiableAt.fun_sum fun k _ => ((hcd p.1 hp.1.1 k).comp p differentiableAt_fst).mul (differentiableAt_snd.pow _))`.

Rewrite using `[show Φa j = fun p => G p * monicDifferenceCoeff (fun k => c k p.1) p.2 j * (F p)⁻¹ from`. Use function extensionality and compare the values at `fun _ => div_eq_mul_inv _ _]`. Conclude with `(((hGd p hp.1).mul hP).mul ((hFd p hp.1).inv hp.2)).differentiableWithinAt`. Establish `haan` using `fun j => hC σ (Φa j) O₀ (ball 0 δ) 0 r hr.le hO₀ isOpen_ball (hΦa j) hmem₀`. Use `⟨fun x => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φq (x, s), fun j z => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φa j (z, s), analyticAt_const.mul (hqan 0 h0q), fun j => analyticAt_const.mul (haan j 0 (mem_ball_self hδ)), ?_⟩` and prove the remaining obligations.

Use `filter_upwards [hUq.mem_nhds h0q] with x hx`. Use `set z : σ → ℂ := fun i => x (some i) with hz`. Use `set t : ℂ := x none with ht`. Establish `hgx : g x = G (z, t)` using `congrArg g (pointWithLast_eta x).symm`. Establish `hcau : (2 * π * I)⁻¹ • (∮ s in C(0, r), (s - t)⁻¹ • G (z, s)) = G (z, t)`.

Use `DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (f := fun s => G (z, s)) ?_ hx.2` and prove the remaining obligations. Use `DifferentiableOn.diffContOnCl_ball (U := ball 0 ε) (fun s hs => ?_) (closedBall_subset_ball hrε)` and prove the remaining obligations. Conclude with `((hGd (z, s) ⟨(hδF z hx.1).2, hs⟩).comp s ((differentiableAt_const z).prodMk differentiableAt_id)).differentiableWithinAt`. Establish `hpt : Set.EqOn (fun s => (s - t)⁻¹ • G (z, s)) (fun s => weierstrassPolynomial c x * Φq (x, s) + ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)) (sphere (0 : ℂ) r)`. Introduce `s hs`.

Establish `hFs : F (z, s) ≠ 0` using `(hδF z hx.1).1 s hs`. Establish `hst : s - t ≠ 0` using `(hmemq x hx s hs).2`. Establish `key : F (z, s) - weierstrassPolynomial c x = (s - t) * ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ)` using `monic_sub_eq_mul_sum (fun k => c k z) s t`. Establish `hsum : ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s) = G (z, s) / F (z, s) * ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ)`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show t ^ (j : ℕ) * (G (z, s) * monicDifferenceCoeff (fun k => c k z) s j / F (z, s)) = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hP : ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) = (F (z, s) - weierstrassPolynomial c x) / (s - t)`. Rewrite using `[key]`.

Clear the denominators using the available nonvanishing facts. Use `show (s - t)⁻¹ • G (z, s) = weierstrassPolynomial c x * (G (z, s) / (F (z, s) * (s - t))) + ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)`. Rewrite using `[hsum, hP, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hcq : ContinuousOn (fun s => Φq (x, s)) (sphere (0 : ℂ) r)` using `hΦq.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hmemq x hx s hs`. Establish `hca : ∀ j ∈ (Finset.univ : Finset (Fin d)), ContinuousOn (fun s => t ^ (j : ℕ) * Φa j (z, s)) (sphere (0 : ℂ) r)` using `fun j _ => continuousOn_const.mul ((hΦa j).continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hmem₀ z hx.1 s hs)`. Establish `hint : (∮ s in C(0, r), (s - t)⁻¹ • G (z, s)) = weierstrassPolynomial c x * (∮ s in C(0, r), Φq (x, s)) + ∑ j : Fin d, t ^ (j : ℕ) * ∮ s in C(0, r), Φa j (z, s)`. Establish `hi1 : CircleIntegrable (fun s => weierstrassPolynomial c x * Φq (x, s)) 0 r` using `(continuousOn_const.mul hcq).circleIntegrable hr.le`. Establish `hi2 : CircleIntegrable (fun s => ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)) 0 r` using `(continuousOn_finsetSum _ hca).circleIntegrable hr.le`.

Rewrite using `[circleIntegral.integral_congr hr.le hpt, circleIntegral.integral_add hi1 hi2, circleIntegral.integral_const_mul, circleIntegral_finset_sum _ _ hr.le hca]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => circleIntegral.integral_const_mul _ _ _ _`. Rewrite using `[hgx, ← hcau, smul_eq_mul, hint, mul_add, Finset.mul_sum]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem WeierstrassPolynomialDivision.proof (hC : ParametricCircleIntegralAnalytic.Statement) :
    WeierstrassPolynomialDivision.Statement := by
  intro σ _ d c g hc hc0 hg
  obtain ⟨εg, hεg, hgan⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨εc, hεc, hcan⟩ := Metric.eventually_nhds_iff_ball.1
    (Filter.eventually_all.2 fun j => (hc j).eventually_analyticAt)
  set ε := min εg εc with hε_def
  have hε : 0 < ε := lt_min hεg hεc
  set r := ε / 2 with hr_def
  have hr : 0 < r := half_pos hε
  have hrε : r < ε := half_lt_self hε

  let G : (σ → ℂ) × ℂ → ℂ := fun p => g (pointWithLast p.1 p.2)
  let F : (σ → ℂ) × ℂ → ℂ := fun p => weierstrassPolynomial c (pointWithLast p.1 p.2)
  let A : Set ((σ → ℂ) × ℂ) := ball 0 ε ×ˢ ball 0 ε
  have hcd : ∀ z ∈ ball (0 : σ → ℂ) ε, ∀ j, DifferentiableAt ℂ (c j) z := fun z hz j =>
    (hcan z (mem_ball_zero_iff.2 ((mem_ball_zero_iff.1 hz).trans_le (min_le_right _ _))) j).differentiableAt
  have hGd : ∀ p ∈ A, DifferentiableAt ℂ G p := by
    intro p hp
    have hp' : pointWithLast p.1 p.2 ∈ ball (0 : Option σ → ℂ) εg := mem_ball_zero_iff.2
      (norm_pointWithLast_lt hεg ((mem_ball_zero_iff.1 hp.1).trans_le (min_le_left _ _))
        ((mem_ball_zero_iff.1 hp.2).trans_le (min_le_left _ _)))
    exact (hgan _ hp').differentiableAt.comp p (differentiable_pointWithLast p)
  have hFd : ∀ p ∈ A, DifferentiableAt ℂ F p := by
    intro p hp
    show DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ d + ∑ j : Fin d, c j p.1 * p.2 ^ (j : ℕ)) p
    exact (differentiableAt_snd.pow d).add (DifferentiableAt.fun_sum fun j _ =>
      ((hcd p.1 hp.1 j).comp p differentiableAt_fst).mul (differentiableAt_snd.pow _))

  have hFne : ∀ᶠ z in 𝓝 (0 : σ → ℂ), ∀ s ∈ sphere (0 : ℂ) r, F (z, s) ≠ 0 := by
    refine (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun s hs => ?_
    have hsn : ‖s‖ = r := mem_sphere_zero_iff_norm.1 hs
    have hA : ((0 : σ → ℂ), s) ∈ A := ⟨mem_ball_self hε, mem_ball_zero_iff.2 (hsn ▸ hrε)⟩
    have h0 : F (0, s) ≠ 0 := by
      show weierstrassPolynomial c (pointWithLast 0 s) ≠ 0
      rw [weierstrassPolynomial_pointWithLast_zero c hc0]
      exact pow_ne_zero _ (norm_ne_zero_iff.1 (hsn ▸ hr.ne'))
    exact (hFd _ hA).continuousAt.eventually_ne h0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff_ball.1 (hFne.and (ball_mem_nhds (0 : σ → ℂ) hε))

  let O₀ : Set ((σ → ℂ) × ℂ) := A ∩ F ⁻¹' {0}ᶜ
  have hO₀ : IsOpen O₀ := ContinuousOn.isOpen_inter_preimage
    (fun p hp => (hFd p hp).continuousAt.continuousWithinAt) (isOpen_ball.prod isOpen_ball) isOpen_compl_singleton
  have hmem₀ : ∀ z ∈ ball (0 : σ → ℂ) δ, ∀ s ∈ sphere (0 : ℂ) r, (z, s) ∈ O₀ := fun z hz s hs =>
    ⟨⟨(hδF z hz).2, mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hs).trans_lt hrε)⟩, (hδF z hz).1 s hs⟩

  let μ : (Option σ → ℂ) × ℂ → (σ → ℂ) × ℂ := fun p => ((fun i => p.1 (some i)), p.2)
  have hμ : Differentiable ℂ μ :=
    (differentiable_pi.2 fun i => by fun_prop).prodMk differentiable_snd
  let Φq : (Option σ → ℂ) × ℂ → ℂ := fun p => G (μ p) / (F (μ p) * (p.2 - p.1 none))
  let Oq : Set ((Option σ → ℂ) × ℂ) := μ ⁻¹' O₀ ∩ {p | p.2 - p.1 none ≠ 0}
  have hOq : IsOpen Oq := (hO₀.preimage hμ.continuous).inter (isOpen_ne_fun (by fun_prop) continuous_const)
  let Uq : Set (Option σ → ℂ) :=
    (fun x : Option σ → ℂ => fun i => x (some i)) ⁻¹' ball (0 : σ → ℂ) δ ∩ (fun x : Option σ → ℂ => x none) ⁻¹' ball (0 : ℂ) r
  have hUq : IsOpen Uq :=
    (isOpen_ball.preimage (by fun_prop)).inter (isOpen_ball.preimage (continuous_apply none))
  have hΦq : DifferentiableOn ℂ Φq Oq := by
    rintro p ⟨⟨hA, hF⟩, hne⟩
    have hden : DifferentiableAt ℂ (fun p : (Option σ → ℂ) × ℂ => F (μ p) * (p.2 - p.1 none)) p :=
      ((hFd _ hA).comp p (hμ p)).mul (differentiableAt_snd.sub
        (by fun_prop : DifferentiableAt ℂ (fun p : (Option σ → ℂ) × ℂ => p.1 none) p))
    rw [show Φq = fun p => G (μ p) * (F (μ p) * (p.2 - p.1 none))⁻¹ from funext fun _ => div_eq_mul_inv _ _]
    exact (((hGd _ hA).comp p (hμ p)).mul (hden.inv (mul_ne_zero hF hne))).differentiableWithinAt
  have hmemq : ∀ x ∈ Uq, ∀ s ∈ sphere (0 : ℂ) r, (x, s) ∈ Oq := by
    intro x hx s hs
    refine ⟨hmem₀ _ hx.1 s hs, ?_⟩
    show s - x none ≠ 0
    intro h
    have h1 := mem_sphere_zero_iff_norm.1 hs
    have h2 := mem_ball_zero_iff.1 hx.2
    rw [sub_eq_zero.1 h] at h1
    linarith
  have h0q : (0 : Option σ → ℂ) ∈ Uq := ⟨mem_ball_self hδ, mem_ball_self hr⟩
  have hqan := hC (Option σ) Φq Oq Uq 0 r hr.le hOq hUq hΦq hmemq

  let Φa : Fin d → (σ → ℂ) × ℂ → ℂ := fun j p => G p * monicDifferenceCoeff (fun k => c k p.1) p.2 j / F p
  have hΦa : ∀ j, DifferentiableOn ℂ (Φa j) O₀ := by
    intro j p hp
    have hP : DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => monicDifferenceCoeff (fun k => c k p.1) p.2 j) p := by
      show DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ (d - 1 - (j : ℕ)) +
        ∑ k ∈ Finset.univ.filter (fun k : Fin d => (j : ℕ) < k), c k p.1 * p.2 ^ ((k : ℕ) - 1 - j)) p
      exact (differentiableAt_snd.pow _).add (DifferentiableAt.fun_sum fun k _ =>
        ((hcd p.1 hp.1.1 k).comp p differentiableAt_fst).mul (differentiableAt_snd.pow _))
    rw [show Φa j = fun p => G p * monicDifferenceCoeff (fun k => c k p.1) p.2 j * (F p)⁻¹ from
      funext fun _ => div_eq_mul_inv _ _]
    exact (((hGd p hp.1).mul hP).mul ((hFd p hp.1).inv hp.2)).differentiableWithinAt
  have haan := fun j => hC σ (Φa j) O₀ (ball 0 δ) 0 r hr.le hO₀ isOpen_ball (hΦa j) hmem₀
  refine ⟨fun x => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φq (x, s),
    fun j z => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φa j (z, s),
    analyticAt_const.mul (hqan 0 h0q), fun j => analyticAt_const.mul (haan j 0 (mem_ball_self hδ)), ?_⟩
  filter_upwards [hUq.mem_nhds h0q] with x hx
  set z : σ → ℂ := fun i => x (some i) with hz
  set t : ℂ := x none with ht
  have hgx : g x = G (z, t) := congrArg g (pointWithLast_eta x).symm

  have hcau : (2 * π * I)⁻¹ • (∮ s in C(0, r), (s - t)⁻¹ • G (z, s)) = G (z, t) := by
    refine DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (f := fun s => G (z, s)) ?_ hx.2
    refine DifferentiableOn.diffContOnCl_ball (U := ball 0 ε) (fun s hs => ?_) (closedBall_subset_ball hrε)
    exact ((hGd (z, s) ⟨(hδF z hx.1).2, hs⟩).comp s
      ((differentiableAt_const z).prodMk differentiableAt_id)).differentiableWithinAt

  have hpt : Set.EqOn (fun s => (s - t)⁻¹ • G (z, s))
      (fun s => weierstrassPolynomial c x * Φq (x, s) + ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s))
      (sphere (0 : ℂ) r) := by
    intro s hs
    have hFs : F (z, s) ≠ 0 := (hδF z hx.1).1 s hs
    have hst : s - t ≠ 0 := (hmemq x hx s hs).2
    have key : F (z, s) - weierstrassPolynomial c x =
        (s - t) * ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) :=
      monic_sub_eq_mul_sum (fun k => c k z) s t
    have hsum : ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s) =
        G (z, s) / F (z, s) * ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show t ^ (j : ℕ) * (G (z, s) * monicDifferenceCoeff (fun k => c k z) s j / F (z, s)) = _
      ring
    have hP : ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) =
        (F (z, s) - weierstrassPolynomial c x) / (s - t) := by
      rw [key]
      field_simp
    show (s - t)⁻¹ • G (z, s) =
      weierstrassPolynomial c x * (G (z, s) / (F (z, s) * (s - t))) + ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)
    rw [hsum, hP, smul_eq_mul]
    field_simp
    ring
  have hcq : ContinuousOn (fun s => Φq (x, s)) (sphere (0 : ℂ) r) :=
    hΦq.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hmemq x hx s hs
  have hca : ∀ j ∈ (Finset.univ : Finset (Fin d)), ContinuousOn (fun s => t ^ (j : ℕ) * Φa j (z, s))
      (sphere (0 : ℂ) r) := fun j _ => continuousOn_const.mul
    ((hΦa j).continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hmem₀ z hx.1 s hs)
  have hint : (∮ s in C(0, r), (s - t)⁻¹ • G (z, s)) =
      weierstrassPolynomial c x * (∮ s in C(0, r), Φq (x, s)) +
        ∑ j : Fin d, t ^ (j : ℕ) * ∮ s in C(0, r), Φa j (z, s) := by
    have hi1 : CircleIntegrable (fun s => weierstrassPolynomial c x * Φq (x, s)) 0 r :=
      (continuousOn_const.mul hcq).circleIntegrable hr.le
    have hi2 : CircleIntegrable (fun s => ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)) 0 r :=
      (continuousOn_finsetSum _ hca).circleIntegrable hr.le
    rw [circleIntegral.integral_congr hr.le hpt, circleIntegral.integral_add hi1 hi2,
      circleIntegral.integral_const_mul, circleIntegral_finset_sum _ _ hr.le hca]
    congr 1
    exact Finset.sum_congr rfl fun j _ => circleIntegral.integral_const_mul _ _ _ _
  rw [hgx, ← hcau, smul_eq_mul, hint, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => by ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

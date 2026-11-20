import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraRegularity
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic

namespace GroundTheory.Automorphic

open Sobolev Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

/- English proof (translation)
Set `_` to `h.chartedSpace`. Use `set b := Module.finBasis ℝ 𝔤`. Use `set d := Module.finrank ℝ 𝔤`. Establish `hfc : ∀ f : h.smoothFuns (F` using `ℂ), ∀ g : G, Continuous fun y : G => (f : G → ℂ) (g * y) := fun f g => (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous.comp (continuous_const.mul continuous_id)`. Establish `hexpc : Continuous fun x : EuclideanSpace ℝ (Fin d) => h.expG (coordEquiv b x)` using `h.continuous_expG.comp (coordEquiv b).continuous`.

Take `⟨ε, hε, hdens⟩` from `h.exists_smooth_density_expCoord μ b`. Establish `hV : {x : EuclideanSpace ℝ (Fin d) | h.expG (coordEquiv b x) ∈ U} ∈ 𝓝 0`. Use `hexpc.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Simplify using `using hU`. Take `⟨ρ₀, hρ₀, hρ₀V⟩` from `Metric.mem_nhds_iff.1 hV`.

Break down `Nat.eq_zero_or_pos d with hd | hd` into its components or cases. Establish `hsub : ∀ x y : EuclideanSpace ℝ (Fin d), x = y`. Introduce `x y; ext i; exact absurd i.2 (by omega)`. Take `⟨κ, hκs, hκc, hκU, hκ⟩` from `hdens (fun _ => 1) contDiff_const (fun x _ => by`. Rewrite using `[hsub x 0]`.

Conclude with `Metric.mem_closedBall_self hε.le)`. Use `⟨κ, hκs, hκc, hκU.trans ?_, fun f _ g => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `hρ₀V (by rw [hsub x 0]; exact Metric.mem_ball_self hρ₀)`. Use `hκ _ (hfc f g)` as an intermediate fact.

Repeatedly rewrite using `[mul_comm ((f : G → ℂ) _)]`. Rewrite using `[this, integral_euclideanSpace_of_eq_zero hd]`. Simplify using the standard rewrite rules. Use `set Q := P ^ (d + 1)`. Establish `hQ : Q.Monic` using `hP.pow _`.

Establish `hQd : Q.natDegree = (d + 1) * P.natDegree` using `hP.natDegree_pow _`. Take `⟨δ, hδ, A, a, hA, ha, hell, hop⟩` from `h.exists_elliptic_aeval_laplacian bL b Q hQ`. Use `set ρ := min (min δ ε) ρ₀`. Establish `hρ : 0 < ρ` using `lt_min (lt_min hδ hε) hρ₀`. Establish `hρδ : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 δ` using `Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))`.

Establish `hρε : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.closedBall 0 ε` using `Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_right _ _)))`. Establish `hρV : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 ρ₀` using `Metric.ball_subset_ball (min_le_right _ _)`. Establish `hm1 : 1 ≤ 2 * Q.natDegree` using `by rw [hQd]; nlinarith`. Establish `hnm : d < 2 * (2 * Q.natDegree)` using `by rw [hQd]; nlinarith`. Take `⟨E, β, -, -, hEs, -, hβs, -, hβU, hid⟩` from `exists_parametrix hd hm1 hnm Metric.isOpen_ball hA (fun α hα => (ha α hα).contDiffOn Metric.isOpen_ball.uniqueDiffOn) hell Metric.isOpen_ball (Metric.mem_ball_self hρ) hρδ`.

Take `⟨κ, hκs, hκc, hκU, hκ⟩` from `hdens β hβs (hβU.trans hρε)`. Use `⟨κ, hκs, hκc, hκU.trans ?_, fun f hf g => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hρ₀V (hρV (hβU hx))`. Establish `hQf : Polynomial.aeval (h.laplacian bL) Q f = 0`.

Rewrite using `[show Q = P ^ d * P from pow_succ P d, map_mul, Module.End.mul_apply, hf, map_zero]`. Use `set ψ := fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))`. Establish `hψ : ContDiff ℝ ∞ ψ` using `h.contDiff_comp_coordEquiv f.2 g b`. Establish `h1` using `hid ψ hψ.contDiffOn`. Establish `h0 : ∫ x, E x * diffOp A a ψ x = 0`.

Rewrite using `[← integral_zero (EuclideanSpace ℝ (Fin d)) ℂ]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ`. Rewrite using `[hop f g x hx, hQf]`.

Simplify using the standard rewrite rules. Rewrite using `[image_eq_zero_of_notMem_tsupport fun hE => hx (hρδ (hEs hE)), zero_mul]`. Rewrite `h1` using `[h0, eq_comm, sub_eq_zero]`. Establish `hψ0 : ψ 0 = (f : G → ℂ) g` using `by simp [ψ]`. Rewrite using `[← hψ0, h1]`.

Repeatedly rewrite using `[mul_comm ((f : G → ℂ) _)]`. Rewrite using `[hκ _ (hfc f g)]`.
-/
theorem exists_kernel_eq_conv_of_aeval_laplacian [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {ι : Type*} [Fintype ι]
    (bL : Module.Basis ι ℝ h.lieSubalgebra) (P : Polynomial ℂ) (hP : P.Monic) (hPd : 0 < P.natDegree)
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ U ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (h.laplacian bL) P f = 0 →
        ∀ g : G, (f : G → ℂ) g = ∫ y, (f : G → ℂ) (g * y) * κ y ∂μ := by
  let _ := h.chartedSpace
  set b := Module.finBasis ℝ 𝔤
  set d := Module.finrank ℝ 𝔤
  have hfc : ∀ f : h.smoothFuns (F := ℂ), ∀ g : G, Continuous fun y : G => (f : G → ℂ) (g * y) :=
    fun f g => (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous.comp
      (continuous_const.mul continuous_id)
  have hexpc : Continuous fun x : EuclideanSpace ℝ (Fin d) => h.expG (coordEquiv b x) :=
    h.continuous_expG.comp (coordEquiv b).continuous
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_expCoord μ b
  have hV : {x : EuclideanSpace ℝ (Fin d) | h.expG (coordEquiv b x) ∈ U} ∈ 𝓝 0 := by
    refine hexpc.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨ρ₀, hρ₀, hρ₀V⟩ := Metric.mem_nhds_iff.1 hV
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·
    have hsub : ∀ x y : EuclideanSpace ℝ (Fin d), x = y := by
      intro x y; ext i; exact absurd i.2 (by omega)
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens (fun _ => 1) contDiff_const (fun x _ => by
      rw [hsub x 0]; exact Metric.mem_closedBall_self hε.le)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun f _ g => ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact hρ₀V (by rw [hsub x 0]; exact Metric.mem_ball_self hρ₀)
    · have := hκ _ (hfc f g)
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [this, integral_euclideanSpace_of_eq_zero hd]
      simp
  ·
    set Q := P ^ (d + 1)
    have hQ : Q.Monic := hP.pow _
    have hQd : Q.natDegree = (d + 1) * P.natDegree := hP.natDegree_pow _
    obtain ⟨δ, hδ, A, a, hA, ha, hell, hop⟩ := h.exists_elliptic_aeval_laplacian bL b Q hQ
    set ρ := min (min δ ε) ρ₀
    have hρ : 0 < ρ := lt_min (lt_min hδ hε) hρ₀
    have hρδ : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 δ :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
    have hρε : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.closedBall 0 ε :=
      Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_right _ _)))
    have hρV : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 ρ₀ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hm1 : 1 ≤ 2 * Q.natDegree := by rw [hQd]; nlinarith
    have hnm : d < 2 * (2 * Q.natDegree) := by rw [hQd]; nlinarith
    obtain ⟨E, β, -, -, hEs, -, hβs, -, hβU, hid⟩ := exists_parametrix hd hm1 hnm Metric.isOpen_ball
      hA (fun α hα => (ha α hα).contDiffOn Metric.isOpen_ball.uniqueDiffOn) hell Metric.isOpen_ball
      (Metric.mem_ball_self hρ) hρδ
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens β hβs (hβU.trans hρε)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun f hf g => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hρ₀V (hρV (hβU hx))
    · have hQf : Polynomial.aeval (h.laplacian bL) Q f = 0 := by
        rw [show Q = P ^ d * P from pow_succ P d, map_mul, Module.End.mul_apply, hf, map_zero]
      set ψ := fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))
      have hψ : ContDiff ℝ ∞ ψ := h.contDiff_comp_coordEquiv f.2 g b
      have h1 := hid ψ hψ.contDiffOn
      have h0 : ∫ x, E x * diffOp A a ψ x = 0 := by
        rw [← integral_zero (EuclideanSpace ℝ (Fin d)) ℂ]
        congr 1
        funext x
        by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ
        · rw [hop f g x hx, hQf]; simp
        · rw [image_eq_zero_of_notMem_tsupport fun hE => hx (hρδ (hEs hE)), zero_mul]
      rw [h0, eq_comm, sub_eq_zero] at h1
      have hψ0 : ψ 0 = (f : G → ℂ) g := by simp [ψ]
      rw [← hψ0, h1]
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [hκ _ (hfc f g)]

noncomputable def convDeriv (X : 𝔤) (κ : G → ℂ) (y : G) : ℂ :=
  h.rightDeriv X (fun z => κ z⁻¹) y⁻¹

variable {h}

/- English proof (translation)
Set `_` to `h.chartedSpace`. Conclude with `ContMDiff.continuous hf`.
-/
theorem continuous_of_isSmoothFun {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  let _ := h.chartedSpace
  exact ContMDiff.continuous hf

/- English proof (translation)
Set `_` to `h.chartedSpace`. Use `h.lieGroup ∞` as an intermediate fact. Conclude with `hκ.comp (contMDiff_inv 𝓘(ℝ, 𝔤) ∞)`.
-/
theorem isSmoothFun_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) :
    h.IsSmoothFun (fun z : G => κ z⁻¹) := by
  let _ := h.chartedSpace
  have := h.lieGroup ∞
  exact hκ.comp (contMDiff_inv 𝓘(ℝ, 𝔤) ∞)

/- English proof (translation)
The claim follows from `continuous_of_isSmoothFun (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)`.
-/
theorem continuous_rightDeriv_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (X : 𝔤) :
    Continuous (h.rightDeriv X fun z : G => κ z⁻¹) :=
  continuous_of_isSmoothFun (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)

/- English proof (translation)
The claim follows from `(continuous_rightDeriv_comp_inv hκ X).comp continuous_inv`.
-/
theorem continuous_convDeriv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (X : 𝔤) :
    Continuous (h.convDeriv X κ) :=
  (continuous_rightDeriv_comp_inv hκ X).comp continuous_inv

/- English proof (translation)
Establish `hc : Continuous fun Y : 𝔤 => g * h.expG Y` using `continuous_const.mul h.continuous_expG`. Establish `h0 : (fun Y : 𝔤 => f (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => (0 : ℂ)`. Establish `: Tendsto (fun Y : 𝔤 => g * h.expG Y) (𝓝 0) (𝓝 g)`. Simplify using `using hc.tendsto (0 : 𝔤)`. Conclude with `this.eventually hf`.

Simplify using `only [rightDeriv, h0.fderiv_eq, fderiv_const_apply]`. Both sides reduce to the same expression.
-/
theorem rightDeriv_eq_zero_of_eventually {f : G → ℂ} {g : G} (hf : ∀ᶠ z in 𝓝 g, f z = 0)
    (X : 𝔤) : h.rightDeriv X f g = 0 := by
  have hc : Continuous fun Y : 𝔤 => g * h.expG Y := continuous_const.mul h.continuous_expG
  have h0 : (fun Y : 𝔤 => f (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have : Tendsto (fun Y : 𝔤 => g * h.expG Y) (𝓝 0) (𝓝 g) := by
      simpa using hc.tendsto (0 : 𝔤)
    exact this.eventually hf
  simp only [rightDeriv, h0.fderiv_eq, fderiv_const_apply]
  rfl

/- English proof (translation)
Use `rightDeriv_eq_zero_of_eventually ?_ X` and prove the remaining obligations. Establish `hopen : IsOpen (tsupport κ)ᶜ` using `(isClosed_tsupport κ).isOpen_compl`. Establish `ht : Tendsto (fun w : G => w⁻¹) (𝓝 z) (𝓝 z⁻¹)` using `continuous_inv.tendsto z`. Conclude with `(ht.eventually (hopen.mem_nhds hz)).mono fun w hw => (image_eq_zero_of_notMem_tsupport hw : κ w⁻¹ = 0)`.
-/
theorem rightDeriv_comp_inv_eq_zero {κ : G → ℂ} {z : G} (hz : z⁻¹ ∉ tsupport κ) (X : 𝔤) :
    h.rightDeriv X (fun w : G => κ w⁻¹) z = 0 := by
  refine rightDeriv_eq_zero_of_eventually ?_ X
  have hopen : IsOpen (tsupport κ)ᶜ := (isClosed_tsupport κ).isOpen_compl
  have ht : Tendsto (fun w : G => w⁻¹) (𝓝 z) (𝓝 z⁻¹) := continuous_inv.tendsto z
  exact (ht.eventually (hopen.mem_nhds hz)).mono fun w hw =>
    (image_eq_zero_of_notMem_tsupport hw : κ w⁻¹ = 0)

/- English proof (translation)
Introduce `y hy`. Assume the negation of the conclusion as `hyκ`. Conclude with `hy (rightDeriv_comp_inv_eq_zero (by rwa [inv_inv]) X)`.
-/
theorem support_convDeriv_subset (X : 𝔤) (κ : G → ℂ) :
    Function.support (h.convDeriv X κ) ⊆ tsupport κ := by
  intro y hy
  by_contra hyκ
  exact hy (rightDeriv_comp_inv_eq_zero (by rwa [inv_inv]) X)

/- English proof (translation)
The claim follows from `hκc.mono' (support_convDeriv_subset X κ)`.
-/
theorem hasCompactSupport_convDeriv {κ : G → ℂ} (hκc : HasCompactSupport κ) (X : 𝔤) :
    HasCompactSupport (h.convDeriv X κ) :=
  hκc.mono' (support_convDeriv_subset X κ)

/- English proof (translation)
Establish `hDcs : HasCompactSupport (h.rightDeriv X fun w : G => κ w⁻¹)`. Use `HasCompactSupport.intro (hκc.image continuous_inv) fun z hz => ?_` and prove the remaining obligations. Use `rightDeriv_comp_inv_eq_zero (fun hk => hz ⟨z⁻¹, hk, inv_inv z⟩) X` and prove the remaining obligations. Conclude with `hDcs.exists_bound_of_continuous (continuous_rightDeriv_comp_inv hκ X)`.
-/
theorem exists_bound_rightDeriv_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ)
    (X : 𝔤) : ∃ M, ∀ z, ‖h.rightDeriv X (fun w : G => κ w⁻¹) z‖ ≤ M := by
  have hDcs : HasCompactSupport (h.rightDeriv X fun w : G => κ w⁻¹) := by
    refine HasCompactSupport.intro (hκc.image continuous_inv) fun z hz => ?_
    refine rightDeriv_comp_inv_eq_zero (fun hk => hz ⟨z⁻¹, hk, inv_inv z⟩) X
  exact hDcs.exists_bound_of_continuous (continuous_rightDeriv_comp_inv hκ X)

/- English proof (translation)
Establish `hec : Continuous fun t : ℝ => h.expG (t • X)` using `h.continuous_expG.comp (continuous_id.smul continuous_const)`. Establish `hfc : Continuous f` using `continuous_of_isSmoothFun hf`. Establish `hfg : Continuous fun y : G => f (g * y)` using `hfc.comp (continuous_const.mul continuous_id)`. Establish `hκ'c : Continuous fun z : G => κ z⁻¹` using `continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)`. Establish `hDc` using `continuous_rightDeriv_comp_inv hκ X`.

Establish `hshift : ∀ t : ℝ, f (g * h.expG (t • X)) = ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ`. Introduce `t`. Rewrite using `[hconv (g * h.expG (t • X))]`. Use `integral_mul_left_eq_self (μ := μ) (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))` as an intermediate fact. Rewrite using `[← this]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_inv]`. Establish `hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹) (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t`. Introduce `y t`.

Establish `h1` using `h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))`. Establish `h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹) (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t)`. Rewrite using `[sub_self]`. Conclude with `h1`. Use `(h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)` and prove the remaining obligations.

Simplify using `only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]`. Use `set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) '' (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef`. Establish `hS : IsCompact S` using `((isCompact_closedBall 0 1).prod hκc).image ((hec.comp continuous_fst).mul continuous_snd)`. Establish `hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S → h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0`. Introduce `y t ht hy`.

Use `rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X` and prove the remaining obligations. Simplify `hk` using `[mul_inv_rev]`. Simplify using the standard rewrite rules. Take `⟨M, hM⟩` from `exists_bound_rightDeriv_comp_inv hκ hκc X`. Establish `hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ`.

Use `IntegrableOn.integrable_indicator ?_ hS.measurableSet` and prove the remaining obligations. Conclude with `(hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS`. Establish `hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ`. Establish `: (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y`. Use function extensionality and compare the values at `y`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ)) (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (F' := fun (t : ℝ) (y : G) => f (g * y) * h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1) (bound …`. Distinguish the cases in `hy : y ∈ S`.

Rewrite using `[indicator_of_mem hy, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)`. Rewrite using `[indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero, norm_zero])`. Use `hbound`. Use the proof step `(Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))`.

Establish `hd1 : HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f g) 0` using `h.hasDerivAt_rightDeriv hf X g`. Establish `hd2` using `key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)`. Rewrite using `[hd1.unique hd2]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Simplify using `[convDeriv]`.
-/
theorem rightDeriv_eq_integral_convDeriv [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ)
    {f : G → ℂ} (hf : h.IsSmoothFun f) (hconv : ∀ g, f g = ∫ y, f (g * y) * κ y ∂μ)
    (X : 𝔤) (g : G) :
    h.rightDeriv X f g = ∫ y, f (g * y) * h.convDeriv X κ y ∂μ := by
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hfc : Continuous f := continuous_of_isSmoothFun hf
  have hfg : Continuous fun y : G => f (g * y) := hfc.comp (continuous_const.mul continuous_id)
  have hκ'c : Continuous fun z : G => κ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)
  have hDc := continuous_rightDeriv_comp_inv hκ X

  have hshift : ∀ t : ℝ, f (g * h.expG (t • X)) =
      ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ := by
    intro t
    rw [hconv (g * h.expG (t • X))]
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_inv]

  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]

  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hκc).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hκ hκc X
  have hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ := by
    have : (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y := by
      funext y; simp
    rw [this]
    exact Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ))
      (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹)
    (F' := fun (t : ℝ) (y : G) => f (g * y) *
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => ‖f (g * y)‖ * M)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t =>
      (hfg.mul (hκ'c.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable) hint0
    (hfg.mul (hDc.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero,
          norm_zero])
    hbound
    (Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))
  have hd1 : HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f g) 0 :=
    h.hasDerivAt_rightDeriv hf X g
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  congr 1
  funext y
  simp [convDeriv]

end IsExpLieAlgebra

end GroundTheory.Automorphic

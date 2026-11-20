import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ContDiffCompCoordEquiv
import GroundTheory.AutomorphicForms.DixmierMalliavinHaarDensity

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open MeasureTheory Metric Set Filter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

/- English proof (translation)
Establish `hPz : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (b i : 𝔸)) z` using `h.val_prodExp _ z`. Establish `hN : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne` using `hPz ▸ hz`. Establish `hL` using `h.symm_mem_lie hN`. Rewrite `hL` using `[hPz]`. Establish `e1 : ((b.equivFun.symm (prodExpCoord b z) : 𝔤) : 𝔸) = (expPartialHomeomorph ℝ 𝔸).symm (prodExpVal (fun i => (b i : 𝔸)) z)`.

Simplify using `only [prodExpCoord, logCoord, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.symm_apply_apply]`. Conclude with `subspaceProj_of_mem hL`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[coe_expG, e1, h.exp_symm hz, hPz]`.
-/
theorem prodExp_eq_expG_prodExpCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {z : Fin d → ℝ}
    (hz : prodExpVal (fun i => (b i : 𝔸)) z ∈ h.nhdOne) :
    h.prodExp (⇑b) z = h.expG (b.equivFun.symm (prodExpCoord b z)) := by
  have hPz : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (b i : 𝔸)) z :=
    h.val_prodExp _ z
  have hN : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne := hPz ▸ hz
  have hL := h.symm_mem_lie hN
  rw [hPz] at hL
  have e1 : ((b.equivFun.symm (prodExpCoord b z) : 𝔤) : 𝔸) =
      (expPartialHomeomorph ℝ 𝔸).symm (prodExpVal (fun i => (b i : 𝔸)) z) := by
    simp only [prodExpCoord, logCoord, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.symm_apply_apply]
    exact subspaceProj_of_mem hL
  apply Subtype.ext; apply Units.ext
  rw [coe_expG, e1, h.exp_symm hz, hPz]

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/- English proof (translation)
Take `⟨r, ρ, c, W, hr, hρ, hρpos, hW, hPW, hcP, hc, hint⟩` from `h.exists_haar_density_prodExp μ b`. Use `set P := h.prodExp (⇑b) with hPdef`. Establish `hPc : Continuous P` using `h.continuous_prodExp _`. Use `⟨r / 2, by positivity, fun K hK hKs => ?_⟩` and prove the remaining obligations. Establish `hεr : closedBall (0 : Fin d → ℝ) (r / 2) ⊆ ball 0 r` using `closedBall_subset_ball (by linarith)`.

Use `set C := P '' closedBall (0 : Fin d → ℝ) (r / 2) with hCdef`. Establish `hCc : IsCompact C` using `(isCompact_closedBall _ _).image hPc`. Set `κ : G → ℂ` to `W.indicator fun y => K (c y) * (((ρ (c y))⁻¹ : ℝ) : ℂ)`. Establish `hκC : ∀ y, y ∉ C → κ y = 0`. Introduce `y hy`.

Distinguish the cases in `hyW : y ∈ W`. Establish `hz : c y ∉ closedBall (0 : Fin d → ℝ) (r / 2)` using `fun hz => hy ⟨c y, hz, hcP y hyW⟩`. Establish `: K (c y) = 0` using `image_eq_zero_of_notMem_tsupport fun h' => hz (hKs h')`. Simplify using `[κ, indicator_of_mem hyW, this]`. Simplify using `[κ, indicator_of_notMem hyW]`.

Establish `hκsupp : tsupport κ ⊆ C` using `closure_minimal (fun y hy => by_contra fun h' => hy (hκC y h')) hCc.isClosed`. Establish `hKc : IsCompact (tsupport K)` using `(isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hKs`. Establish `hκsupp' : tsupport κ ⊆ P '' tsupport K`. Use `closure_minimal (fun y hy => ?_) (hKc.image hPc).isClosed` and prove the remaining obligations. Distinguish the cases in `hyW : y ∈ W`.

Establish `hK0 : K (c y) ≠ 0`. Introduce `h0`. Apply `hy` to reduce the goal to its premises. Simplify using `[κ, indicator_of_mem hyW, h0]`. Conclude with `⟨c y, subset_tsupport _ hK0, hcP y hyW⟩`.

Conclude with `absurd (by simp [κ, indicator_of_notMem hyW]) hy`. Establish `hκW : ∀ z ∈ ball (0 : Fin d → ℝ) r, κ (P z) * (ρ z : ℂ) = K z`. Introduce `z hz`. Take `⟨hzW, hcz⟩` from `hPW z hz`. Establish `hρz : (ρ z : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (hρpos z hz).ne'`.

Simplify using `only [κ, indicator_of_mem hzW, hcz, Complex.ofReal_inv]`. Clear the denominators using the available nonvanishing facts. Establish `hsmooth : (letI` using `h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) := by`. Introduce `g`. Rewrite using `[h.contMDiffAt_iff_expG]`.

Establish `hcont : Continuous (fun Y : 𝔤 => g * h.expG Y)` using `continuous_const.mul h.continuous_expG`. Establish `hg0 : g * h.expG 0 = g` using `by rw [h.expG_zero, mul_one]`. Distinguish the cases in `hg : g ∈ C`. Take `⟨z₀, hz₀, rfl⟩` from `hg`. Establish `hz₀r : z₀ ∈ ball (0 : Fin d → ℝ) r` using `hεr hz₀`.

Take `⟨hgW, hcg⟩` from `hPW z₀ hz₀r`. Establish `hev : (fun Y : 𝔤 => κ (P z₀ * h.expG Y)) =ᶠ[𝓝 0] fun Y => K (c (P z₀ * h.expG Y)) * (((ρ (c (P z₀ * h.expG Y)))⁻¹ : ℝ) : ℂ)`. Establish `: ∀ᶠ Y in 𝓝 (0 : 𝔤), P z₀ * h.expG Y ∈ W`. Use `hcont.continuousAt (x := 0)` as an intermediate fact. Rewrite `this` using `[ContinuousAt, hg0]`.

Conclude with `this (hW.mem_nhds hgW)`. Use `filter_upwards [this] with Y hY`. Simplify using `[κ, indicator_of_mem hY]`. Use `ContDiffAt.congr_of_eventuallyEq ?_ hev` and prove the remaining obligations. Establish `hc0` using `hc (P z₀) hgW`.

Establish `hρ0 : ρ (c (P z₀ * h.expG 0)) ≠ 0`. Rewrite using `[hg0, hcg]`. Conclude with `(hρpos z₀ hz₀r).ne'`. Conclude with `(hK.contDiffAt.comp _ hc0).mul ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ ((hρ.contDiffAt.comp _ hc0).inv hρ0))`. Establish `hev : (fun Y : 𝔤 => κ (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => 0`.

Establish `: ∀ᶠ Y in 𝓝 (0 : 𝔤), g * h.expG Y ∈ Cᶜ`. Use `hcont.continuousAt (x := 0)` as an intermediate fact. Rewrite `this` using `[ContinuousAt, hg0]`. Conclude with `this (hCc.isClosed.isOpen_compl.mem_nhds hg)`. Use `filter_upwards [this] with Y hY`.

Conclude with `hκC _ hY`. Conclude with `contDiffAt_const.congr_of_eventuallyEq hev`. Establish `hκc : Continuous κ`. Set `` to `h.chartedSpace`. Conclude with `hsmooth.continuous`.

Use `⟨κ, hsmooth, HasCompactSupport.intro hCc hκC, hκsupp', fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `hψ₀s : tsupport (fun y => κ y * φ y) ⊆ P '' ball 0 r` using `(tsupport_mul_subset_left).trans (hκsupp.trans (image_mono hεr))`. Rewrite using `[hint (fun y => κ y * φ y) (hκc.mul hφ) ((HasCompactSupport.intro hCc hκC).mul_right) hψ₀s]`. Rewrite using `[← setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun t => K t * φ (P t)) (s := ball (0 : Fin d → ℝ) r) fun z hz => by`. Establish `: K z = 0` using `image_eq_zero_of_notMem_tsupport fun h' => hz (hεr (hKs h'))`.

Simplify using `[this]]`. Use `setIntegral_congr_fun measurableSet_ball fun z hz => ?_` and prove the remaining obligations. Rewrite using `[mul_right_comm, hκW z hz]`.
-/
theorem exists_smooth_density_prodExp_tsupport {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ K : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ K → tsupport K ⊆ closedBall 0 ε →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧ tsupport κ ⊆ h.prodExp (⇑b) '' tsupport K ∧
        ∀ φ : G → ℂ, Continuous φ → ∫ y, κ y * φ y ∂μ = ∫ t, K t * φ (h.prodExp (⇑b) t) := by
  obtain ⟨r, ρ, c, W, hr, hρ, hρpos, hW, hPW, hcP, hc, hint⟩ := h.exists_haar_density_prodExp μ b
  set P := h.prodExp (⇑b) with hPdef
  have hPc : Continuous P := h.continuous_prodExp _
  refine ⟨r / 2, by positivity, fun K hK hKs => ?_⟩
  have hεr : closedBall (0 : Fin d → ℝ) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (by linarith)
  set C := P '' closedBall (0 : Fin d → ℝ) (r / 2) with hCdef
  have hCc : IsCompact C := (isCompact_closedBall _ _).image hPc
  let κ : G → ℂ := W.indicator fun y => K (c y) * (((ρ (c y))⁻¹ : ℝ) : ℂ)
  have hκC : ∀ y, y ∉ C → κ y = 0 := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hz : c y ∉ closedBall (0 : Fin d → ℝ) (r / 2) := fun hz => hy ⟨c y, hz, hcP y hyW⟩
      have : K (c y) = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hKs h')
      simp [κ, indicator_of_mem hyW, this]
    · simp [κ, indicator_of_notMem hyW]
  have hκsupp : tsupport κ ⊆ C :=
    closure_minimal (fun y hy => by_contra fun h' => hy (hκC y h')) hCc.isClosed
  have hKc : IsCompact (tsupport K) :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hKs
  have hκsupp' : tsupport κ ⊆ P '' tsupport K := by
    refine closure_minimal (fun y hy => ?_) (hKc.image hPc).isClosed
    by_cases hyW : y ∈ W
    · have hK0 : K (c y) ≠ 0 := by
        intro h0; apply hy; simp [κ, indicator_of_mem hyW, h0]
      exact ⟨c y, subset_tsupport _ hK0, hcP y hyW⟩
    · exact absurd (by simp [κ, indicator_of_notMem hyW]) hy
  have hκW : ∀ z ∈ ball (0 : Fin d → ℝ) r, κ (P z) * (ρ z : ℂ) = K z := by
    intro z hz
    obtain ⟨hzW, hcz⟩ := hPW z hz
    have hρz : (ρ z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hρpos z hz).ne'
    simp only [κ, indicator_of_mem hzW, hcz, Complex.ofReal_inv]
    field_simp
  have hsmooth : (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) := by
    intro g
    rw [h.contMDiffAt_iff_expG]
    have hcont : Continuous (fun Y : 𝔤 => g * h.expG Y) :=
      continuous_const.mul h.continuous_expG
    have hg0 : g * h.expG 0 = g := by rw [h.expG_zero, mul_one]
    by_cases hg : g ∈ C
    · obtain ⟨z₀, hz₀, rfl⟩ := hg
      have hz₀r : z₀ ∈ ball (0 : Fin d → ℝ) r := hεr hz₀
      obtain ⟨hgW, hcg⟩ := hPW z₀ hz₀r
      have hev : (fun Y : 𝔤 => κ (P z₀ * h.expG Y)) =ᶠ[𝓝 0]
          fun Y => K (c (P z₀ * h.expG Y)) * (((ρ (c (P z₀ * h.expG Y)))⁻¹ : ℝ) : ℂ) := by
        have : ∀ᶠ Y in 𝓝 (0 : 𝔤), P z₀ * h.expG Y ∈ W := by
          have := hcont.continuousAt (x := 0)
          rw [ContinuousAt, hg0] at this
          exact this (hW.mem_nhds hgW)
        filter_upwards [this] with Y hY
        simp [κ, indicator_of_mem hY]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hc0 := hc (P z₀) hgW
      have hρ0 : ρ (c (P z₀ * h.expG 0)) ≠ 0 := by
        rw [hg0, hcg]; exact (hρpos z₀ hz₀r).ne'
      exact (hK.contDiffAt.comp _ hc0).mul
        ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ ((hρ.contDiffAt.comp _ hc0).inv hρ0))
    · have hev : (fun Y : 𝔤 => κ (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => 0 := by
        have : ∀ᶠ Y in 𝓝 (0 : 𝔤), g * h.expG Y ∈ Cᶜ := by
          have := hcont.continuousAt (x := 0)
          rw [ContinuousAt, hg0] at this
          exact this (hCc.isClosed.isOpen_compl.mem_nhds hg)
        filter_upwards [this] with Y hY
        exact hκC _ hY
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hκc : Continuous κ := by
    let := h.chartedSpace
    exact hsmooth.continuous
  refine ⟨κ, hsmooth, HasCompactSupport.intro hCc hκC, hκsupp', fun φ hφ => ?_⟩
  have hψ₀s : tsupport (fun y => κ y * φ y) ⊆ P '' ball 0 r :=
    (tsupport_mul_subset_left).trans (hκsupp.trans (image_mono hεr))
  rw [hint (fun y => κ y * φ y) (hκc.mul hφ)
    ((HasCompactSupport.intro hCc hκC).mul_right) hψ₀s]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun t => K t * φ (P t))
    (s := ball (0 : Fin d → ℝ) r) fun z hz => by
      have : K z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hεr (hKs h'))
      simp [this]]
  refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [mul_right_comm, hκW z hz]

/- English proof (translation)
Take `⟨ε₁, hε₁, hdens⟩` from `h.exists_smooth_density_prodExp_tsupport μ b`. Take `⟨S, T, ψ, hSo, hTo, h0S, hΦST, hψTS, hψΦ, hΦψ, hψs, hSN⟩` from `h.exists_prodExp_coord b`. Use `set Φ := prodExpCoord b with hΦdef`. Use `set P := h.prodExp (⇑b) with hPdef`. Establish `hΦ0 : Φ 0 = 0` using `prodExpCoord_zero b`.

Establish `h0T : (0 : Fin d → ℝ) ∈ T` using `hΦ0 ▸ hΦST h0S`. Establish `hψ0 : ψ 0 = 0` using `by have := hψΦ 0 h0S; rwa [hΦ0] at this`. Establish `hSU : S ⊆ {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target}` using `fun t ht => h.nhdOne_subset_target (hSN t ht)`. Establish `hΦs : ContDiffOn ℝ ∞ Φ S` using `(contDiffOn_prodExpCoord b).mono hSU`. Establish `hΦat : ∀ t ∈ S, ContDiffAt ℝ ∞ Φ t` using `fun t ht => hΦs.contDiffAt (hSo.mem_nhds ht)`.

Establish `hψat : ∀ w ∈ T, ContDiffAt ℝ ∞ ψ w` using `fun w hw => hψs.contDiffAt (hTo.mem_nhds hw)`. Establish `hPΦ : ∀ t ∈ S, P t = h.expG (b.equivFun.symm (Φ t))` using `fun t ht => h.prodExp_eq_expG_prodExpCoord b (hSN t ht)`. Establish `hdet : ∀ t ∈ S, (fderiv ℝ Φ t).det ≠ 0`. Introduce `t ht`. Establish `hΦt : HasFDerivAt Φ (fderiv ℝ Φ t) t` using `((hΦat t ht).differentiableAt (by simp)).hasFDerivAt`.

Establish `hψt : HasFDerivAt ψ (fderiv ℝ ψ (Φ t)) (Φ t)` using `((hψat _ (hΦST ht)).differentiableAt (by simp)).hasFDerivAt`. Establish `hcomp` using `hψt.comp t hΦt`. Establish `hid : (ψ ∘ Φ) =ᶠ[𝓝 t] id` using `by filter_upwards [hSo.mem_nhds ht] with s hs`. Conclude with `hψΦ s hs`. Establish `e : (fderiv ℝ ψ (Φ t)).comp (fderiv ℝ Φ t) = ContinuousLinearMap.id ℝ (Fin d → ℝ)`.

Rewrite using `[← hcomp.fderiv, hid.fderiv_eq, fderiv_id]`. Introduce `h0`. Use `congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L.det) e` as an intermediate fact. Simplify using `only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id] at this`. Establish `h2 : LinearMap.det ((fderiv ℝ ψ (Φ t) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) ∘ₗ (fderiv ℝ Φ t : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) = 1` using `this`.

Rewrite `h2` using `[LinearMap.det_comp]`. Use `replace this := h2`. Rewrite `this` using `[show LinearMap.det (fderiv ℝ Φ t : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = 0 from h0, mul_zero]`. Conclude with `zero_ne_one this`. Establish `hψc : ContinuousAt ψ 0` using `(hψat 0 h0T).continuousAt`.

Take `⟨δ, hδ, hδT⟩` from `Metric.isOpen_iff.1 hTo 0 h0T`. Take `⟨η, hη, hηψ⟩` from `Metric.continuousAt_iff.1 hψc ε₁ hε₁`. Use `⟨min (δ / 2) (η / 2), lt_min (by positivity) (by positivity), fun β hβ hβs => ?_⟩` and prove the remaining obligations. Use `set ε := min (δ / 2) (η / 2) with hεdef`. Establish `hεδ : ε < δ` using `lt_of_le_of_lt (min_le_left _ _) (by linarith)`.

Establish `hεη : ε < η` using `lt_of_le_of_lt (min_le_right _ _) (by linarith)`. Use `set e : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := fun w => WithLp.toLp 2 w with he`. Use `set β' : (Fin d → ℝ) → ℂ := fun w => β (e w) with hβ'`. Establish `he_cont : Continuous e` using `PiLp.continuous_toLp 2 _`. Establish `hβ'c : ContDiff ℝ ∞ β'` using `hβ.comp PiLp.contDiff_toLp`.

Establish `hnorm : ∀ w : Fin d → ℝ, ‖w‖ ≤ ‖e w‖` using `fun w => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by`. Simplify `PiLp.norm_apply_le (e w) i` using `[e]`. Establish `hβ's : tsupport β' ⊆ closedBall 0 ε`. Use `closure_minimal (fun w hw => ?_) isClosed_closedBall` and prove the remaining obligations. Establish `: e w ∈ closedBall 0 ε` using `hβs (subset_tsupport _ hw)`.

Rewrite `this`, the goal using `[mem_closedBall_zero_iff]`. Conclude with `(hnorm w).trans this`. Establish `hβ'T : tsupport β' ⊆ T` using `fun w hw => hδT (by`. Use `hβ's hw` as an intermediate fact. Rewrite `this` using `[mem_closedBall_zero_iff]`.

Rewrite using `[mem_ball_zero_iff]`. Use the proof step `linarith)`. Establish `hβ'comp : IsCompact (tsupport β')` using `(isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hβ's`. Establish `hβ'e : ∀ w ∈ tsupport β', e w ∈ tsupport β`. Introduce `w hw`.

Establish `: tsupport β' ⊆ e ⁻¹' tsupport β` using `closure_minimal (fun v hv => subset_tsupport _ hv) ((isClosed_tsupport β).preimage he_cont)`. Conclude with `this hw`. Use `set C' := ψ '' tsupport β' with hC'def`. Establish `hC'c : IsCompact C'` using `hβ'comp.image_of_continuousOn (hψs.continuousOn.mono hβ'T)`. Establish `hC'S : C' ⊆ S` using `by rintro _ ⟨w, hw, rfl⟩; exact hψTS (hβ'T hw)`.

Establish `hC'ε : C' ⊆ closedBall 0 ε₁`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Establish `hw'` using `hβ's hw`. Rewrite `hw'` using `[mem_closedBall_zero_iff]`. Use `hηψ (x := w) (by rw [dist_zero_right]; linarith)` as an intermediate fact.

Rewrite `this` using `[hψ0, dist_zero_right]`. Rewrite using `[mem_closedBall_zero_iff]`. Conclude with `this.le`. Set `K : (Fin d → ℝ) → ℂ` to `fun t => if t ∈ S then ((|(fderiv ℝ Φ t).det| : ℝ) : ℂ) * β' (Φ t) else 0`. Establish `hKsupp : Function.support K ⊆ C'`.

Introduce `t ht`. Distinguish the cases in `htS : t ∈ S`. Establish `hβt : β' (Φ t) ≠ 0`. Introduce `h0`. Apply `ht` to reduce the goal to its premises.

Simplify using `[K, htS, h0]`. Conclude with `⟨Φ t, subset_tsupport _ hβt, hψΦ t htS⟩`. Conclude with `absurd (by simp [K, htS]) ht`. Establish `hKts : tsupport K ⊆ C'` using `closure_minimal hKsupp hC'c.isClosed`. Establish `hK : ContDiff ℝ ∞ K`.

Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `t`. Distinguish the cases in `htS : t ∈ S`. Establish `hev : K =ᶠ[𝓝 t] fun s => ((|(fderiv ℝ Φ s).det| : ℝ) : ℂ) * β' (Φ s)` using `by filter_upwards [hSo.mem_nhds htS] with s hs`. Simplify using `[K, hs]`.

Use `ContDiffAt.congr_of_eventuallyEq ?_ hev` and prove the remaining obligations. Establish `hfd : ContDiffAt ℝ ∞ (fderiv ℝ Φ) t` using `(hΦat t htS).fderiv_right (by simp)`. Establish `hd : ContDiffAt ℝ ∞ (fun s => (fderiv ℝ Φ s).det) t` using `contDiff_det_pi.contDiffAt.comp t hfd`. Establish `ha : ContDiffAt ℝ ∞ (fun s => |(fderiv ℝ Φ s).det|) t`. Use `(contDiffAt_abs (n := ⊤) (hdet t htS)).comp t hd` as an intermediate fact.

Conclude with `this`. Conclude with `((Complex.ofRealCLM.contDiff.contDiffAt).comp t ha).mul (hβ'c.contDiffAt.comp t (hΦat t htS))`. Establish `hev : K =ᶠ[𝓝 t] fun _ => 0`. Establish `htC : t ∉ C'` using `fun hC => htS (hC'S hC)`. Use `filter_upwards [hC'c.isClosed.isOpen_compl.mem_nhds htC] with s hs`.

Assume the negation of the conclusion as `hne`. Conclude with `hs (hKsupp hne)`. Conclude with `contDiffAt_const.congr_of_eventuallyEq hev`. Take `⟨κ, hκs, hκc, hκt, hκint⟩` from `hdens K hK (hKts.trans hC'ε)`. Use `⟨κ, hκs, hκc, ?_, fun φ hφ => ?_⟩` and prove the remaining obligations.

Use `hκt.trans ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Take `⟨w, hw, rfl⟩` from `hKts ht`. Establish `hψw : ψ w ∈ S` using `hψTS (hβ'T hw)`. Use `⟨e w, hβ'e w hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[hPΦ _ hψw, hΦψ w (hβ'T hw)]`. Use `congr 1`. Rewrite using `[hκint φ hφ] set F : (Fin d → ℝ) → ℂ := fun w => β' w * φ (h.expG (b.equivFun.symm w)) with hF`. Establish `h1 : ∫ x, β x * φ (h.expG (coordEquiv b x)) = ∫ w, F w`. Use `(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp' (g := F)` as an intermediate fact.

Rewrite using `[← this]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[F, β', e, coordEquiv]`. Rewrite using `[h1]`. Use `set s := S ∩ Φ ⁻¹' T with hsdef`.

Establish `hs : IsOpen s` using `hΦs.continuousOn.isOpen_inter_preimage hSo hTo`. Establish `hΦs_img : Φ '' s = T`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩`.

Conclude with `ht.2`. Introduce `hw; exact ⟨ψ w, ⟨hψTS hw, by rw [mem_preimage, hΦψ w hw]; exact hw⟩, hΦψ w hw⟩`. Establish `h2 : ∫ w, F w = ∫ w in T, F w`. Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_).symm` and prove the remaining obligations. Establish `: β' w = 0` using `image_eq_zero_of_notMem_tsupport fun h' => hw (hβ'T h')`.

Simplify using `[F, this]`. Establish `hderiv : ∀ t ∈ s, HasFDerivWithinAt Φ (fderiv ℝ Φ t) s t` using `fun t ht => ((hΦat t ht.1).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt`. Establish `hinj : InjOn Φ s` using `fun t₁ ht₁ t₂ ht₂ he => by`. Rewrite using `[← hψΦ t₁ ht₁.1, ← hψΦ t₂ ht₂.1, he]`. Establish `h3` using `integral_image_eq_integral_abs_det_fderiv_smul volume hs.measurableSet hderiv hinj F`.

Rewrite `h3` using `[hΦs_img]`. Rewrite using `[h2, h3]`. Rewrite using `[← setIntegral_eq_integral_of_forall_compl_eq_zero (s := s) (f := fun t => K t * φ (P t)) fun t ht => by`. Distinguish the cases in `htS : t ∈ S`. Establish `hΦt : Φ t ∉ T` using `fun hT => ht ⟨htS, hT⟩`.

Establish `: β' (Φ t) = 0` using `image_eq_zero_of_notMem_tsupport fun h' => hΦt (hβ'T h')`. Simplify using `[K, htS, this]`. Simplify using `[K, htS]]`. Use `setIntegral_congr_fun hs.measurableSet fun t ht => ?_` and prove the remaining obligations. Simplify using `only [K, if_pos ht.1, F, Complex.real_smul, hPΦ t ht.1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_smooth_density_expCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ β : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ ∞ β →
      tsupport β ⊆ closedBall 0 ε →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧ tsupport κ ⊆ (fun x => h.expG (coordEquiv b x)) '' tsupport β ∧
        ∀ φ : G → ℂ, Continuous φ →
          ∫ y, κ y * φ y ∂μ = ∫ x, β x * φ (h.expG (coordEquiv b x)) := by
  classical
  obtain ⟨ε₁, hε₁, hdens⟩ := h.exists_smooth_density_prodExp_tsupport μ b
  obtain ⟨S, T, ψ, hSo, hTo, h0S, hΦST, hψTS, hψΦ, hΦψ, hψs, hSN⟩ := h.exists_prodExp_coord b
  set Φ := prodExpCoord b with hΦdef
  set P := h.prodExp (⇑b) with hPdef
  have hΦ0 : Φ 0 = 0 := prodExpCoord_zero b
  have h0T : (0 : Fin d → ℝ) ∈ T := hΦ0 ▸ hΦST h0S
  have hψ0 : ψ 0 = 0 := by have := hψΦ 0 h0S; rwa [hΦ0] at this

  have hSU : S ⊆ {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} :=
    fun t ht => h.nhdOne_subset_target (hSN t ht)
  have hΦs : ContDiffOn ℝ ∞ Φ S := (contDiffOn_prodExpCoord b).mono hSU
  have hΦat : ∀ t ∈ S, ContDiffAt ℝ ∞ Φ t := fun t ht => hΦs.contDiffAt (hSo.mem_nhds ht)
  have hψat : ∀ w ∈ T, ContDiffAt ℝ ∞ ψ w := fun w hw => hψs.contDiffAt (hTo.mem_nhds hw)

  have hPΦ : ∀ t ∈ S, P t = h.expG (b.equivFun.symm (Φ t)) := fun t ht =>
    h.prodExp_eq_expG_prodExpCoord b (hSN t ht)

  have hdet : ∀ t ∈ S, (fderiv ℝ Φ t).det ≠ 0 := by
    intro t ht
    have hΦt : HasFDerivAt Φ (fderiv ℝ Φ t) t := ((hΦat t ht).differentiableAt (by simp)).hasFDerivAt
    have hψt : HasFDerivAt ψ (fderiv ℝ ψ (Φ t)) (Φ t) :=
      ((hψat _ (hΦST ht)).differentiableAt (by simp)).hasFDerivAt
    have hcomp := hψt.comp t hΦt
    have hid : (ψ ∘ Φ) =ᶠ[𝓝 t] id := by
      filter_upwards [hSo.mem_nhds ht] with s hs
      exact hψΦ s hs
    have e : (fderiv ℝ ψ (Φ t)).comp (fderiv ℝ Φ t) = ContinuousLinearMap.id ℝ (Fin d → ℝ) := by
      rw [← hcomp.fderiv, hid.fderiv_eq, fderiv_id]
    intro h0
    have := congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L.det) e
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id] at this
    have h2 : LinearMap.det ((fderiv ℝ ψ (Φ t) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) ∘ₗ
        (fderiv ℝ Φ t : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) = 1 := this
    rw [LinearMap.det_comp] at h2
    replace this := h2
    rw [show LinearMap.det (fderiv ℝ Φ t : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = 0 from h0,
      mul_zero] at this
    exact zero_ne_one this

  have hψc : ContinuousAt ψ 0 := (hψat 0 h0T).continuousAt
  obtain ⟨δ, hδ, hδT⟩ := Metric.isOpen_iff.1 hTo 0 h0T
  obtain ⟨η, hη, hηψ⟩ := Metric.continuousAt_iff.1 hψc ε₁ hε₁
  refine ⟨min (δ / 2) (η / 2), lt_min (by positivity) (by positivity), fun β hβ hβs => ?_⟩
  set ε := min (δ / 2) (η / 2) with hεdef
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεη : ε < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)

  set e : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := fun w => WithLp.toLp 2 w with he
  set β' : (Fin d → ℝ) → ℂ := fun w => β (e w) with hβ'
  have he_cont : Continuous e := PiLp.continuous_toLp 2 _
  have hβ'c : ContDiff ℝ ∞ β' := hβ.comp PiLp.contDiff_toLp
  have hnorm : ∀ w : Fin d → ℝ, ‖w‖ ≤ ‖e w‖ := fun w =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
      simpa [e] using PiLp.norm_apply_le (e w) i
  have hβ's : tsupport β' ⊆ closedBall 0 ε := by
    refine closure_minimal (fun w hw => ?_) isClosed_closedBall
    have : e w ∈ closedBall 0 ε := hβs (subset_tsupport _ hw)
    rw [mem_closedBall_zero_iff] at this ⊢
    exact (hnorm w).trans this
  have hβ'T : tsupport β' ⊆ T := fun w hw => hδT (by
    have := hβ's hw
    rw [mem_closedBall_zero_iff] at this
    rw [mem_ball_zero_iff]; linarith)
  have hβ'comp : IsCompact (tsupport β') :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hβ's
  have hβ'e : ∀ w ∈ tsupport β', e w ∈ tsupport β := by
    intro w hw
    have : tsupport β' ⊆ e ⁻¹' tsupport β :=
      closure_minimal (fun v hv => subset_tsupport _ hv) ((isClosed_tsupport β).preimage he_cont)
    exact this hw

  set C' := ψ '' tsupport β' with hC'def
  have hC'c : IsCompact C' := hβ'comp.image_of_continuousOn (hψs.continuousOn.mono hβ'T)
  have hC'S : C' ⊆ S := by rintro _ ⟨w, hw, rfl⟩; exact hψTS (hβ'T hw)
  have hC'ε : C' ⊆ closedBall 0 ε₁ := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' := hβ's hw
    rw [mem_closedBall_zero_iff] at hw'
    have := hηψ (x := w) (by rw [dist_zero_right]; linarith)
    rw [hψ0, dist_zero_right] at this
    rw [mem_closedBall_zero_iff]; exact this.le
  let K : (Fin d → ℝ) → ℂ := fun t =>
    if t ∈ S then ((|(fderiv ℝ Φ t).det| : ℝ) : ℂ) * β' (Φ t) else 0
  have hKsupp : Function.support K ⊆ C' := by
    intro t ht
    by_cases htS : t ∈ S
    · have hβt : β' (Φ t) ≠ 0 := by
        intro h0; apply ht; simp [K, htS, h0]
      exact ⟨Φ t, subset_tsupport _ hβt, hψΦ t htS⟩
    · exact absurd (by simp [K, htS]) ht
  have hKts : tsupport K ⊆ C' := closure_minimal hKsupp hC'c.isClosed
  have hK : ContDiff ℝ ∞ K := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases htS : t ∈ S
    · have hev : K =ᶠ[𝓝 t] fun s => ((|(fderiv ℝ Φ s).det| : ℝ) : ℂ) * β' (Φ s) := by
        filter_upwards [hSo.mem_nhds htS] with s hs
        simp [K, hs]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hfd : ContDiffAt ℝ ∞ (fderiv ℝ Φ) t := (hΦat t htS).fderiv_right (by simp)
      have hd : ContDiffAt ℝ ∞ (fun s => (fderiv ℝ Φ s).det) t :=
        contDiff_det_pi.contDiffAt.comp t hfd
      have ha : ContDiffAt ℝ ∞ (fun s => |(fderiv ℝ Φ s).det|) t := by
        have := (contDiffAt_abs (n := ⊤) (hdet t htS)).comp t hd
        exact this
      exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp t ha).mul
        (hβ'c.contDiffAt.comp t (hΦat t htS))
    · have hev : K =ᶠ[𝓝 t] fun _ => 0 := by
        have htC : t ∉ C' := fun hC => htS (hC'S hC)
        filter_upwards [hC'c.isClosed.isOpen_compl.mem_nhds htC] with s hs
        by_contra hne
        exact hs (hKsupp hne)
      exact contDiffAt_const.congr_of_eventuallyEq hev
  obtain ⟨κ, hκs, hκc, hκt, hκint⟩ := hdens K hK (hKts.trans hC'ε)
  refine ⟨κ, hκs, hκc, ?_, fun φ hφ => ?_⟩
  ·
    refine hκt.trans ?_
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hKts ht
    have hψw : ψ w ∈ S := hψTS (hβ'T hw)
    refine ⟨e w, hβ'e w hw, ?_⟩
    rw [hPΦ _ hψw, hΦψ w (hβ'T hw)]
    congr 1
  · rw [hκint φ hφ]
    set F : (Fin d → ℝ) → ℂ := fun w => β' w * φ (h.expG (b.equivFun.symm w)) with hF

    have h1 : ∫ x, β x * φ (h.expG (coordEquiv b x)) = ∫ w, F w := by
      have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
        (g := F)
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [F, β', e, coordEquiv]
    rw [h1]

    set s := S ∩ Φ ⁻¹' T with hsdef
    have hs : IsOpen s := hΦs.continuousOn.isOpen_inter_preimage hSo hTo
    have hΦs_img : Φ '' s = T := by
      ext w; constructor
      · rintro ⟨t, ht, rfl⟩; exact ht.2
      · intro hw; exact ⟨ψ w, ⟨hψTS hw, by rw [mem_preimage, hΦψ w hw]; exact hw⟩, hΦψ w hw⟩
    have h2 : ∫ w, F w = ∫ w in T, F w := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_).symm
      have : β' w = 0 := image_eq_zero_of_notMem_tsupport fun h' => hw (hβ'T h')
      simp [F, this]
    have hderiv : ∀ t ∈ s, HasFDerivWithinAt Φ (fderiv ℝ Φ t) s t := fun t ht =>
      ((hΦat t ht.1).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
    have hinj : InjOn Φ s := fun t₁ ht₁ t₂ ht₂ he => by
      rw [← hψΦ t₁ ht₁.1, ← hψΦ t₂ ht₂.1, he]
    have h3 := integral_image_eq_integral_abs_det_fderiv_smul volume hs.measurableSet hderiv hinj F
    rw [hΦs_img] at h3
    rw [h2, h3]

    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := s)
      (f := fun t => K t * φ (P t)) fun t ht => by
        by_cases htS : t ∈ S
        · have hΦt : Φ t ∉ T := fun hT => ht ⟨htS, hT⟩
          have : β' (Φ t) = 0 := image_eq_zero_of_notMem_tsupport fun h' => hΦt (hβ'T h')
          simp [K, htS, this]
        · simp [K, htS]]
    refine setIntegral_congr_fun hs.measurableSet fun t ht => ?_
    simp only [K, if_pos ht.1, F, Complex.real_smul, hPΦ t ht.1]
    ring

end IsExpLieAlgebra

end GroundTheory.Automorphic

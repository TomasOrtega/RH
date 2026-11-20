import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexTaylor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix Metric

noncomputable section

/- English proof (translation)
Use `set L := fderiv ℝ f x`. Use `set H := fderiv ℝ (fderiv ℝ f) x with hHdef`. Establish `hsymm : IsSymmSndFDerivAt ℝ f x` using `hf.isSymmSndFDerivAt (by simp)`. Establish `hH : HasFDerivAt (fderiv ℝ f) H x` using `((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt`. Establish `ho` using `hasFDerivAt_iff_isLittleO_nhds_zero.1 hH`.

Establish `htend : Tendsto (fun z : E => x + z) (𝓝 0) (𝓝 x)`. Establish `: Continuous fun z : E => x + z` using `continuous_const.add continuous_id`. Simplify using `using this.tendsto (0 : E)`. Establish `hdiff : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℝ f (x + z)` using `htend.eventually ((hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp))`. Use `isLittleO_iff.2 fun ε hε => ?_` and prove the remaining obligations.

Establish `hb` using `(isLittleO_iff.1 ho hε).and hdiff`. Take `⟨δ, hδ, hball⟩` from `Metric.eventually_nhds_iff_ball.1 hb`. Use `filter_upwards [ball_mem_nhds (0 : E) hδ] with z hz`. Use `set g : E → ℝ := fun w => f (x + w) - f x - L w - (2 : ℝ)⁻¹ • H w w with hg`. Establish `hderiv : ∀ w ∈ ball (0 : E) δ, HasFDerivAt g (fderiv ℝ f (x + w) - L - H w) w`.

Introduce `w hw`. Establish `h1 : HasFDerivAt (fun w => f (x + w)) ((fderiv ℝ f (x + w)).comp (ContinuousLinearMap.id ℝ E)) w` using `(hball w hw).2.hasFDerivAt.comp w ((hasFDerivAt_id w).const_add x)`. Establish `h2 : HasFDerivAt (fun w => H w w) ((H w).comp (ContinuousLinearMap.id ℝ E) + H.flip w) w` using `H.hasFDerivAt.clm_apply (hasFDerivAt_id w)`. Establish `h3` using `((h1.sub_const (f x)).sub L.hasFDerivAt).sub (h2.const_smul (2 : ℝ)⁻¹)`. Use `h3.congr_fderiv ?_` and prove the remaining obligations.

Use extensionality with `v`. Simplify using `only [_root_.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, _root_.smul_apply, _root_.add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]`. Use `hsymm v w` as an intermediate fact. Rewrite `this` using `[← hHdef]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hz' : ‖z‖ < δ` using `by simpa using hz`. Establish `hsub : closedBall (0 : E) ‖z‖ ⊆ ball 0 δ` using `closedBall_subset_ball hz'`. Establish `hbound : ∀ w ∈ closedBall (0 : E) ‖z‖, ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖z‖`. Introduce `w hw`.

Establish `hw'` using `(hball w (hsub hw)).1`. Establish `hwz : ‖w‖ ≤ ‖z‖` using `by simpa using hw`. Combine the equalities or inequalities in the displayed calculation. Establish `hz0 : z ∈ closedBall (0 : E) ‖z‖` using `by simp`. Establish `hmvt` using `(convex_closedBall (0 : E) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le (fun w hw => (hderiv w (hsub hw)).hasFDerivWithinAt) hbound (mem_closedBall_self (norm_nonneg z)) hz0`.

Establish `hg0 : g 0 = 0` using `by simp [hg]`. Rewrite `hmvt` using `[hg0, sub_zero, sub_zero]`. Establish `: g z = f (x + z) - f x - L z - H z z / 2`. Simplify using `only [hg, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← this, norm_pow, norm_norm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem taylor_two_isLittleO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (fun z => f (x + z) - f x - fderiv ℝ f x z - fderiv ℝ (fderiv ℝ f) x z z / 2)
      =o[𝓝 0] fun z => ‖z‖ ^ 2 := by
  set L := fderiv ℝ f x
  set H := fderiv ℝ (fderiv ℝ f) x with hHdef
  have hsymm : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  have hH : HasFDerivAt (fderiv ℝ f) H x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.1 hH
  have htend : Tendsto (fun z : E => x + z) (𝓝 0) (𝓝 x) := by
    have : Continuous fun z : E => x + z := continuous_const.add continuous_id
    simpa using this.tendsto (0 : E)
  have hdiff : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℝ f (x + z) :=
    htend.eventually ((hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp))
  refine isLittleO_iff.2 fun ε hε => ?_
  have hb := (isLittleO_iff.1 ho hε).and hdiff
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hb
  filter_upwards [ball_mem_nhds (0 : E) hδ] with z hz
  set g : E → ℝ := fun w => f (x + w) - f x - L w - (2 : ℝ)⁻¹ • H w w with hg
  have hderiv : ∀ w ∈ ball (0 : E) δ, HasFDerivAt g (fderiv ℝ f (x + w) - L - H w) w := by
    intro w hw
    have h1 : HasFDerivAt (fun w => f (x + w)) ((fderiv ℝ f (x + w)).comp
        (ContinuousLinearMap.id ℝ E)) w :=
      (hball w hw).2.hasFDerivAt.comp w ((hasFDerivAt_id w).const_add x)
    have h2 : HasFDerivAt (fun w => H w w) ((H w).comp (ContinuousLinearMap.id ℝ E) + H.flip w) w :=
      H.hasFDerivAt.clm_apply (hasFDerivAt_id w)
    have h3 := ((h1.sub_const (f x)).sub L.hasFDerivAt).sub (h2.const_smul (2 : ℝ)⁻¹)
    refine h3.congr_fderiv ?_
    ext v
    simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, _root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    have := hsymm v w
    rw [← hHdef] at this
    rw [this]
    ring
  have hz' : ‖z‖ < δ := by simpa using hz
  have hsub : closedBall (0 : E) ‖z‖ ⊆ ball 0 δ := closedBall_subset_ball hz'
  have hbound : ∀ w ∈ closedBall (0 : E) ‖z‖, ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖z‖ := by
    intro w hw
    have hw' := (hball w (hsub hw)).1
    have hwz : ‖w‖ ≤ ‖z‖ := by simpa using hw
    calc ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖w‖ := hw'
      _ ≤ ε * ‖z‖ := by gcongr
  have hz0 : z ∈ closedBall (0 : E) ‖z‖ := by simp
  have hmvt := (convex_closedBall (0 : E) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw => (hderiv w (hsub hw)).hasFDerivWithinAt) hbound
    (mem_closedBall_self (norm_nonneg z)) hz0
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, sub_zero] at hmvt
  have : g z = f (x + z) - f x - L z - H z z / 2 := by
    simp only [hg, smul_eq_mul]; ring
  rw [← this, norm_pow, norm_norm]
  calc ‖g z‖ ≤ ε * ‖z‖ * ‖z‖ := hmvt
    _ = ε * ‖z‖ ^ 2 := by ring

def complexLinearCoeffs {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) : Fin D → ℂ :=
  fun j => (L (Pi.single j 1) : ℂ) - Complex.I * (L (Complex.I • Pi.single j 1) : ℂ)

/- English proof (translation)
Establish `hz : z = ∑ j, ((z j).re • (Pi.single j 1 : Fin D → ℂ) + (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ)))`. Use extensionality with `k`. Apply the tactic sequence `apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]`. Use `conv_rhs => rw [hz]`. Simplify using `only [map_sum, map_add, map_smul, dotProduct, Complex.re_sum, smul_eq_mul]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [complexLinearCoeffs, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem re_complexLinearCoeffs_dot {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (complexLinearCoeffs L ⬝ᵥ z).re = L z := by
  have hz : z = ∑ j, ((z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ))) := by
    ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  conv_rhs => rw [hz]
  simp only [map_sum, map_add, map_smul, dotProduct, Complex.re_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [complexLinearCoeffs, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

def complexQuadMatrix {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun j k =>
    let ej : Fin D → ℂ := Pi.single j 1
    let ek : Fin D → ℂ := Pi.single k 1
    ((H ej ek - H (Complex.I • ej) (Complex.I • ek) : ℝ) -
      Complex.I * ((H ej (Complex.I • ek) + H (Complex.I • ej) ek : ℝ))) / 4

/- English proof (translation)
Take `⟨c, hc⟩ : ∃ c : Fin D → (Fin D → ℂ), c = fun j => (z j).re • (Pi.single j 1 : Fin D → ℂ) + (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ))` from `⟨_, rfl⟩`. Take `⟨d, hd⟩ : ∃ d : Fin D → (Fin D → ℂ), d = fun j => (z j).re • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) + (-(z j).im) • (Pi.single j 1 : Fin D → ℂ)` from `⟨_, rfl⟩`. Establish `hz : z = ∑ j, c j`. Rewrite using `[hc]`. Use extensionality with `k`.

Apply the tactic sequence `apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]`. Establish `hIz : Complex.I • z = ∑ j, d j`. Rewrite using `[hd]`. Use extensionality with `k`. Apply the tactic sequence `apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]`.

Establish `expand : ∀ c : Fin D → (Fin D → ℂ), H (Finset.sum Finset.univ c) (Finset.sum Finset.univ c) = ∑ i, ∑ k, H (c i) (c k)`. Introduce `c`. Simplify using `only [map_sum, _root_.sum_apply]`. Rewrite using `[Finset.sum_comm]`. Establish `e1 : H z z = ∑ i, ∑ k, H (c i) (c k)`.

Combine the equalities or inequalities in the displayed calculation. Establish `e2 : H (Complex.I • z) (Complex.I • z) = ∑ i, ∑ k, H (d i) (d k)`. Rewrite using `[hIz]`. Conclude with `expand d`. Establish `hR : (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re = ∑ i, ∑ k, (z i * (complexQuadMatrix H i k * z k)).re`.

Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum]`. Rewrite using `[hR, e1, e2, ← Finset.sum_sub_distrib, Finset.sum_div]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_div]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Substitute `hc hd` using the available equality. Simplify using `only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]`. Simplify using `only [complexQuadMatrix, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem re_dot_complexQuadMatrix {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (z : Fin D → ℂ) :
    (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re = (H z z - H (Complex.I • z) (Complex.I • z)) / 4 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin D → (Fin D → ℂ), c = fun j => (z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin D → (Fin D → ℂ), d = fun j =>
      (z j).re • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) +
      (-(z j).im) • (Pi.single j 1 : Fin D → ℂ) := ⟨_, rfl⟩
  have hz : z = ∑ j, c j := by
    rw [hc]; ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have hIz : Complex.I • z = ∑ j, d j := by
    rw [hd]; ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have expand : ∀ c : Fin D → (Fin D → ℂ),
      H (Finset.sum Finset.univ c) (Finset.sum Finset.univ c) = ∑ i, ∑ k, H (c i) (c k) := by
    intro c
    simp only [map_sum, _root_.sum_apply]
    rw [Finset.sum_comm]
  have e1 : H z z = ∑ i, ∑ k, H (c i) (c k) := by
    calc H z z = H (∑ j, c j) (∑ j, c j) := by rw [← hz]
      _ = _ := expand c
  have e2 : H (Complex.I • z) (Complex.I • z) = ∑ i, ∑ k, H (d i) (d k) := by
    rw [hIz]; exact expand d
  have hR : (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re =
      ∑ i, ∑ k, (z i * (complexQuadMatrix H i k * z k)).re := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum]
  rw [hR, e1, e2, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  subst hc hd
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp only [complexQuadMatrix, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/- English proof (translation)
Introduce `D ψ y₀ hψ`. Use `⟨complexLinearCoeffs (fderiv ℝ ψ y₀), complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀), ?_⟩` and prove the remaining obligations. Use `(taylor_two_isLittleO hψ).congr_left fun z => ?_` and prove the remaining obligations. Establish `h1` using `re_complexLinearCoeffs_dot (fderiv ℝ ψ y₀) z`. Establish `h2` using `re_dot_complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀) z`.

Establish `h3` using `ReciprocityTheory.AnForm.M.re_star_dot_hessC ψ y₀ (star z)`. Rewrite `h3` using `[star_star]`. Rewrite using `[Complex.add_re, h1, h2, h3]`. Unfold `levi`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ComplexTaylorTwo.proof : ComplexTaylorTwo.Statement := by
  intro D ψ y₀ hψ
  refine ⟨complexLinearCoeffs (fderiv ℝ ψ y₀), complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀), ?_⟩
  refine (taylor_two_isLittleO hψ).congr_left fun z => ?_
  have h1 := re_complexLinearCoeffs_dot (fderiv ℝ ψ y₀) z
  have h2 := re_dot_complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀) z
  have h3 := ReciprocityTheory.AnForm.M.re_star_dot_hessC ψ y₀ (star z)
  rw [star_star] at h3
  rw [Complex.add_re, h1, h2, h3]
  unfold levi
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

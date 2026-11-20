import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Development
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Use `fun_prop`.
-/
lemma exp_flow_cont {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  fun_prop

end Linfty

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma flow_zero (g : Matrix (Fin n) (Fin n) ℂ) :
    g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
  simp

/- English proof (translation)
Establish `h0` using `Formalism.REAL.hasDerivAt_matrix_exp_smul_at_zero X`. Establish `hc : HasDerivAt (fun u : ℝ => g * NormedSpace.exp ((u : ℂ) • X)) (g * X) 0`. Establish `hL` using `(LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ g)).hasFDerivAt (x := NormedSpace.exp (((0 : ℝ) : ℂ) • X))`. Conclude with `hL.comp_hasDerivAt (0 : ℝ) h0`. Establish `hFd : HasFDerivAt F (fderiv ℝ F g) g` using `((hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)).hasFDerivAt`.

Establish `hcomp : HasDerivAt (fun u : ℝ => F (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0` using `hFd.comp_hasDerivAt_of_eq (0 : ℝ) hc (flow_zero g).symm`. Establish `hU0 : U ∈ 𝓝 (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))`. Rewrite using `[flow_zero]`. Conclude with `hU.mem_nhds hgU`. Establish `hev : (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) =ᶠ[𝓝 0] (fun u : ℝ => F (g * NormedSpace.exp ((u : ℂ) • X)))` using `by filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with u hu`.

Conclude with `hfF _ hu (hG g hg u)`. Conclude with `hcomp.congr_of_eventuallyEq hev`.
-/
lemma hasDerivAt_local (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f F : Matrix (Fin n) (Fin n) ℂ → ℂ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ G → f h = F h) (hg : g ∈ G) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have h0 := Formalism.REAL.hasDerivAt_matrix_exp_smul_at_zero X
  have hc : HasDerivAt (fun u : ℝ => g * NormedSpace.exp ((u : ℂ) • X)) (g * X) 0 := by
    have hL := (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ g)).hasFDerivAt
      (x := NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    exact hL.comp_hasDerivAt (0 : ℝ) h0
  have hFd : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasDerivAt (fun u : ℝ => F (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 :=
    hFd.comp_hasDerivAt_of_eq (0 : ℝ) hc (flow_zero g).symm
  have hU0 : U ∈ 𝓝 (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [flow_zero]; exact hU.mem_nhds hgU
  have hev : (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) =ᶠ[𝓝 0]
      (fun u : ℝ => F (g * NormedSpace.exp ((u : ℂ) • X))) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with u hu
    exact hfF _ hu (hG g hg u)
  exact hcomp.congr_of_eventuallyEq hev

/- English proof (translation)
The claim follows from `(hasDerivAt_local hG hU hgU hF hfF hg).deriv`.
-/
lemma rdV_local (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f F : Matrix (Fin n) (Fin n) ℂ → ℂ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ G → f h = F h) (hg : g ∈ G) :
    RdV X f g = fderiv ℝ F g (g * X) := (hasDerivAt_local hG hU hgU hF hfF hg).deriv

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g hg`. Rewrite using `[rdV_local hG hU hgU hF hfF hg]`. Conclude with `hasDerivAt_local hG hU hgU hF hfF hg`.
-/
lemma hasDerivAt_zero (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (RdV X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rdV_local hG hU hgU hF hfF hg]
  exact hasDerivAt_local hG hU hgU hF hfF hg

/- English proof (translation)
Establish `hh : g * NormedSpace.exp ((t : ℂ) • X) ∈ G` using `hG g hg t`. Establish `h0` using `hasDerivAt_zero hG hf hh`. Establish `h0' : HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X))) (RdV X f (g * NormedSpace.exp ((t : ℂ) • X))) (t - t)`. Rewrite using `[sub_self]`. Conclude with `h0`.

Use `(h0'.comp_sub_const t t).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `show f (g * NormedSpace.exp ((s : ℂ) • X)) = f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X))`. Establish `hcomm : Commute ((t : ℂ) • X) (((s - t : ℝ) : ℂ) • X)` using `((Commute.refl X).smul_left _).smul_right _`. Establish `e : (t : ℂ) • X + ((s - t : ℝ) : ℂ) • X = (s : ℂ) • X`. Rewrite using `[← add_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_assoc, ← Matrix.exp_add_of_commute _ _ hcomm, e]`.
-/
lemma hasDerivAt_shift (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X)))
      (RdV X f (g * NormedSpace.exp ((t : ℂ) • X))) t := by
  have hh : g * NormedSpace.exp ((t : ℂ) • X) ∈ G := hG g hg t
  have h0 := hasDerivAt_zero hG hf hh
  have h0' : HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X)))
      (RdV X f (g * NormedSpace.exp ((t : ℂ) • X))) (t - t) := by
    rw [sub_self]; exact h0
  refine (h0'.comp_sub_const t t).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show f (g * NormedSpace.exp ((s : ℂ) • X)) =
    f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X))
  have hcomm : Commute ((t : ℂ) • X) (((s - t : ℝ) : ℂ) • X) :=
    ((Commute.refl X).smul_left _).smul_right _
  have e : (t : ℂ) • X + ((s - t : ℝ) : ℂ) • X = (s : ℂ) • X := by
    rw [← add_smul]; congr 1; push_cast; ring
  rw [mul_assoc, ← Matrix.exp_add_of_commute _ _ hcomm, e]

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg₀U, hF, hfF⟩` from `hf g₀ hg₀`. Establish `hFc : ContinuousAt F g₀` using `hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)`. Use `hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)` and prove the remaining obligations. Use `filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgG`.

Conclude with `hfF g hgU hgG`.
-/
lemma contOn_of_smooth {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) : ContinuousOn f G := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgG
  exact hfF g hgU hgG

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg₀U, hF, hfF⟩` from `hf g₀ hg₀`. Establish `hd : ContinuousOn (fderiv ℝ F) U` using `hF.continuousOn_fderiv_of_isOpen hU (by simp)`. Establish `hc : ContinuousAt (fun g => fderiv ℝ F g (g * X)) g₀` using `(hd.continuousAt (hU.mem_nhds hg₀U)).clm_apply ((continuous_id.matrix_mul continuous_const).continuousAt)`. Use `hc.continuousWithinAt.congr_of_eventuallyEq ?_ (rdV_local hG hU hg₀U hF hfF hg₀)` and prove the remaining obligations.

Use `filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgG`. Conclude with `rdV_local hG hU hgU hF hfF hgG`.
-/
lemma contOn_rdV (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) : ContinuousOn (RdV X f) G := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hd : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU (by simp)
  have hc : ContinuousAt (fun g => fderiv ℝ F g (g * X)) g₀ :=
    (hd.continuousAt (hU.mem_nhds hg₀U)).clm_apply
      ((continuous_id.matrix_mul continuous_const).continuousAt)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (rdV_local hG hU hg₀U hF hfF hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgG
  exact rdV_local hG hU hgU hF hfF hgG

end QnRdSkewW

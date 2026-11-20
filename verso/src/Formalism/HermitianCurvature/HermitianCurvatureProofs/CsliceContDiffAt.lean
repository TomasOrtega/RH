import Formalism.HermitianCurvature.HermitianCurvatureProofs.HsRealSmulRight

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Introduce `j`. Distinguish the cases in `hj : j = l`. Substitute `hj` using the available equality. Simplify using `using ht`. Rewrite using `[Function.update_of_ne hj]`.

Conclude with `hc j`.
-/
theorem update_mem_OmX {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) {t : ℂ} (ht : t ≠ 0) :
    Function.update c l t ∈ OmX r := by
  intro j
  by_cases hj : j = l
  · subst hj; simpa using ht
  · rw [Function.update_of_ne hj]; exact hc j

/- English proof (translation)
Distinguish the cases in `hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g`. Take `⟨-, hs, -⟩` from `Φ.2`. Take `⟨U, F, hU, hxU, hF, hΦ⟩` from `hs (x, g) ⟨hx, hg.1, hg.2⟩`. Establish `hcont : Continuous (fun c' : Fin r → ℂ => (c', g))` using `continuous_id.prodMk continuous_const`. Establish `hV : IsOpen ((fun c' : Fin r → ℂ => (c', g)) ⁻¹' U)` using `hU.preimage hcont`.

Establish `hFx : ContDiffAt ℝ ∞ (fun c' : Fin r → ℂ => F (c', g)) x` using `(hF.contDiffAt (hU.mem_nhds hxU)).comp x (contDiff_id.prodMk contDiff_const).contDiffAt`. Use `hFx.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hV.mem_nhds hxU] with c' hc'`. Conclude with `hΦ (c', g) hc' hg.1`. Establish `h0 : (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) = fun _ => 0`.

Use function extensionality and compare the values at `c'`. Conclude with `radSp_zero_off Φ (x := (c', g)) (fun h => hg ⟨h.2.1, h.2.2⟩)`. Rewrite using `[h0]`. Conclude with `contDiffAt_const`.
-/
theorem cslice_contDiffAt (Φ : RadSp k r z z' π π') (g : Mx k r) {x : Fin r → ℂ} (hx : x ∈ OmX r) :
    ContDiffAt ℝ ∞ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) x := by
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨-, hs, -⟩ := Φ.2
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (x, g) ⟨hx, hg.1, hg.2⟩
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := continuous_id.prodMk continuous_const
    have hV : IsOpen ((fun c' : Fin r → ℂ => (c', g)) ⁻¹' U) := hU.preimage hcont
    have hFx : ContDiffAt ℝ ∞ (fun c' : Fin r → ℂ => F (c', g)) x :=
      (hF.contDiffAt (hU.mem_nhds hxU)).comp x (contDiff_id.prodMk contDiff_const).contDiffAt
    refine hFx.congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hxU] with c' hc'
    exact hΦ (c', g) hc' hg.1
  · have h0 : (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) = fun _ => 0 := by
      funext c'
      exact radSp_zero_off Φ (x := (c', g)) (fun h => hg ⟨h.2.1, h.2.2⟩)
    rw [h0]; exact contDiffAt_const

/- English proof (translation)
Establish `hu` using `hasFDerivAt_update (𝕜 := ℝ) c (i := l) t`. Establish `h` using `hf.hasFDerivAt.comp t hu`. Establish `hd : ∀ v : ℂ, fderiv ℝ (fun s => f (Function.update c l s)) t v = fderiv ℝ f (Function.update c l t) (Pi.single l v)`. Introduce `v`. Rewrite using `[show (fun s => f (Function.update c l s)) = f ∘ Function.update c l from rfl, h.fderiv]`.

Simplify using `only [ContinuousLinearMap.comp_apply]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = l`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hj]`. Prove the components needed by the constructor for the conclusion. Unfold `dZv wirt`. Rewrite using `[hd, hd]`.

Unfold `dZbv wirtBar`. Rewrite using `[hd, hd]`.
-/
theorem dZv_update {f : (Fin r → ℂ) → (Wq →L[ℂ] Wp)} (c : Fin r → ℂ) (l : Fin r) (t : ℂ)
    (hf : DifferentiableAt ℝ f (Function.update c l t)) :
    dZv (fun s => f (Function.update c l s)) t = wirt l f (Function.update c l t) ∧
      dZbv (fun s => f (Function.update c l s)) t = wirtBar l f (Function.update c l t) := by
  have hu := hasFDerivAt_update (𝕜 := ℝ) c (i := l) t
  have h := hf.hasFDerivAt.comp t hu
  have hd : ∀ v : ℂ, fderiv ℝ (fun s => f (Function.update c l s)) t v =
      fderiv ℝ f (Function.update c l t) (Pi.single l v) := by
    intro v
    rw [show (fun s => f (Function.update c l s)) = f ∘ Function.update c l from rfl, h.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    congr 1
    funext j
    by_cases hj : j = l
    · subst hj; simp
    · simp [hj]
  constructor
  · unfold dZv wirt; rw [hd, hd]
  · unfold dZbv wirtBar; rw [hd, hd]

/- English proof (translation)
Use `set fΦ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g with hfΦ`. Use `set fΨ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g with hfΨ`. Use `set A : ℂ → (Wq →L[ℂ] Wp) := fun t => fΦ (Function.update c l t) with hA`. Use `set Bf : ℂ → (Wq →L[ℂ] Wp) := fun t => fΨ (Function.update c l t) with hB`. Establish `hupd : ContDiff ℝ ∞ (fun t : ℂ => Function.update c l t)` using `contDiff_pi.mpr fun j => by`.

Distinguish the cases in `hj : j = l`. Substitute `hj` using the available equality. Simplify using `only [Function.update_self]`. Conclude with `contDiff_id`. Simplify `contDiff_const` using `[Function.update_of_ne hj]`.

Establish `hAc : ContDiffOn ℝ 1 A {t | t ≠ 0}` using `fun t ht => (((cslice_contDiffAt Φ g (update_mem_OmX hc l ht)).comp t hupd.contDiffAt).of_le (by simp)).contDiffWithinAt`. Establish `hBc : ContDiffOn ℝ 1 Bf {t | t ≠ 0}` using `fun t ht => (((cslice_contDiffAt Ψ g (update_mem_OmX hc l ht)).comp t hupd.contDiffAt).of_le (by simp)).contDiffWithinAt`. Establish `hpΦ : ∀ t : ℂ, t ≠ 0 → (X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g = t • dZv A t`. Introduce `t ht`. Establish `hd` using `dZv_update (f := fΦ) c l t ((cslice_contDiffAt Φ g (update_mem_OmX hc l ht)).differentiableAt (by simp))`.

Rewrite using `[X.op_apply, hd.1]`. Use `show pOp l fΦ (Function.update c l t) = _`. Unfold `pOp`. Rewrite using `[if_pos (update_mem_OmX hc l ht), Function.update_self]`. Establish `hpΨ : ∀ t : ℂ, t ≠ 0 → (X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g = conj t • dZbv Bf t`.

Introduce `t ht`. Establish `hd` using `dZv_update (f := fΨ) c l t ((cslice_contDiffAt Ψ g (update_mem_OmX hc l ht)).differentiableAt (by simp))`. Rewrite using `[X.op_apply, hd.2]`. Use `show pbOp l fΨ (Function.update c l t) = _`. Unfold `pbOp`.

Rewrite using `[if_pos (update_mem_OmX hc l ht), Function.update_self]`. Both sides reduce to the same expression. Establish `e1 : (fun t : ℂ => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)) = fun t => B.hsInner (t • dZv A t) (Bf t) / ((‖t‖ ^ 2 : ℝ) : ℂ)`. Use function extensionality and compare the values at `t`. Distinguish the cases in `ht : t = 0`.

Substitute `ht` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[hpΦ t ht]`. Establish `e2 : (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)) = fun t => B.hsInner (A t) (conj t • dZbv Bf t) / ((‖t‖ ^ 2 : ℝ) : ℂ)`. Use function extensionality and compare the values at `t`.

Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[hpΨ t ht]`. Establish `h1'` using `e1 ▸ h1`.

Establish `h2'` using `e2 ▸ h2`. Rewrite using `[e1, e2]`. Conclude with `pLogAdjHS A Bf hAc hBc h0 h1' h2'`.
-/
theorem site_p_adj_g (X : ActualOps k r z z' π π') (Φ Ψ : RadSp k r z z' π π') (l : Fin r) (c : Fin r → ℂ)
    (hc : c ∈ OmX r) (g : Mx k r)
    (h0 : Integrable (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)))
    (h1 : Integrable (fun t : ℂ => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)))
    (h2 : Integrable (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ))) :
    ∫ t : ℂ, B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ) =
    -∫ t : ℂ, B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  set fΦ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g with hfΦ
  set fΨ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g with hfΨ
  set A : ℂ → (Wq →L[ℂ] Wp) := fun t => fΦ (Function.update c l t) with hA
  set Bf : ℂ → (Wq →L[ℂ] Wp) := fun t => fΨ (Function.update c l t) with hB
  have hupd : ContDiff ℝ ∞ (fun t : ℂ => Function.update c l t) :=
    contDiff_pi.mpr fun j => by
      by_cases hj : j = l
      · subst hj; simp only [Function.update_self]; exact contDiff_id
      · simpa [Function.update_of_ne hj] using contDiff_const
  have hAc : ContDiffOn ℝ 1 A {t | t ≠ 0} := fun t ht =>
    (((cslice_contDiffAt Φ g (update_mem_OmX hc l ht)).comp t hupd.contDiffAt).of_le (by simp)).contDiffWithinAt
  have hBc : ContDiffOn ℝ 1 Bf {t | t ≠ 0} := fun t ht =>
    (((cslice_contDiffAt Ψ g (update_mem_OmX hc l ht)).comp t hupd.contDiffAt).of_le (by simp)).contDiffWithinAt
  have hpΦ : ∀ t : ℂ, t ≠ 0 → (X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g = t • dZv A t := by
    intro t ht
    have hd := dZv_update (f := fΦ) c l t
      ((cslice_contDiffAt Φ g (update_mem_OmX hc l ht)).differentiableAt (by simp))
    rw [X.op_apply, hd.1]
    show pOp l fΦ (Function.update c l t) = _
    unfold pOp
    rw [if_pos (update_mem_OmX hc l ht), Function.update_self]
  have hpΨ : ∀ t : ℂ, t ≠ 0 → (X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g =
      conj t • dZbv Bf t := by
    intro t ht
    have hd := dZv_update (f := fΨ) c l t
      ((cslice_contDiffAt Ψ g (update_mem_OmX hc l ht)).differentiableAt (by simp))
    rw [X.op_apply, hd.2]
    show pbOp l fΨ (Function.update c l t) = _
    unfold pbOp
    rw [if_pos (update_mem_OmX hc l ht), Function.update_self]
    rfl
  have e1 : (fun t : ℂ => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)) =
      fun t => B.hsInner (t • dZv A t) (Bf t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    by_cases ht : t = 0
    · subst ht; simp
    · rw [hpΦ t ht]
  have e2 : (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)) =
      fun t => B.hsInner (A t) (conj t • dZbv Bf t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    by_cases ht : t = 0
    · subst ht; simp
    · rw [hpΨ t ht]
  have h1' := e1 ▸ h1
  have h2' := e2 ▸ h2
  rw [e1, e2]
  exact pLogAdjHS A Bf hAc hBc h0 h1' h2'

/- English proof (translation)
Unfold `pairAt`. Simplify using `only [← integral_div]`. Rewrite using `[integral_integral_swap h1]`. Use `conv_rhs => rw [integral_integral_swap h2]`. Rewrite using `[← integral_neg]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [h0.prod_left_ae, h1.prod_left_ae, h2.prod_left_ae] with x hx0 hx1 hx2`. Conclude with `site_p_adj_g X Φ Ψ l c hc (Matrix.of x) hx0 hx1 hx2`.
-/
theorem site_p_adj (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) [SFinite μ] (Φ Ψ : RadSp k r z z' π π')
    (l : Fin r) (c : Fin r → ℂ) (hc : c ∈ OmX r)
    (h0 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
      (Matrix.of q.2)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1) (Matrix.of q.2)) /
        ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ))
    (h1 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp))
      (Function.update c l q.1) (Matrix.of q.2)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
        (Matrix.of q.2)) / ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ))
    (h2 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
      (Matrix.of q.2)) ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1) (Matrix.of q.2)) /
        ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ)) :
    ∫ t : ℂ, pairAt μ (X.op l 0 Φ) Ψ (Function.update c l t) / ((‖t‖ ^ 2 : ℝ) : ℂ) =
      -∫ t : ℂ, pairAt μ Φ (X.op l 3 Ψ) (Function.update c l t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  unfold pairAt
  simp only [← integral_div]
  rw [integral_integral_swap h1]
  conv_rhs => rw [integral_integral_swap h2]
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [h0.prod_left_ae, h1.prod_left_ae, h2.prod_left_ae] with x hx0 hx1 hx2
  exact site_p_adj_g X Φ Ψ l c hc (Matrix.of x) hx0 hx1 hx2

end Formalism.FourierDecayAlt.P5.HerB

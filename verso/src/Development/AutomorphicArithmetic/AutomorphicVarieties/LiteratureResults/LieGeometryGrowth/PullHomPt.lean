import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbD
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullProdDer

noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Geo

section

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

private def tot (W : V → V) (z : V × ℝ) : V := flow W z.2 z.1

/- English proof (translation)
Establish `h : DifferentiableAt ℝ (fun z : V × ℝ => W z.1) (x, r)` using `DifferentiableAt.comp (x, r) (g := W) (f := Prod.fst) hW differentiableAt_fst`. Conclude with `differentiableAt_fst.add (differentiableAt_snd.smul h)`.
-/
private theorem tot_diff {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) :
    DifferentiableAt ℝ (tot W) (x, r) := by
  have h : DifferentiableAt ℝ (fun z : V × ℝ => W z.1) (x, r) :=
    DifferentiableAt.comp (x, r) (g := W) (f := Prod.fst) hW differentiableAt_fst
  exact differentiableAt_fst.add (differentiableAt_snd.smul h)

/- English proof (translation)
Unfold `tot flow`. Conclude with `contDiffAt_fst.add (contDiffAt_snd.smul (hW.comp (x, r) contDiffAt_fst))`.
-/
private theorem tot_smooth {W : V → V} {x : V} (hW : ContDiffAt ℝ ∞ W x) (r : ℝ) :
    ContDiffAt ℝ ∞ (tot W) (x, r) := by
  unfold tot flow
  exact contDiffAt_fst.add (contDiffAt_snd.smul (hW.comp (x, r) contDiffAt_fst))

/- English proof (translation)
Establish `h1` using `(tot_diff hW r).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x r)`. Establish `h2 : flow W r = tot W ∘ fun y => (y, r)` using `rfl`. Rewrite using `[h2, h1.fderiv]`. Both sides reduce to the same expression.
-/
private theorem tot_inl {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) (v : V) :
    fderiv ℝ (tot W) (x, r) (v, 0) = fderiv ℝ (flow W r) x v := by
  have h1 := (tot_diff hW r).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x r)
  have h2 : flow W r = tot W ∘ fun y => (y, r) := rfl
  rw [h2, h1.fderiv]
  rfl

/- English proof (translation)
Establish `h1` using `(tot_diff hW r).hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_const r x).prodMk (hasDerivAt_id r))`. Establish `h2 : HasDerivAt (tot W ∘ fun s => (x, s)) ((1 : ℝ) • W x) r` using `((hasDerivAt_id r).smul_const (W x)).const_add x`. Simplify using `using h1.unique h2`.
-/
private theorem tot_inr {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) :
    fderiv ℝ (tot W) (x, r) (0, 1) = W x := by
  have h1 := (tot_diff hW r).hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_const r x).prodMk (hasDerivAt_id r))
  have h2 : HasDerivAt (tot W ∘ fun s => (x, s)) ((1 : ℝ) • W x) r :=
    ((hasDerivAt_id r).smul_const (W x)).const_add x
  simpa using h1.unique h2

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply, pb_apply, Function.comp_apply, ContinuousLinearMap.inl_apply, tot_inl hW]`. Both sides reduce to the same expression.
-/
private theorem pb_tot {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) {q : ℕ}
    (w : V → V [⋀^Fin q]→L[ℝ] F) :
    (pb (tot W) w (x, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) = pb (flow W r) w x := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, pb_apply, Function.comp_apply,
    ContinuousLinearMap.inl_apply, tot_inl hW]
  rfl

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.curryLeft_apply_apply, pb_apply, hk_apply]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations.

Simplify using `[tot_inr hW]`. Simplify using `[tot_inl hW]`.
-/
private theorem hk_tot {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) {q : ℕ}
    (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) :
    ((pb (tot W) w (x, r)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) = hk W r w x := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    pb_apply, hk_apply]
  congr 1
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [tot_inr hW]
  · simp [tot_inl hW]

end

/- English proof (translation)
Introduce `V F _ _ _ _ _ _ W p t hW`. Establish `hd : DifferentiableAt ℝ W p` using `hW.differentiableAt (by simp)`. Establish `hfl : ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), (fun r => pb (flow W r) w p) = fun r => (pb (tot W) w (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)` using `fun q w => funext fun r => (pb_tot hd r w).symm`. Establish `key : ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), ContDiffAt ℝ ∞ w (flow W t p) → DifferentiableAt ℝ (pb (tot W) w) (p, t) ∧ extDeriv (pb (tot W) w) (p, t) = pb (tot W) (extDeriv w) (p, t)`. Introduce `q w hw`.

Take `⟨h1, h2⟩` from `pbD (V × ℝ) V F q (tot W) w (p, t) (tot_smooth hW t) hw`. Conclude with `⟨h1.differentiableAt (by simp), h2⟩`. Use `⟨fun w hw => ?_, fun q w hw => ?_⟩` and prove the remaining obligations. Take `⟨hD, hE⟩` from `key 0 w hw`. Rewrite using `[hfl, ← hk_tot hd t (extDeriv w), ← hE]`.

Conclude with `(prodDer V F p t).1 _ hD`. Take `⟨hD, hE⟩` from `key (q + 1) w hw`. Establish `hev : (fun y => ((pb (tot W) w (y, t)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) =ᶠ[𝓝 p] hk W t w`. Establish `h1 : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ 1 W y` using `(hW.of_le (by simp)).eventually (by simp)`. Use `filter_upwards [h1] with y hy`.

Conclude with `hk_tot (hy.differentiableAt (by simp)) t w`. Rewrite using `[hfl, ← hk_tot hd t (extDeriv w), ← hE, ← hev.extDeriv_eq]`. Conclude with `(prodDer V F p t).2 q _ hD`.
-/
theorem homPt : HomPt := by
  intro V F _ _ _ _ _ _ W p t hW
  have hd : DifferentiableAt ℝ W p := hW.differentiableAt (by simp)
  have hfl : ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), (fun r => pb (flow W r) w p) =
      fun r => (pb (tot W) w (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) :=
    fun q w => funext fun r => (pb_tot hd r w).symm
  have key : ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), ContDiffAt ℝ ∞ w (flow W t p) →
      DifferentiableAt ℝ (pb (tot W) w) (p, t) ∧
        extDeriv (pb (tot W) w) (p, t) = pb (tot W) (extDeriv w) (p, t) := by
    intro q w hw
    obtain ⟨h1, h2⟩ := pbD (V × ℝ) V F q (tot W) w (p, t) (tot_smooth hW t) hw
    exact ⟨h1.differentiableAt (by simp), h2⟩
  refine ⟨fun w hw => ?_, fun q w hw => ?_⟩
  · obtain ⟨hD, hE⟩ := key 0 w hw
    rw [hfl, ← hk_tot hd t (extDeriv w), ← hE]
    exact (prodDer V F p t).1 _ hD
  · obtain ⟨hD, hE⟩ := key (q + 1) w hw
    have hev : (fun y => ((pb (tot W) w (y, t)).curryLeft (0, 1)).compContinuousLinearMap
        (ContinuousLinearMap.inl ℝ V ℝ)) =ᶠ[𝓝 p] hk W t w := by
      have h1 : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ 1 W y := (hW.of_le (by simp)).eventually (by simp)
      filter_upwards [h1] with y hy
      exact hk_tot (hy.differentiableAt (by simp)) t w
    rw [hfl, ← hk_tot hd t (extDeriv w), ← hE, ← hev.extDeriv_eq]
    exact (prodDer V F p t).2 q _ hD

end UpperTheory.V.Lit.Geo

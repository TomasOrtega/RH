import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSimpleRootBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

/- English proof (translation)
Rewrite using `[Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _))]`. Simplify using `[Polynomial.coeff_map]`.
-/
theorem eval_map_eval_eq_sum {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (w : Fin d → ℂ) (s : ℂ) :
    (p.map (MvPolynomial.eval w)).eval s =
      ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval w (p.coeff i) * s ^ i := by
  rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _))]
  simp [Polynomial.coeff_map]

/- English proof (translation)
Establish `h : (fun v : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) = fun v => ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval v.1 (p.coeff i) * v.2 ^ i`. Use function extensionality and compare the values at `v`. Conclude with `eval_map_eval_eq_sum p v.1 v.2`. Rewrite using `[h]`. Use `Finset.analyticAt_fun_sum (𝕜 := ℂ) _ fun i _ => ?_` and prove the remaining obligations.

Use `AnalyticAt.mul ?_ (analyticAt_snd.pow i)` and prove the remaining obligations. Conclude with `(AnalyticOnNhd.eval_mvPolynomial (p.coeff i) v.1 trivial).comp analyticAt_fst`.
-/
theorem analyticAt_eval_map {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (v : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) v := by
  have h : (fun v : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) =
      fun v => ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval v.1 (p.coeff i) * v.2 ^ i := by
    funext v; exact eval_map_eval_eq_sum p v.1 v.2
  rw [h]
  refine Finset.analyticAt_fun_sum (𝕜 := ℂ) _ fun i _ => ?_
  refine AnalyticAt.mul ?_ (analyticAt_snd.pow i)
  exact (AnalyticOnNhd.eval_mvPolynomial (p.coeff i) v.1 trivial).comp analyticAt_fst

/- English proof (translation)
Introduce `d p y τ hroot hder`. Use `set F : (Fin d → ℂ) × ℂ → ℂ := fun v => (p.map (MvPolynomial.eval v.1)).eval v.2 with hFdef`. Establish `hcd : ContDiffAt ℂ 1 F (y, τ)` using `(analyticAt_eval_map p (y, τ)).contDiffAt`. Establish `hpart : fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ = (1 : ℂ →L[ℂ] ℂ).smulRight ((p.map (MvPolynomial.eval y)).derivative.eval τ)`. Establish `h1 : HasFDerivAt (fun s : ℂ => F (y, s)) (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ` using `((analyticAt_eval_map p (y, τ)).differentiableAt.hasFDerivAt).comp τ ((hasFDerivAt_const y τ).prodMk (hasFDerivAt_id τ))`.

Conclude with `h1.unique ((p.map (MvPolynomial.eval y)).hasDerivAt τ).hasFDerivAt`. Establish `hinv : (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible`. Rewrite using `[hpart]`. Use `⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using the standard rewrite rules. Use `set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef`. Establish `hψy : ψ y = τ` using `hcd.implicitFunction_apply_self one_ne_zero hinv`. Establish `hFu : F (y, τ) = 0` using `hroot`. Take `⟨U₀, hU₀, B₀, hB₀, hsub⟩` from `mem_nhds_prod_iff.mp (hcd.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv)`.

Take `⟨B, hBsub, hBo, hτB⟩` from `mem_nhds_iff.mp hB₀`. Establish `hψcd : ContDiffAt ℂ 1 ψ y` using `hcd.contDiffAt_implicitFunction one_ne_zero hinv`. Establish `hψB : ∀ᶠ w in 𝓝 y, ψ w ∈ B` using `hψcd.continuousAt.preimage_mem_nhds (by rw [hψy]; exact hBo.mem_nhds hτB)`. Take `⟨U, hUsub, hUo, hyU⟩` from `eventually_nhds_iff.mp (((show ∀ᶠ w in 𝓝 y, w ∈ U₀ from hU₀).and (hψcd.eventually (by simp))).and hψB)`. Use `⟨U, B, ψ, hUo, hyU, hBo, hτB, fun w hw => ?_, hψy, fun w hw => ⟨(hUsub w hw).2, ?_⟩⟩` and prove the remaining obligations.

Conclude with `((hUsub w hw).1.2.differentiableAt one_ne_zero).differentiableWithinAt`. Introduce `s hs`. Establish `h` using `hsub (Set.mk_mem_prod (hUsub w hw).1.1 (hBsub hs))`. Simplify using `only [Set.mem_ofPred_eq, hFu] at h`. Rewrite using `[Polynomial.IsRoot.def]`.

Conclude with `h.trans eq_comm`.
-/
theorem SimpleRootBranch.proof : SimpleRootBranch.Statement := by
  intro d p y τ hroot hder
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => (p.map (MvPolynomial.eval v.1)).eval v.2 with hFdef
  have hcd : ContDiffAt ℂ 1 F (y, τ) := (analyticAt_eval_map p (y, τ)).contDiffAt

  have hpart : fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight ((p.map (MvPolynomial.eval y)).derivative.eval τ) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (y, s))
        (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ :=
      ((analyticAt_eval_map p (y, τ)).differentiableAt.hasFDerivAt).comp τ
        ((hasFDerivAt_const y τ).prodMk (hasFDerivAt_id τ))
    exact h1.unique ((p.map (MvPolynomial.eval y)).hasDerivAt τ).hasFDerivAt
  have hinv : (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψy : ψ y = τ := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hFu : F (y, τ) = 0 := hroot
  obtain ⟨U₀, hU₀, B₀, hB₀, hsub⟩ :=
    mem_nhds_prod_iff.mp (hcd.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv)
  obtain ⟨B, hBsub, hBo, hτB⟩ := mem_nhds_iff.mp hB₀
  have hψcd : ContDiffAt ℂ 1 ψ y := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  have hψB : ∀ᶠ w in 𝓝 y, ψ w ∈ B :=
    hψcd.continuousAt.preimage_mem_nhds (by rw [hψy]; exact hBo.mem_nhds hτB)
  obtain ⟨U, hUsub, hUo, hyU⟩ := eventually_nhds_iff.mp
    (((show ∀ᶠ w in 𝓝 y, w ∈ U₀ from hU₀).and (hψcd.eventually (by simp))).and hψB)
  refine ⟨U, B, ψ, hUo, hyU, hBo, hτB, fun w hw => ?_, hψy, fun w hw => ⟨(hUsub w hw).2, ?_⟩⟩
  · exact ((hUsub w hw).1.2.differentiableAt one_ne_zero).differentiableWithinAt
  · intro s hs
    have h := hsub (Set.mk_mem_prod (hUsub w hw).1.1 (hBsub hs))
    simp only [Set.mem_ofPred_eq, hFu] at h
    rw [Polynomial.IsRoot.def]
    exact h.trans eq_comm

end

end GroundTheory.Heights₂.Heights.ComplexSets

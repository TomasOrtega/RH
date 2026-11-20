import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImplicitCurve
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Topology Metric

noncomputable section

namespace ImplicitCurve

/- English proof (translation)
Use `analyticOnNhd_pi_iff.2 fun j => ?_` and prove the remaining obligations. Establish `hj : DifferentiableOn ℂ (fun t => Φ t j) U` using `differentiableOn_pi.1 hΦ j`. Use `IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_` and prove the remaining obligations. Establish `hw : DifferentiableAt ℂ (fun t => Φ t j) (Function.update w i (w i))`. Rewrite using `[Function.update_eq_self]`.

Conclude with `(hj w hw).differentiableAt (hU.mem_nhds hw)`. Conclude with `hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt`.
-/
theorem analyticOnNhd_of_differentiableOn {m p : ℕ} {U : Set (Fin m → ℂ)}
    {Φ : (Fin m → ℂ) → Fin p → ℂ} (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U) :
    AnalyticOnNhd ℂ Φ U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => Φ t j) U := differentiableOn_pi.1 hΦ j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn
    fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => Φ t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]; exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

/- English proof (translation)
Introduce `n k γ R L s hγ hs hbij`. Use `set F : (Fin (k + 1) → ℂ) → Fin (k + 1) → ℂ := fun t => vecCons (t 0) (L *ᵥ γ t) with hF`. Establish `hFd : DifferentiableOn ℂ F (ball 0 R)`. Use `differentiableOn_pi.2 fun i => Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify `(differentiableOn_pi.1 (differentiableOn_id (s := ball (0 : Fin (k + 1) → ℂ) R)) 0)` using `[hF]`.

Simplify using `only [hF, cons_val_succ, mulVec, dotProduct]`. Conclude with `DifferentiableOn.fun_sum fun l _ => (differentiableOn_pi.1 hγ l).const_mul _`. Establish `hFa` using `analyticOnNhd_of_differentiableOn isOpen_ball hFd`. Use `set e := (LinearEquiv.ofBijective (fderiv ℂ F s : (Fin (k + 1) → ℂ) →ₗ[ℂ] Fin (k + 1) → ℂ) hbij).toContinuousLinearEquiv`. Establish `he : (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) = fderiv ℂ F s` using `by ext1 x; rfl`.

Establish `hst : HasStrictFDerivAt F (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) s`. Rewrite using `[he]`. Conclude with `(hFa s hs).hasStrictFDerivAt`. Establish `hV : ∀ᶠ t in 𝓝 s, (t ∈ ball (0 : Fin (k + 1) → ℂ) R ∧ fderiv ℂ F t ∈ Set.range ((↑) : ((Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ)) → _)) ∧ t ∈ (hst.toOpenPartialHomeomorph F).source` using `(Filter.Eventually.and (isOpen_ball.mem_nhds hs) ((hFa s hs).fderiv.continuousAt.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, he⟩))).and ((hst.toOpenPartialHomeomorph F).open_source.mem_nhds hst.mem_toOpenPartialHomeomorph_source)`. Take `⟨ε, hε, hεV⟩` from `Metric.mem_nhds_iff.1 hV`.

Use `set Ψ := (hst.toOpenPartialHomeomorph F).restrOpen (ball s ε) isOpen_ball`. Establish `hΨs : Ψ.source = (hst.toOpenPartialHomeomorph F).source ∩ ball s ε` using `OpenPartialHomeomorph.restrOpen_source _ _ _`. Establish `hsΨ : s ∈ Ψ.source` using `hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, mem_ball_self hε⟩`. Establish `hsrc : ∀ t ∈ Ψ.source, t ∈ ball 0 R ∧ ∃ e' : (Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ), HasFDerivAt Ψ (e' : _ →L[ℂ] _) t`. Introduce `t ht`.

Take `⟨⟨htR, e', he'⟩, -⟩` from `hεV (hΨs ▸ ht).2`. Use `⟨htR, e', ?_⟩` and prove the remaining obligations. Rewrite using `[he']`. Conclude with `(hFa t htR).differentiableAt.hasFDerivAt`. Take `⟨r, hr, hrT⟩` from `Metric.isOpen_iff.1 Ψ.open_target (F s) (Ψ.map_source hsΨ)`.

Use `set p : (Fin 1 → ℂ) → Fin (k + 1) → ℂ := fun τ => vecCons (s 0 + τ 0) (L *ᵥ γ s) with hp`. Establish `hpT : ∀ τ ∈ ball (0 : Fin 1 → ℂ) r, p τ ∈ Ψ.target`. Introduce `τ hτ`. Use `hrT ((dist_pi_lt_iff hr).2 fun i => Fin.cases ?_ (fun j => ?_) i)` and prove the remaining obligations. Simplify `(norm_le_pi_norm τ 0).trans_lt (mem_ball_zero_iff.1 hτ)` using `[hp, hF, dist_eq_norm]`.

Simplify `hr` using `[hp, hF]`. Use `⟨r, hr, fun τ => Ψ.symm (p τ), fun τ hτ => ?_, ?_, fun τ hτ => ?_, ?_⟩` and prove the remaining obligations. Establish `hpd : Differentiable ℂ p` using `differentiable_pi.2 fun i => Fin.cases (by simpa [hp] using (differentiable_const (s 0)).add (differentiable_pi.1 differentiable_id 0)) (fun j => by simp [hp]) i`. Take `⟨-, e', he'⟩` from `hsrc _ (Ψ.map_target (hpT τ hτ))`. Conclude with `((Ψ.hasFDerivAt_symm (hpT τ hτ) he').differentiableAt.comp τ (hpd τ)).differentiableWithinAt`.

Establish `h0 : p 0 = F s` using `by simp [hp, hF] show Ψ.symm (p 0) = s`. Rewrite using `[h0]`. Conclude with `Ψ.left_inv hsΨ`. Establish `h2 : F (Ψ.symm (p τ)) = p τ` using `Ψ.right_inv (hpT τ hτ)`. Use `⟨(hsrc _ (Ψ.map_target (hpT τ hτ))).1, ?_, ?_⟩` and prove the remaining obligations.

Simplify `congrFun h2 0` using `[hF, hp]`. Simplify `congrArg Fin.tail h2` using `[hF, hp]`. Use `⟨Ψ.source ∩ {t | ‖t 0 - s 0‖ < r}, Filter.inter_mem (Ψ.open_source.mem_nhds hsΨ) ((isOpen_lt ((continuous_apply 0).sub continuous_const).norm continuous_const).mem_nhds (by simpa using hr)), ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨ht, htr⟩ hL`. Use `⟨fun _ => t 0 - s 0, by simpa [pi_norm_const] using htr, ?_⟩` and prove the remaining obligations.

Establish `hpt : p (fun _ => t 0 - s 0) = F t` using `by simp [hp, hF, hL]`. Simplify using `only`. Rewrite using `[hpt]`. Conclude with `Ψ.left_inv ht`.
-/
theorem proof : ImplicitCurve.Statement := by
  intro n k γ R L s hγ hs hbij
  set F : (Fin (k + 1) → ℂ) → Fin (k + 1) → ℂ := fun t => vecCons (t 0) (L *ᵥ γ t) with hF
  have hFd : DifferentiableOn ℂ F (ball 0 R) := by
    refine differentiableOn_pi.2 fun i => Fin.cases ?_ (fun j => ?_) i
    · simpa [hF] using (differentiableOn_pi.1 (differentiableOn_id (s := ball (0 : Fin (k + 1) → ℂ) R)) 0)
    · simp only [hF, cons_val_succ, mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun l _ => (differentiableOn_pi.1 hγ l).const_mul _
  have hFa := analyticOnNhd_of_differentiableOn isOpen_ball hFd
  set e := (LinearEquiv.ofBijective
    (fderiv ℂ F s : (Fin (k + 1) → ℂ) →ₗ[ℂ] Fin (k + 1) → ℂ) hbij).toContinuousLinearEquiv
  have he : (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) = fderiv ℂ F s := by ext1 x; rfl
  have hst : HasStrictFDerivAt F (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) s := by
    rw [he]; exact (hFa s hs).hasStrictFDerivAt
  have hV : ∀ᶠ t in 𝓝 s, (t ∈ ball (0 : Fin (k + 1) → ℂ) R ∧ fderiv ℂ F t ∈
      Set.range ((↑) : ((Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ)) → _)) ∧
      t ∈ (hst.toOpenPartialHomeomorph F).source :=
    (Filter.Eventually.and (isOpen_ball.mem_nhds hs) ((hFa s hs).fderiv.continuousAt.preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, he⟩))).and
      ((hst.toOpenPartialHomeomorph F).open_source.mem_nhds hst.mem_toOpenPartialHomeomorph_source)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  set Ψ := (hst.toOpenPartialHomeomorph F).restrOpen (ball s ε) isOpen_ball
  have hΨs : Ψ.source = (hst.toOpenPartialHomeomorph F).source ∩ ball s ε :=
    OpenPartialHomeomorph.restrOpen_source _ _ _
  have hsΨ : s ∈ Ψ.source := hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, mem_ball_self hε⟩
  have hsrc : ∀ t ∈ Ψ.source, t ∈ ball 0 R ∧
      ∃ e' : (Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ), HasFDerivAt Ψ (e' : _ →L[ℂ] _) t := by
    intro t ht
    obtain ⟨⟨htR, e', he'⟩, -⟩ := hεV (hΨs ▸ ht).2
    refine ⟨htR, e', ?_⟩
    rw [he']; exact (hFa t htR).differentiableAt.hasFDerivAt
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 Ψ.open_target (F s) (Ψ.map_source hsΨ)
  set p : (Fin 1 → ℂ) → Fin (k + 1) → ℂ := fun τ => vecCons (s 0 + τ 0) (L *ᵥ γ s) with hp
  have hpT : ∀ τ ∈ ball (0 : Fin 1 → ℂ) r, p τ ∈ Ψ.target := by
    intro τ hτ
    refine hrT ((dist_pi_lt_iff hr).2 fun i => Fin.cases ?_ (fun j => ?_) i)
    · simpa [hp, hF, dist_eq_norm] using (norm_le_pi_norm τ 0).trans_lt (mem_ball_zero_iff.1 hτ)
    · simpa [hp, hF] using hr
  refine ⟨r, hr, fun τ => Ψ.symm (p τ), fun τ hτ => ?_, ?_, fun τ hτ => ?_, ?_⟩
  · have hpd : Differentiable ℂ p := differentiable_pi.2 fun i => Fin.cases
      (by simpa [hp] using (differentiable_const (s 0)).add (differentiable_pi.1 differentiable_id 0))
      (fun j => by simp [hp]) i
    obtain ⟨-, e', he'⟩ := hsrc _ (Ψ.map_target (hpT τ hτ))
    exact ((Ψ.hasFDerivAt_symm (hpT τ hτ) he').differentiableAt.comp τ
      (hpd τ)).differentiableWithinAt
  · have h0 : p 0 = F s := by simp [hp, hF]
    show Ψ.symm (p 0) = s
    rw [h0]; exact Ψ.left_inv hsΨ
  · have h2 : F (Ψ.symm (p τ)) = p τ := Ψ.right_inv (hpT τ hτ)
    refine ⟨(hsrc _ (Ψ.map_target (hpT τ hτ))).1, ?_, ?_⟩
    · simpa [hF, hp] using congrFun h2 0
    · simpa [hF, hp] using congrArg Fin.tail h2
  · refine ⟨Ψ.source ∩ {t | ‖t 0 - s 0‖ < r}, Filter.inter_mem (Ψ.open_source.mem_nhds hsΨ)
      ((isOpen_lt ((continuous_apply 0).sub continuous_const).norm continuous_const).mem_nhds
        (by simpa using hr)), ?_⟩
    rintro t ⟨ht, htr⟩ hL
    refine ⟨fun _ => t 0 - s 0, by simpa [pi_norm_const] using htr, ?_⟩
    have hpt : p (fun _ => t 0 - s 0) = F t := by simp [hp, hF, hL]
    dsimp only
    rw [hpt]; exact Ψ.left_inv ht

end ImplicitCurve

end

end GroundTheory.Heights₂.Heights

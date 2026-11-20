import Mathlib

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

/- English proof (translation)
Establish `hTT : ∀ f, T (T f) = T f` using `fun f => by`. Use `hT.isIdempotentElem` as an intermediate fact. Conclude with `congrArg (fun S : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν => S f) this`. Establish `hsym : ∀ f g : Lp ℂ 2 ν, ⟪T f, g⟫_ℂ = ⟪f, T g⟫_ℂ` using `fun f g => by`. Establish `h` using `hT.isSelfAdjoint`.

Rewrite `h` using `[ContinuousLinearMap.isSelfAdjoint_iff']`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_right, h]`. Use `set d : ℕ → Lp ℂ 2 ν := denseSeq (Lp ℂ 2 ν) with hd`. Establish `h1 : ∀ᵐ x ∂ν, ∀ n, ⟪κ x, d n - T (d n)⟫_ℂ = 0`. Rewrite using `[ae_all_iff]`.

Introduce `n`. Establish `hz : T (d n - T (d n)) = 0` using `by rw [map_sub, hTT, sub_self]`. Establish `h0 : ((T (d n - T (d n)) : Lp ℂ 2 ν) : Y → ℂ) =ᵐ[ν] 0`. Rewrite using `[hz]`. Conclude with `Lp.coeFn_zero _ _ _`.

Use `filter_upwards [hκ (d n - T (d n)), h0] with x a1 a2`. Rewrite using `[← a1, a2]`. Both sides reduce to the same expression. Establish `h2 : ∀ᵐ x ∂ν, ∀ w, (((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) : Y → ℂ) x = ⟪κ x, ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν)⟫_ℂ`. Rewrite using `[ae_all_iff]`.

Introduce `w`. Take `⟨u, hu⟩` from `(F w).2`. Establish `hfix : T ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) = ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν)`. Rewrite using `[← hu]`. Conclude with `hTT u`.

Use `filter_upwards [hκ ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν)] with x a1`. Rewrite using `[← a1, hfix]`. Use `filter_upwards [h1, h2] with x a1 a2`. Establish `hall : ∀ f : Lp ℂ 2 ν, ⟪κ x, f - T f⟫_ℂ = 0`. Introduce `f`.

Establish `hc : Continuous fun f : Lp ℂ 2 ν => ⟪κ x, f - T f⟫_ℂ` using `by fun_prop`. Establish `hcl : IsClosed {f : Lp ℂ 2 ν | ⟪κ x, f - T f⟫_ℂ = 0}` using `isClosed_eq hc continuous_const`. Conclude with `(denseRange_denseSeq (Lp ℂ 2 ν)).induction_on (p := fun f => ⟪κ x, f - T f⟫_ℂ = 0) f hcl a1`. Establish `hfix : T (κ x) = κ x`. Establish `e1 : ⟪κ x - T (κ x), κ x - T (κ x)⟫_ℂ = 0`.

Rewrite using `[inner_sub_left, hall, hsym, map_sub, hTT, sub_self, inner_zero_right, sub_zero]`. Use `inner_self_eq_zero.1 e1` as an intermediate fact. Conclude with `(sub_eq_zero.1 this).symm`. Use `set v : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν) := ⟨κ x, ⟨κ x, hfix⟩⟩ with hv`. Establish `hp` using `F.sum_sq_norm_inner_right v`.

Establish `hn : ‖v‖ = ‖κ x‖` using `rfl`. Rewrite using `[← hn, ← hp]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[a2 w]`. Establish `: ⟪F w, v⟫_ℂ = ⟪((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν), κ x⟫_ℂ` using `rfl`.

Rewrite using `[this, ← norm_inner_symm]`.
-/
theorem rrk_diag {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SeparableSpace (Lp ℂ 2 ν)]
    (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hT : IsStarProjection T) {N : ℕ}
    (F : OrthonormalBasis (Fin N) ℂ (LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)))
    (κ : Y → Lp ℂ 2 ν) (hκ : ∀ f : Lp ℂ 2 ν, ∀ᵐ x ∂ν, (T f : Y → ℂ) x = ⟪κ x, f⟫_ℂ) :
    ∀ᵐ x ∂ν, ‖κ x‖ ^ 2 = ∑ w, ‖(((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) : Y → ℂ) x‖ ^ 2 := by
  have hTT : ∀ f, T (T f) = T f := fun f => by
    have := hT.isIdempotentElem
    exact congrArg (fun S : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν => S f) this
  have hsym : ∀ f g : Lp ℂ 2 ν, ⟪T f, g⟫_ℂ = ⟪f, T g⟫_ℂ := fun f g => by
    have h := hT.isSelfAdjoint
    rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h
    rw [← ContinuousLinearMap.adjoint_inner_right, h]
  set d : ℕ → Lp ℂ 2 ν := denseSeq (Lp ℂ 2 ν) with hd
  have h1 : ∀ᵐ x ∂ν, ∀ n, ⟪κ x, d n - T (d n)⟫_ℂ = 0 := by
    rw [ae_all_iff]
    intro n
    have hz : T (d n - T (d n)) = 0 := by rw [map_sub, hTT, sub_self]
    have h0 : ((T (d n - T (d n)) : Lp ℂ 2 ν) : Y → ℂ) =ᵐ[ν] 0 := by
      rw [hz]; exact Lp.coeFn_zero _ _ _
    filter_upwards [hκ (d n - T (d n)), h0] with x a1 a2
    rw [← a1, a2]; rfl
  have h2 : ∀ᵐ x ∂ν, ∀ w, (((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) : Y → ℂ) x =
      ⟪κ x, ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν)⟫_ℂ := by
    rw [ae_all_iff]
    intro w
    obtain ⟨u, hu⟩ := (F w).2
    have hfix : T ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) =
        ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) := by
      rw [← hu]; exact hTT u
    filter_upwards [hκ ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν)] with x a1
    rw [← a1, hfix]
  filter_upwards [h1, h2] with x a1 a2
  have hall : ∀ f : Lp ℂ 2 ν, ⟪κ x, f - T f⟫_ℂ = 0 := by
    intro f
    have hc : Continuous fun f : Lp ℂ 2 ν => ⟪κ x, f - T f⟫_ℂ := by fun_prop
    have hcl : IsClosed {f : Lp ℂ 2 ν | ⟪κ x, f - T f⟫_ℂ = 0} := isClosed_eq hc continuous_const
    exact (denseRange_denseSeq (Lp ℂ 2 ν)).induction_on (p := fun f => ⟪κ x, f - T f⟫_ℂ = 0) f hcl a1
  have hfix : T (κ x) = κ x := by
    have e1 : ⟪κ x - T (κ x), κ x - T (κ x)⟫_ℂ = 0 := by
      rw [inner_sub_left, hall, hsym, map_sub, hTT, sub_self, inner_zero_right, sub_zero]
    have := inner_self_eq_zero.1 e1
    exact (sub_eq_zero.1 this).symm
  set v : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν) := ⟨κ x, ⟨κ x, hfix⟩⟩ with hv
  have hp := F.sum_sq_norm_inner_right v
  have hn : ‖v‖ = ‖κ x‖ := rfl
  rw [← hn, ← hp]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [a2 w]
  have : ⟪F w, v⟫_ℂ = ⟪((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν), κ x⟫_ℂ := rfl
  rw [this, ← norm_inner_symm]

end Formalism.MainNotions.LeviCoordinates

end

import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix Classical
open NumberField

/- English proof (translation)
Take `⟨y, hy⟩ : ∃ y : mixedEmbedding.mixedSpace F, x * y * x = x` from `⟨(fun w => (x.1 w)⁻¹, fun w => (x.2 w)⁻¹), Prod.ext (funext fun w => mul_inv_mul_cancel (x.1 w)) (funext fun w => mul_inv_mul_cancel (x.2 w))⟩`. Use `⟨y, fun h => hx ?_⟩` and prove the remaining obligations. Establish `hi : IsIdempotentElem (LinearMap.mulLeft ℝ (x * y))`. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x * y * (x * y * z) = x * y * z`.

Rewrite using `[← mul_assoc, ← mul_assoc, hy]`. Establish `ht` using `(LinearMap.IsIdempotentElem.isProj_range _ hi).trace`. Establish `h0 : LinearMap.trace ℝ _ (LinearMap.mulLeft ℝ (x * y)) = 0` using `h`. Rewrite `ht` using `[h0]`. Establish `hr : LinearMap.range (LinearMap.mulLeft ℝ (x * y)) = ⊥` using `Submodule.finrank_eq_zero.1 (by exact_mod_cast ht.symm)`.

Establish `: x * y * x = 0` using `LinearMap.congr_fun (LinearMap.range_eq_bot.1 hr) x`. Rewrite `this` using `[hy]`. Then use the resulting hypothesis.
-/
theorem exists_trace_ne {F : Type} [Field F] [NumberField F] (x : mixedEmbedding.mixedSpace F) (hx : x ≠ 0) :
    ∃ y, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * y) ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y : mixedEmbedding.mixedSpace F, x * y * x = x :=
    ⟨(fun w => (x.1 w)⁻¹, fun w => (x.2 w)⁻¹), Prod.ext (funext fun w => mul_inv_mul_cancel (x.1 w))
      (funext fun w => mul_inv_mul_cancel (x.2 w))⟩
  refine ⟨y, fun h => hx ?_⟩
  have hi : IsIdempotentElem (LinearMap.mulLeft ℝ (x * y)) := by
    refine LinearMap.ext fun z => ?_
    change x * y * (x * y * z) = x * y * z
    rw [← mul_assoc, ← mul_assoc, hy]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  have h0 : LinearMap.trace ℝ _ (LinearMap.mulLeft ℝ (x * y)) = 0 := h
  rw [h0] at ht
  have hr : LinearMap.range (LinearMap.mulLeft ℝ (x * y)) = ⊥ :=
    Submodule.finrank_eq_zero.1 (by exact_mod_cast ht.symm)
  have : x * y * x = 0 := LinearMap.congr_fun (LinearMap.range_eq_bot.1 hr) x
  rwa [hy] at this

/- English proof (translation)
Introduce `F _ _ κ _`. Set `B : V F κ →ₗ[ℝ] V F κ →ₗ[ℝ] ℝ` to `LinearMap.mk₂ ℝ (fun x b => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ b)) (fun x x' b => by rw [add_dotProduct, map_add]) (fun c x b => by rw [smul_dotProduct, map_smul]) (fun x b b' => by rw [dotProduct_add, map_add]) (fun c x b => by rw [dotProduct_smul, map_smul])`. Set `A : V F κ →ₗ[ℝ] V F κ →L[ℝ] ℝ` to `(LinearMap.toContinuousLinearMap : (V F κ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B`. Establish `hA : LinearMap.ker A = ⊥`. Use `LinearMap.ker_eq_bot'.2 fun x hx => funext fun i => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hi`. Take `⟨y, hy⟩` from `exists_trace_ne (x i) hi`. Establish `: Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ Pi.single i y) = 0` using `congrArg (fun T : V F κ →L[ℝ] ℝ => T (Pi.single i y)) hx`. Rewrite `this` using `[dotProduct_single]`. Conclude with `hy this`.

Take `⟨K, -, hK⟩` from `A.exists_antilipschitzWith hA`. Use `⟨2 * K, by positivity, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖x‖ ≤ K * ‖A x‖` using `ZeroHomClass.bound_of_antilipschitz A hK x`. Distinguish the cases in `h0 : ‖A x‖ = 0`. Use `⟨0, by simp, ?_⟩` and prove the remaining obligations.

Rewrite `h1` using `[h0, mul_zero]`. Conclude with `h1.trans (by positivity)`. Establish `hp : 0 < ‖A x‖` using `(norm_nonneg _).lt_of_ne' h0`. Take `⟨b, hb, hb'⟩` from `(A x).exists_lt_apply_of_lt_opNorm (r := ‖A x‖ / 2) (by linarith)`. Use `⟨b, hb.le, h1.trans ?_⟩` and prove the remaining obligations.

Establish `h2 : ‖A x‖ / 2 < |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ b)|` using `hb'`. Establish `h3 : (0 : ℝ) ≤ K` using `K.2`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem trBd : TrBd := by
  intro F _ _ κ _
  let B : V F κ →ₗ[ℝ] V F κ →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun x b => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ b))
    (fun x x' b => by rw [add_dotProduct, map_add]) (fun c x b => by rw [smul_dotProduct, map_smul])
    (fun x b b' => by rw [dotProduct_add, map_add]) (fun c x b => by rw [dotProduct_smul, map_smul])
  let A : V F κ →ₗ[ℝ] V F κ →L[ℝ] ℝ := (LinearMap.toContinuousLinearMap : (V F κ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B
  have hA : LinearMap.ker A = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => funext fun i => ?_
    by_contra hi
    obtain ⟨y, hy⟩ := exists_trace_ne (x i) hi
    have : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ Pi.single i y) = 0 :=
      congrArg (fun T : V F κ →L[ℝ] ℝ => T (Pi.single i y)) hx
    rw [dotProduct_single] at this
    exact hy this
  obtain ⟨K, -, hK⟩ := A.exists_antilipschitzWith hA
  refine ⟨2 * K, by positivity, fun x => ?_⟩
  have h1 : ‖x‖ ≤ K * ‖A x‖ := ZeroHomClass.bound_of_antilipschitz A hK x
  by_cases h0 : ‖A x‖ = 0
  · refine ⟨0, by simp, ?_⟩
    rw [h0, mul_zero] at h1
    exact h1.trans (by positivity)
  · have hp : 0 < ‖A x‖ := (norm_nonneg _).lt_of_ne' h0
    obtain ⟨b, hb, hb'⟩ := (A x).exists_lt_apply_of_lt_opNorm (r := ‖A x‖ / 2) (by linarith)
    refine ⟨b, hb.le, h1.trans ?_⟩
    have h2 : ‖A x‖ / 2 < |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ b)| := hb'
    have h3 : (0 : ℝ) ≤ K := K.2
    nlinarith

end PositivityTheory.ThKF0.Grow

import Mathlib

namespace GlobalTheory.CompanionTheory.Div

/- English proof (translation)
Introduce `A O _ _ θ hθ ξ hξ M D L _ _ _ _ _ _ r q hr hker`. Establish `hq : ∀ m m', r m = r m' → q m = q m'`. Introduce `m m' h`. Take `⟨n, hn⟩` from `(hker (m - m')).1 (by rw [map_sub, h, sub_self])`. Establish `h0 : q (m - m') = 0` using `by rw [hn, map_smulₛₗ, hξ, zero_smul]`.

Rewrite `h0` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Set `s` to `Function.surjInv hr`. Establish `hs : ∀ d, r (s d) = d` using `Function.surjInv_eq hr`. Use `⟨{ toFun := fun d => q (s d), map_add' := ?_, map_smul' := ?_ }, fun m => hq _ _ (hs _)⟩` and prove the remaining obligations. Introduce `d d'`.

Rewrite using `[← map_add]`. Conclude with `hq _ _ (by rw [map_add, hs, hs, hs])`. Introduce `o d`. Take `⟨a, rfl⟩` from `hθ o`. Simplify using `only [RingHom.id_apply]`.

Rewrite using `[← map_smulₛₗ]`. Conclude with `hq _ _ (by rw [map_smulₛₗ, hs, hs])`.
-/
theorem semilinear_factors_through_reduction :
    ∀ (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O), Function.Surjective θ →
      ∀ (ξ : A), θ ξ = 0 →
      ∀ (M D L : Type) [AddCommGroup M] [Module A M] [AddCommGroup D] [Module O D]
        [AddCommGroup L] [Module O L] (r : M →ₛₗ[θ] D) (q : M →ₛₗ[θ] L),
        Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = ξ • n) →
        ∃ π : D →ₗ[O] L, ∀ m, π (r m) = q m := by
  intro A O _ _ θ hθ ξ hξ M D L _ _ _ _ _ _ r q hr hker
  have hq : ∀ m m', r m = r m' → q m = q m' := by
    intro m m' h
    obtain ⟨n, hn⟩ := (hker (m - m')).1 (by rw [map_sub, h, sub_self])
    have h0 : q (m - m') = 0 := by rw [hn, map_smulₛₗ, hξ, zero_smul]
    rwa [map_sub, sub_eq_zero] at h0
  let s := Function.surjInv hr
  have hs : ∀ d, r (s d) = d := Function.surjInv_eq hr
  refine ⟨{ toFun := fun d => q (s d), map_add' := ?_, map_smul' := ?_ }, fun m => hq _ _ (hs _)⟩
  · intro d d'
    rw [← map_add]
    exact hq _ _ (by rw [map_add, hs, hs, hs])
  · intro o d
    obtain ⟨a, rfl⟩ := hθ o
    simp only [RingHom.id_apply]
    rw [← map_smulₛₗ]
    exact hq _ _ (by rw [map_smulₛₗ, hs, hs])

end GlobalTheory.CompanionTheory.Div

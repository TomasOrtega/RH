import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Introduce `k Γ M _ _ _ _ _ F ρ hρ hN x hx`. Unfold `Frame.framedTwoCoboundaries at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, y, e, h1, h2, h3, h4, h5⟩` from `hx`.

Use `⟨fun s => h s - (ρ s (y F.v0) - y F.v0), fun v => y v - y F.v0, h1.sub ((hρ _).sub (IsLocallyConstant.const _)), sub_self _, ?_, fun v s => ?_, fun q n hn => ?_⟩` and prove the remaining obligations. Rewrite using `[h3]`. Use function extensionality and compare the values at `p`. Simplify using `only [dOne, map_sub, map_mul, Module.End.mul_apply]`. Normalize the expressions using the abelian group laws.

Rewrite using `[h4]`. Simplify using `only [map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[h5, (h2 q).2.2 n hn]`. Simplify using `only [hN q n hn, sub_self]`.

Consider the case `zero`. Use `⟨0, 0, IsLocallyConstant.const 0, rfl, ?_, by simp, by simp⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Simplify using `[dOne]`. Consider the case `add x x' _ _ ih ih'`.

Take `⟨h, y, a1, a2, a3, a4, a5⟩` from `ih`. Take `⟨h', y', b1, b2, b3, b4, b5⟩` from `ih'`. Use `⟨h + h', y + y', a1.add b1, by simp [a2, b2], ?_, fun v s => ?_, fun q n hn => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Simplify using `only [Prod.fst_add, Pi.add_apply, a3, b3, dOne, map_add]`.

Normalize the expressions using the abelian group laws. Simplify using `only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a4, b4, map_add]`. Normalize the expressions using the abelian group laws. Simplify using `only [Prod.snd_add, Pi.add_apply, a5 q n hn, b5 q n hn]`. Consider the case `smul c x _ ih`.

Take `⟨h, y, a1, a2, a3, a4, a5⟩` from `ih`. Use `⟨c • h, c • y, a1.comp (c • ·), by simp [a2], ?_, fun v s => ?_, fun q n hn => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Simplify using `[a3, dOne, smul_sub]`. Simplify using `[a4, smul_sub]`.

Simplify using `[a5 q n hn]`.
-/
theorem UpperTheory.V.Alg.cocycle_normal_form :
    ∀ (k Γ M : Type) [CommRing k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M] (F : Frame Γ) (ρ : Representation k Γ M), (∀ m : M, IsLocallyConstant fun s => ρ s m) → (∀ q, ∀ n ∈ F.N q, ∀ m, ρ (F.ψ q n) m = m) →
          ∀ x ∈ F.framedTwoCoboundaries ρ, ∃ (h : Γ → M) (y : F.T → M), IsLocallyConstant h ∧ y F.v0 = 0 ∧ x.1 = dOne ρ h ∧ (∀ v s, x.2.1 v s = h (F.φ v s) - (ρ (F.φ v s) (y v) - y v)) ∧ ∀ q, ∀ n ∈ F.N q, x.2.2 q n = h (F.ψ q n) := by
  intro k Γ M _ _ _ _ _ F ρ hρ hN x hx
  unfold Frame.framedTwoCoboundaries at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, y, e, h1, h2, h3, h4, h5⟩ := hx
    refine ⟨fun s => h s - (ρ s (y F.v0) - y F.v0), fun v => y v - y F.v0,
      h1.sub ((hρ _).sub (IsLocallyConstant.const _)), sub_self _, ?_, fun v s => ?_, fun q n hn => ?_⟩
    · rw [h3]
      funext p
      simp only [dOne, map_sub, map_mul, Module.End.mul_apply]
      abel
    · rw [h4]
      simp only [map_sub]
      abel
    · rw [h5, (h2 q).2.2 n hn]
      simp only [hN q n hn, sub_self]
  | zero =>
    refine ⟨0, 0, IsLocallyConstant.const 0, rfl, ?_, by simp, by simp⟩
    funext p
    simp [dOne]
  | add x x' _ _ ih ih' =>
    obtain ⟨h, y, a1, a2, a3, a4, a5⟩ := ih
    obtain ⟨h', y', b1, b2, b3, b4, b5⟩ := ih'
    refine ⟨h + h', y + y', a1.add b1, by simp [a2, b2], ?_, fun v s => ?_, fun q n hn => ?_⟩
    · funext p
      simp only [Prod.fst_add, Pi.add_apply, a3, b3, dOne, map_add]
      abel
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a4, b4, map_add]
      abel
    · simp only [Prod.snd_add, Pi.add_apply, a5 q n hn, b5 q n hn]
  | smul c x _ ih =>
    obtain ⟨h, y, a1, a2, a3, a4, a5⟩ := ih
    refine ⟨c • h, c • y, a1.comp (c • ·), by simp [a2], ?_, fun v s => ?_, fun q n hn => ?_⟩
    · funext p
      simp [a3, dOne, smul_sub]
    · simp [a4, smul_sub]
    · simp [a5 q n hn]

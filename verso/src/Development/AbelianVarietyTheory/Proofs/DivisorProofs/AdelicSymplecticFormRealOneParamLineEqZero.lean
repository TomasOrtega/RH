import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaTransform

/- English proof (translation)
Introduce `F _ _ N hF M hM t s`. Set `φ : InfinitePlace F → AF F →+* ℝ` to `fun w => (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)`. Establish `hφ : ∀ w (x : AF F), φ w x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w) (x.1 w)` using `fun _ _ => rfl`. Establish `hcont : ∀ w (g : ℝ → AF F), Continuous g → Continuous fun r => φ w (g r)`. Introduce `w g hg`.

Simplify using `only [hφ]`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal w)).continuous.comp ((continuous_apply w).comp (continuous_fst.comp hg))`. Establish `lin : ∀ (p : VA F N →+ AF F), Continuous p → ∀ w r, φ w (p (M r)) = r * φ w (p (M 1))`. Introduce `p hp w r`. Set `f : ℝ →+ ℝ` to `((φ w).toAddMonoidHom.comp p).comp M`.

Establish `hc : Continuous f` using `hcont w (fun r => p (M r)) (hp.comp hM.1)`. Use `map_real_smul f hc r 1` as an intermediate fact. Simplify `this` using `[f]`. Establish `p1 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp (AddMonoidHom.fst _ _) : VA F N →+ AF F)` using `fun l => (continuous_apply l).comp continuous_fst`. Establish `p2 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp (AddMonoidHom.snd _ _) : VA F N →+ AF F)` using `fun l => (continuous_apply l).comp continuous_snd`.

Establish `k1 : ∀ l w r, φ w ((M r).1 l) = r * φ w ((M 1).1 l)` using `fun l w r => lin _ (p1 l) w r`. Establish `k2 : ∀ l w r, φ w ((M r).2 l) = r * φ w ((M 1).2 l)` using `fun l w r => lin _ (p2 l) w r`. Establish `hfst : fstA F (symV (M t) (M s)) = 0`. Use function extensionality and compare the values at `w`. Apply `(InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).injective` to reduce the goal to its premises.

Establish `h : φ w (symV (M t) (M s)) = 0`. Simplify using `only [symV, dotProduct, map_sub, map_sum, map_mul]`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Rewrite using `[k1 l w t, k1 l w s, k2 l w t, k2 l w s]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h.trans (map_zero _).symm`. Establish `h0 : ∀ r l, sndA F ((M r).1 l) = 0 ∧ sndA F ((M r).2 l) = 0` using `fun r l => ⟨congrFun (hM.2 r).1 l, congrFun (hM.2 r).2 l⟩`. Establish `hsnd : sndA F (symV (M t) (M s)) = 0`. Simplify using `only [symV, dotProduct, map_sub, map_sum, map_mul, (h0 _ _).1, (h0 _ _).2, zero_mul, Finset.sum_const_zero, sub_zero]`.

Conclude with `Prod.ext hfst hsnd`.
-/
theorem symV_realLine_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ t s : ℝ, symV (M t) (M s) = 0 := by
  intro F _ _ N hF M hM t s

  let φ : InfinitePlace F → AF F →+* ℝ := fun w =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).comp
      ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)
  have hφ : ∀ w (x : AF F), φ w x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)
      (x.1 w) := fun _ _ => rfl
  have hcont : ∀ w (g : ℝ → AF F), Continuous g → Continuous fun r => φ w (g r) := by
    intro w g hg
    simp only [hφ]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal w)).continuous.comp
      ((continuous_apply w).comp (continuous_fst.comp hg))
  have lin : ∀ (p : VA F N →+ AF F), Continuous p → ∀ w r, φ w (p (M r)) = r * φ w (p (M 1)) := by
    intro p hp w r
    let f : ℝ →+ ℝ := ((φ w).toAddMonoidHom.comp p).comp M
    have hc : Continuous f := hcont w (fun r => p (M r)) (hp.comp hM.1)
    have := map_real_smul f hc r 1
    simpa [f] using this
  have p1 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_fst
  have p2 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.snd _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_snd
  have k1 : ∀ l w r, φ w ((M r).1 l) = r * φ w ((M 1).1 l) := fun l w r => lin _ (p1 l) w r
  have k2 : ∀ l w r, φ w ((M r).2 l) = r * φ w ((M 1).2 l) := fun l w r => lin _ (p2 l) w r
  have hfst : fstA F (symV (M t) (M s)) = 0 := by
    funext w
    apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).injective
    have h : φ w (symV (M t) (M s)) = 0 := by
      simp only [symV, dotProduct, map_sub, map_sum, map_mul]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [k1 l w t, k1 l w s, k2 l w t, k2 l w s]
      ring
    exact h.trans (map_zero _).symm
  have h0 : ∀ r l, sndA F ((M r).1 l) = 0 ∧ sndA F ((M r).2 l) = 0 := fun r l =>
    ⟨congrFun (hM.2 r).1 l, congrFun (hM.2 r).2 l⟩
  have hsnd : sndA F (symV (M t) (M s)) = 0 := by
    simp only [symV, dotProduct, map_sub, map_sum, map_mul, (h0 _ _).1, (h0 _ _).2, zero_mul,
      Finset.sum_const_zero, sub_zero]
  exact Prod.ext hfst hsnd

end GlobalTheory.ThetaTransform

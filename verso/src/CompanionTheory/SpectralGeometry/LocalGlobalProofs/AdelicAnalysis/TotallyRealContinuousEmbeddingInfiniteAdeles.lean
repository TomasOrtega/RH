import Mathlib

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicRealLine

/- English proof (translation)
Establish `h` using `(InfinitePlace.Completion.isometryEquivRealOfIsReal hw).dist_eq x 0`. Establish `h0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal hw) 0 = 0` using `map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw)`. Rewrite `h` using `[h0, dist_zero_right, dist_zero_right]`. Rewrite using `[← h, Real.norm_eq_abs]`. Both sides reduce to the same expression.
-/
theorem norm_eq_abs_ringEquiv {F : Type} [Field F] {w : InfinitePlace F} (hw : w.IsReal)
    (x : w.Completion) :
    ‖x‖ = |InfinitePlace.Completion.ringEquivRealOfIsReal hw x| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).dist_eq x 0
  have h0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal hw) 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  rw [h0, dist_zero_right, dist_zero_right] at h
  rw [← h, Real.norm_eq_abs]
  rfl

/- English proof (translation)
Introduce `F _ _ hF`. Establish `hr : ∀ w : InfinitePlace F, w.IsReal` using `fun w => @IsTotallyReal.isReal F _ hF w`. Use `⟨⟨Pi.ringHom fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).symm.toRingHom, ?_⟩, ?_⟩` and prove the remaining obligations. Use `continuous_pi fun w => ?_` and prove the remaining obligations. Conclude with `(InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm.continuous`.

Introduce `θ _ t w`. Establish `hφ` using `DFunLike.congr_fun (Subsingleton.elim (((InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).toRingHom.comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ)) : ℝ →+* ℝ) (RingHom.id ℝ)) t`. Express the relevant statement in the definitionally equal form `InfinitePlace.Completion.ringEquivRealOfIsReal (hr w) (θ t w) = t at hφ`. Rewrite using `[GlobalTheory.CompanionTheory.AdelicRealLine.norm_eq_abs_ringEquiv (hr w), hφ]`.
-/
theorem exists_continuous_real_embedding :
    ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
      (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧
        ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
          ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  intro F _ _ hF
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => @IsTotallyReal.isReal F _ hF w
  refine ⟨⟨Pi.ringHom fun w =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).symm.toRingHom, ?_⟩, ?_⟩
  · refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm.continuous
  · intro θ _ t w
    have hφ := DFunLike.congr_fun (Subsingleton.elim
      (((InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).toRingHom.comp
        ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ)) : ℝ →+* ℝ)
      (RingHom.id ℝ)) t
    change InfinitePlace.Completion.ringEquivRealOfIsReal (hr w) (θ t w) = t at hφ
    rw [GlobalTheory.CompanionTheory.AdelicRealLine.norm_eq_abs_ringEquiv (hr w), hφ]

end GlobalTheory.CompanionTheory.AdelicRealLine

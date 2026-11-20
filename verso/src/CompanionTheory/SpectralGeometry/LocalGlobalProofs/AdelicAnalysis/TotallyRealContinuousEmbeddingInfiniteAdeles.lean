import Mathlib

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicRealLine

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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

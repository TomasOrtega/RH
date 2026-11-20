import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace MCChartFrameDeriv

/- English proof (translation)
Establish `h1 : A j l ≤ ∑ l', A j l'` using `Finset.single_le_sum (f := fun l' => A j l') (fun l' _ => (hA j l').le) (Finset.mem_univ l)`. Establish `h2 : ∑ l', A j l' ≤ ∑ j', ∑ l', A j' l'` using `Finset.single_le_sum (f := fun j' => ∑ l', A j' l') (fun j' _ => Finset.sum_nonneg fun l' _ => (hA j' l').le) (Finset.mem_univ j)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_one_add_sum {g r : ℕ} (A : Fin g → Fin r → ℝ) (hA : ∀ j l, 0 < A j l) (j : Fin g)
    (l : Fin r) : A j l ≤ 1 + ∑ j', ∑ l', A j' l' := by
  have h1 : A j l ≤ ∑ l', A j l' :=
    Finset.single_le_sum (f := fun l' => A j l') (fun l' _ => (hA j l').le) (Finset.mem_univ l)
  have h2 : ∑ l', A j l' ≤ ∑ j', ∑ l', A j' l' :=
    Finset.single_le_sum (f := fun j' => ∑ l', A j' l')
      (fun j' _ => Finset.sum_nonneg fun l' _ => (hA j' l').le) (Finset.mem_univ j)
  linarith

end MCChartFrameDeriv

open MCChartFrameDeriv in

/- English proof (translation)
Introduce `D`. Establish `hU : IsOpen (D.U ×ˢ D.V)` using `D.isOpen_U.prod D.isOpen_V`. Establish `hex : ∀ j l, ∃ A : ℝ, 0 < A ∧ ∀ x ∈ D.K, DifferentiableAt ℝ (fun q => D.f q j l) x ∧ ‖D.f x j l‖ ≤ A ∧ ‖fderiv ℝ (fun q => D.f q j l) x‖ ≤ A` using `fun j l => h₁ (fun q => D.f q j l) (D.U ×ˢ D.V) D.K hU (D.f_analytic j l) D.isCompact_K D.K_subset`. Use `choose A hApos hA using hex`. Establish `hsum : 0 ≤ ∑ j, ∑ l, A j l` using `Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hApos j l).le`.

Use `⟨1 + ∑ j, ∑ l, A j l, by linarith, fun p hp j l => ?_⟩` and prove the remaining obligations. Take `⟨hd, hb, hb'⟩` from `hA j l p hp`. Establish `hle` using `le_one_add_sum A hApos j l`. Conclude with `⟨hd, hb.trans hle, hb'.trans hle⟩`.
-/
theorem ChartFrameDeriv.proof (h₁ : AnalyticDerivBound.Statement) : ChartFrameDeriv.Statement := by
  intro D
  have hU : IsOpen (D.U ×ˢ D.V) := D.isOpen_U.prod D.isOpen_V
  have hex : ∀ j l, ∃ A : ℝ, 0 < A ∧ ∀ x ∈ D.K,
      DifferentiableAt ℝ (fun q => D.f q j l) x ∧ ‖D.f x j l‖ ≤ A ∧
        ‖fderiv ℝ (fun q => D.f q j l) x‖ ≤ A := fun j l =>
    h₁ (fun q => D.f q j l) (D.U ×ˢ D.V) D.K hU (D.f_analytic j l) D.isCompact_K D.K_subset
  choose A hApos hA using hex
  have hsum : 0 ≤ ∑ j, ∑ l, A j l :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hApos j l).le
  refine ⟨1 + ∑ j, ∑ l, A j l, by linarith, fun p hp j l => ?_⟩
  obtain ⟨hd, hb, hb'⟩ := hA j l p hp
  have hle := le_one_add_sum A hApos j l
  exact ⟨hd, hb.trans hle, hb'.trans hle⟩

end

end GroundTheory.Heights₂.Heights

import Formalism.PeriodIntegrals.InvSerSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatMemWf

noncomputable section

namespace PI.WfLogWork

open PI.ExpIntWProof

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h n`. Conclude with `h (Finsupp.single () n)`. Introduce `h n`. Establish `hn : n = Finsupp.single () (n ())` using `by first`.

Consider the case `exact Finsupp.unique_single n`. Consider the case `(ext; simp)`. Rewrite using `[hn]`. Conclude with `h (n ())`.
-/
theorem coefWf_iff {p : ℕ} [Fact p.Prime] (f : PowerSeries ℂ_[p]) :
    CoefWf (f : MvPowerSeries Unit ℂ_[p]) ↔ ∀ n, PowerSeries.coeff n f ∈ Wf p := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h n
    have hn : n = Finsupp.single () (n ()) := by
      first
        | exact Finsupp.unique_single n
        | (ext; simp)
    rw [hn]
    exact h (n ())

/- English proof (translation)
Use `show PI.InWf x`. Unfold `PI.InWf`. Conclude with `⟨0, by rw [pow_zero, one_mul]; exact h⟩`.
-/
theorem Wp_le_Wf {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (h : x ∈ Wp p) : x ∈ Wf p := by
  show PI.InWf x
  unfold PI.InWf
  exact ⟨0, by rw [pow_zero, one_mul]; exact h⟩

end PI.WfLogWork

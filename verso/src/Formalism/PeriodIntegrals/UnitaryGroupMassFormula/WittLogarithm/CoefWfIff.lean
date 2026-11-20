import Formalism.PeriodIntegrals.InvSerSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatMemWf

noncomputable section

namespace PI.WfLogWork

open PI.ExpIntWProof

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem Wp_le_Wf {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (h : x ∈ Wp p) : x ∈ Wf p := by
  show PI.InWf x
  unfold PI.InWf
  exact ⟨0, by rw [pow_zero, one_mul]; exact h⟩

end PI.WfLogWork

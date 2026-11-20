import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.AvgStep

noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfCpt

open MeasureTheory Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Substitute using the available equality. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem gelfCpt_of_steps (hAvg : AvgStep) (hMul : MulStep) (hSpan : PI.UMultOne.IntSpan)
    (hConv : PI.UMultOne.ConvComm) : PI.UMultOne.GelfandCompact := by
  intro G _ _ _ _ _ _ H τ hH hτc hτa hτi hτH N ρ hc hirr A B hA hB
  borelize G
  let μ : Measure G := Measure.haar
  obtain ⟨a, ha, hAa⟩ := hSpan G μ N ρ hc hirr A
  obtain ⟨b, hb, hBb⟩ := hSpan G μ N ρ hc hirr B
  have eA : A = intMat μ ρ a := by ext i j; exact hAa i j
  have eB : B = intMat μ ρ b := by ext i j; exact hBb i j
  subst eA eB
  obtain ⟨a', ha'c, ha'i, ea'⟩ := hAvg G μ H hH N ρ hc a ha hA
  obtain ⟨b', hb'c, hb'i, eb'⟩ := hAvg G μ H hH N ρ hc b hb hB
  rw [← ea', ← eb', hMul G μ N ρ hc a' b' ha'c hb'c, hMul G μ N ρ hc b' a' hb'c ha'c]
  congr 1
  funext z
  exact hConv G μ H τ hτc hτa hτi hτH a' b' ha'c hb'c ha'i hb'i z

end PI.UnitaryGroupMassFormula.GelfCpt

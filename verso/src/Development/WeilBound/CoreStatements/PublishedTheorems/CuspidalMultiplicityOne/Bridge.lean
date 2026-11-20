import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.CuspidalMultiplicityOne.CuspidalMultiplicityOneLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfUnitary

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep

namespace PositivityTheory.Lit1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem cuspidalMultiplicityOneUnitary_of_lit (h : CuspidalMultiplicityOneLit) :
    GlobalTheory.Published.CuspidalMultiplicityOneUnitary := by
  intro E _ _ _ a ha π π' hu _ e
  have hiso : CuspSub.Iso π π' := Quotient.exact (s := CuspSub.setoid E a) e
  have h1 : π ∈ {π'' : CuspSub E a | π''.Iso π} := (CuspSub.setoid E a).iseqv.refl π
  have h2 : π' ∈ {π'' : CuspSub E a | π''.Iso π} := (CuspSub.setoid E a).iseqv.symm hiso
  rw [h E a ha π hu h1 h2]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cuspidalMultiplicityOne_of_lit (h : CuspidalMultiplicityOneLit) : GlobalTheory.Published.CuspidalMultiplicityOne :=
  GlobalTheory.CuspMultOne.of_unitary (cuspidalMultiplicityOneUnitary_of_lit h)

end PositivityTheory.Lit1

end

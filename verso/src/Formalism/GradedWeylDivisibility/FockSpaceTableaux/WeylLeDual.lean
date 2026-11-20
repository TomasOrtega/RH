import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
private theorem applyWord_hw_mem_dualWeyl
    (h1 : HWMem) (h2 : RowDivStable)
    (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∀ w : List (Fin r × Fin r × ℕ),
      applyWord R w (hw R hn ν) ∈ dualWeyl R r n ν := fun
  | [] => h1 R r n hn ν hν
  | x :: w => h2 R r n ν x.1 x.2.1 x.2.2 _
      (applyWord_hw_mem_dualWeyl h1 h2 R r n hn ν hν w)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem weylLeDual_of (h1 : HWMem) (h2 : RowDivStable) : WeylLeDual := by
  intro R _ r n hn ν hν
  show Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) =>
      applyWord R w (hw R hn ν)) ≤ dualWeyl R r n ν
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact applyWord_hw_mem_dualWeyl h1 h2 R r n hn ν hν w

end Formalism.GradedWeylDivisibility

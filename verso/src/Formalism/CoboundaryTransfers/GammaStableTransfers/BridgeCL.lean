import Formalism.CoboundaryTransfers.StatementBridge
import Formalism.WachModuleLifts.WachModuleProofs.WachModuleStatementHolds

noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem baseOfCL_qLin {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (B : CL.W.Base p A) : (baseOfCL B).QLin := by
  show B.q = B.π₀ + ((p : ℕ) : A)
  rw [B.hq, map_natCast]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem wach_lattice_nonempty_Q : NonemptyQ := by
  intro p _
  obtain ⟨W, hN, hX⟩ := CL.W.wach_module_nonempty p
  refine ⟨baseOfCL (CL.W.polyBase p), ofCL W, rfl, hN, hX, ?_, baseOfCL_qLin _,
    (CL.W.polyBase p).hφ⟩
  show ¬ IsUnit (Polynomial.X + Polynomial.C (p : ℤ_[p]))
  exact Polynomial.not_isUnit_X_add_C _

end Formalism.CoboundaryTransfers

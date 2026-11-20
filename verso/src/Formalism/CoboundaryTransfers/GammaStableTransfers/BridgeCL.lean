import Formalism.CoboundaryTransfers.StatementBridge
import Formalism.WachModuleLifts.WachModuleProofs.WachModuleStatementHolds

noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

/- English proof (translation)
Use `show B.q = B.π₀ + ((p : ℕ) : A)`. Rewrite using `[B.hq, map_natCast]`.
-/
theorem baseOfCL_qLin {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (B : CL.W.Base p A) : (baseOfCL B).QLin := by
  show B.q = B.π₀ + ((p : ℕ) : A)
  rw [B.hq, map_natCast]

/- English proof (translation)
Introduce `p _`. Take `⟨W, hN, hX⟩` from `CL.W.wach_module_nonempty p`. Use `⟨baseOfCL (CL.W.polyBase p), ofCL W, rfl, hN, hX, ?_, baseOfCL_qLin _, (CL.W.polyBase p).hφ⟩` and prove the remaining obligations. Use `show ¬ IsUnit (Polynomial.X + Polynomial.C (p : ℤ_[p]))`. Conclude with `Polynomial.not_isUnit_X_add_C _`.
-/
theorem wach_lattice_nonempty_Q : NonemptyQ := by
  intro p _
  obtain ⟨W, hN, hX⟩ := CL.W.wach_module_nonempty p
  refine ⟨baseOfCL (CL.W.polyBase p), ofCL W, rfl, hN, hX, ?_, baseOfCL_qLin _,
    (CL.W.polyBase p).hφ⟩
  show ¬ IsUnit (Polynomial.X + Polynomial.C (p : ℤ_[p]))
  exact Polynomial.not_isUnit_X_add_C _

end Formalism.CoboundaryTransfers

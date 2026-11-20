import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct

namespace GlobalTheory.GapRegular

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Sep (S : SPar) : Prop := ∀ x ∈ S, ∀ y ∈ S, y.1 < x.1 → y.1 + 2 ≤ x.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Sep.dual {S : SPar} (h : Sep S) : Sep (dualPar S) := by
  intro x hx y hy hxy
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
  have := h y' hy' x' hx' (by simpa using hxy)
  simp only
  linarith

end GlobalTheory.GapRegular

end

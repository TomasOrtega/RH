import Formalism.LocalToGlobal.JointCharacters.SameChr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct

namespace Formalism.L2.JoinChr

open Formalism.L2.Theta Formalism.L2.Host

variable {D : D7} {X : ThetaX D} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch}

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem plOf_eq {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) :
    plOf D θ τ = InfinitePlace.mk (embTau D τ) := by
  unfold plOf
  congr 1
  ext k
  have h := (hθ τ).1 k
  have e1 : Theta.infPart D (incA D k) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] k := by
    simp [Theta.infPart, incA, inclR]
  simp only [RingHom.comp_apply]
  rw [e1, h]
  rfl

end Formalism.L2.JoinChr

end

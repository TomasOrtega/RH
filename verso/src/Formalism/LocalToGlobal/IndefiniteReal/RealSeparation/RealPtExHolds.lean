import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.IsRealPtO
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Fock.DRho Matrix

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Establish an intermediate fact. Substitute using the available equality. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isRealPtO_iff {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : RPt D m n) (w : Mx D m n) :
    IsRealPtO θ z w ↔ w = Lb D m n z := by
  have e := Formalism.IndefR.Eqv.eq_thetaC D hθ
  subst e
  constructor
  · rintro ⟨h1, h2⟩
    have hf : ∀ i j, finPart D (w i j) = 0 := fun i j => by
      have := congrFun (congrFun h1 i) j
      rw [Matrix.map_apply, Matrix.zero_apply] at this
      exact this
    rw [← Lb_sigH w hf]
    congr 1
    funext ρ i j
    have := congrFun (congrFun (h2 ρ) i) j
    simp only [compAt, Matrix.map_apply, Matrix.of_apply] at this
    rw [sigH_apply]
    exact this
  · rintro rfl
    refine ⟨?_, fun τ => compAt_Lb z τ⟩
    ext i j
    rw [Matrix.map_apply, Matrix.zero_apply]
    exact finPart_Lb z i j

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem realPtEx_holds : RealPtEx D := by
  intro θ m n hθ z
  exact ⟨Lb D m n z, (isRealPtO_iff hθ z _).2 rfl, fun w hw => (isRealPtO_iff hθ z w).1 hw⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem realPt_eq {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : RPt D m n) : realPt θ z = Lb D m n z :=
  (isRealPtO_iff hθ z _).1 (Classical.epsilon_spec ⟨Lb D m n z, (isRealPtO_iff hθ z _).2 rfl⟩)

end Formalism.IndefR.Mi

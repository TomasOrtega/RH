import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.IsRealPtO
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Fock.DRho Matrix

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Establish `e` using `Formalism.IndefR.Eqv.eq_thetaC D hθ`. Substitute `e` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `hf : ∀ i j, finPart D (w i j) = 0` using `fun i j => by`.

Use `congrFun (congrFun h1 i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply, Matrix.zero_apply]`. Conclude with `this`. Rewrite using `[← Lb_sigH w hf]`. Use `congr 1`.

Use function extensionality and compare the values at `ρ i j`. Use `congrFun (congrFun (h2 ρ) i) j` as an intermediate fact. Simplify using `only [compAt, Matrix.map_apply, Matrix.of_apply] at this`. Rewrite using `[sigH_apply]`. Conclude with `this`.

Introduce and unpack `rfl`. Use `⟨?_, fun τ => compAt_Lb z τ⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.zero_apply]`. Conclude with `finPart_Lb z i j`.
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
Introduce `θ m n hθ z`. Conclude with `⟨Lb D m n z, (isRealPtO_iff hθ z _).2 rfl, fun w hw => (isRealPtO_iff hθ z w).1 hw⟩`.
-/
theorem realPtEx_holds : RealPtEx D := by
  intro θ m n hθ z
  exact ⟨Lb D m n z, (isRealPtO_iff hθ z _).2 rfl, fun w hw => (isRealPtO_iff hθ z w).1 hw⟩

/- English proof (translation)
The claim follows from `(isRealPtO_iff hθ z _).1 (Classical.epsilon_spec ⟨Lb D m n z, (isRealPtO_iff hθ z _).2 rfl⟩)`.
-/
theorem realPt_eq {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : RPt D m n) : realPt θ z = Lb D m n z :=
  (isRealPtO_iff hθ z _).1 (Classical.epsilon_spec ⟨Lb D m n z, (isRealPtO_iff hθ z _).2 rfl⟩)

end Formalism.IndefR.Mi

import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

/- English proof (translation)
Establish `h` using `LinearMap.toMatrix_mulVec_repr X.bas X.bas (Matrix.toLin X.bas X.bas (M.map X.ιE)) y`. Rewrite `h` using `[LinearMap.toMatrix_toLin]`. Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, ← h, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, RingEquiv.symm_apply_apply]`.
-/
private theorem crd_toLin_map_eq_mulVec_crd {D : D7} (X : HidaSetting D) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
    (y : (VS D).V) : X.crd (Matrix.toLin X.bas X.bas (M.map X.ιE) y) = M *ᵥ X.crd y := by
  have h := LinearMap.toMatrix_mulVec_repr X.bas X.bas (Matrix.toLin X.bas X.bas (M.map X.ιE)) y
  rw [LinearMap.toMatrix_toLin] at h
  funext i
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, ← h, Matrix.mulVec, dotProduct,
    Matrix.map_apply, map_sum, map_mul, RingEquiv.symm_apply_apply]

/- English proof (translation)
Introduce `D X g hg`. Set `A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E` to `(g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)`. Set `B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E` to `((g⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)`. Establish `hinj : ∀ y y' : (VS D).V, X.crd y = X.crd y' → y = y'`. Introduce `y y' h`.

Apply `X.bas.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Use `congrFun h i` as an intermediate fact. Simplify `this` using `[Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf]`. Set `n : (VS D).V ≃ₗ[D.host.E] (VS D).V` to `LinearEquiv.ofLinear (Matrix.toLin X.bas X.bas (A.map X.ιE)) (Matrix.toLin X.bas X.bas (B.map X.ιE)) (LinearMap.ext fun y => hinj _ _ (by`.

Rewrite using `[LinearMap.comp_apply, crd_toLin_map_eq_mulVec_crd, crd_toLin_map_eq_mulVec_crd, Matrix.mulVec_mulVec]`. Simplify using `[A, B]))`. Use the proof step `(LinearMap.ext fun y => hinj _ _ (by`. Rewrite using `[LinearMap.comp_apply, crd_toLin_map_eq_mulVec_crd, crd_toLin_map_eq_mulVec_crd, Matrix.mulVec_mulVec]`. Simplify using `[A, B]))`.

Establish `hn : ∀ y, X.crd (n y) = A *ᵥ X.crd y` using `fun y => crd_toLin_map_eq_mulVec_crd X A y`. Use `⟨n, ?_, hn⟩` and prove the remaining obligations. Introduce `x y`. Rewrite using `[← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X (n x) (n y), ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y, hn, hn, Formalism.L2.SG.PoincareInHH.Cut.hform_mulVec _ _ _ hg]`.
-/
theorem memIsomOf_holds : MemIsomOf := by
  intro D X g hg
  let A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E := (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  let B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
    ((g⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  have hinj : ∀ y y' : (VS D).V, X.crd y = X.crd y' → y = y' := by
    intro y y' h
    apply X.bas.repr.injective
    ext i
    have := congrFun h i
    simpa [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf] using this
  let n : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
    LinearEquiv.ofLinear (Matrix.toLin X.bas X.bas (A.map X.ιE)) (Matrix.toLin X.bas X.bas (B.map X.ιE))
      (LinearMap.ext fun y => hinj _ _ (by
        rw [LinearMap.comp_apply, crd_toLin_map_eq_mulVec_crd, crd_toLin_map_eq_mulVec_crd, Matrix.mulVec_mulVec]
        simp [A, B]))
      (LinearMap.ext fun y => hinj _ _ (by
        rw [LinearMap.comp_apply, crd_toLin_map_eq_mulVec_crd, crd_toLin_map_eq_mulVec_crd, Matrix.mulVec_mulVec]
        simp [A, B]))
  have hn : ∀ y, X.crd (n y) = A *ᵥ X.crd y := fun y => crd_toLin_map_eq_mulVec_crd X A y
  refine ⟨n, ?_, hn⟩
  intro x y
  rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X (n x) (n y), ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y,
    hn, hn, Formalism.L2.SG.PoincareInHH.Cut.hform_mulVec _ _ _ hg]

end Formalism.L2.SG.TermOp.Vanish

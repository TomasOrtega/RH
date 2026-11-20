import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLift

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Lift

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) {m : ℕ}

def mu (Z : M.Mat (m + 1)) (v : Fin (m + 1) → M.R) : E :=
  ((Z.Z.map M.R.subtype)⁻¹.mulVec fun i => (v i : E)) (Fin.last m)

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem mu_add (Z : M.Mat (m + 1)) (v w : Fin (m + 1) → M.R) : mu M Z (v + w) = mu M Z v + mu M Z w := by
  unfold mu
  have e : (fun i => ((v + w) i : E)) = (fun i => (v i : E)) + fun i => (w i : E) := by
    funext i
    simp
  rw [e, Matrix.mulVec_add]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem mu_smul (Z : M.Mat (m + 1)) (a : M.R) (v : Fin (m + 1) → M.R) : mu M Z (a • v) = (a : E) * mu M Z v := by
  unfold mu
  have e : (fun i => ((a • v) i : E)) = (a : E) • fun i => (v i : E) := by
    funext i
    simp
  rw [e, Matrix.mulVec_smul]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mu_sum (Z : M.Mat (m + 1)) {ι : Type} (s : Finset ι) (f : ι → Fin (m + 1) → M.R) :
    mu M Z (∑ i ∈ s, f i) = ∑ i ∈ s, mu M Z (f i) := by
  exact map_sum (AddMonoidHom.mk' (mu M Z) (mu_add M Z)) f s

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem coe_mulVec (Z : M.Mat (m + 1)) (x : Fin (m + 1) → M.R) :
    (fun i => ((Z.Z.mulVec x) i : E)) = (Z.Z.map M.R.subtype).mulVec fun j => (x j : E) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem mu_Z (Z : M.Mat (m + 1)) (x : Fin (m + 1) → M.R) : mu M Z (Z.Z.mulVec x) = (x (Fin.last m) : E) := by
  unfold mu
  rw [coe_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ Z.unit, Matrix.one_mulVec]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument.

A detailed English derivation is pending.
-/
theorem mulVec_inj (Z : M.Mat (m + 1)) {x y : Fin (m + 1) → M.R} (h : Z.Z.mulVec x = Z.Z.mulVec y) : x = y := by
  have h1 := congrArg (fun v => fun i => ((v i : M.R) : E)) h
  rw [coe_mulVec, coe_mulVec] at h1
  have h2 := congrArg (fun v => (Z.Z.map M.R.subtype)⁻¹.mulVec v) h1
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ Z.unit, Matrix.one_mulVec] at h2
  funext i
  exact Subtype.ext (congrFun h2 i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lam_mk (Z : M.Mat (m + 1)) (v : Fin (m + 1) → M.R) :
    M.lam Z (Submodule.Quotient.mk v) = M.Rsub.mkQ (mu M Z v) := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem mu_e (Z : M.Mat (m + 1)) :
    mu M Z (Pi.single (Fin.last m) 1) = (Z.Z.map M.R.subtype)⁻¹ (Fin.last m) (Fin.last m) := by
  unfold mu
  have e : (fun i => (((Pi.single (Fin.last m) (1 : M.R) : Fin (m + 1) → M.R) i : M.R) : E)) =
      (Pi.single (Fin.last m) (1 : E) : Fin (m + 1) → E) := by
    funext i
    by_cases h : i = Fin.last m <;> simp [h]
  rw [e, Matrix.mulVec_single]
  simp

def headK (Z : M.Mat (m + 1)) : Submodule M.R (Fin (m + 1) → M.R) :=
  (LinearMap.ker (LinearMap.proj (R := M.R) (φ := fun _ : Fin (m + 1) => M.R) (Fin.last m))).map Z.Z.mulVecLin

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_headK (Z : M.Mat (m + 1)) {y : Fin (m + 1) → M.R} :
    y ∈ headK M Z ↔ ∃ x, x (Fin.last m) = 0 ∧ Z.Z.mulVec x = y := by
  simp [headK, Submodule.mem_map, LinearMap.mem_ker]

end Lift

def LiftOrb : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ (m : ℕ) (Z Z' : M.Mat (m + 1)), Nonempty (M.Iso Z Z') →
    (Z.Z.map M.R.subtype)⁻¹ (Fin.last m) (Fin.last m) = (Z'.Z.map M.R.subtype)⁻¹ (Fin.last m) (Fin.last m) →
    ∃ l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R, IsUnit l.det ∧ IsUnit ρ.det ∧
      (∀ i, l i (Fin.last m) = if i = Fin.last m then 1 else 0) ∧
      (∀ j, ρ (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ Z'.Z = l * Z.Z * ρ

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CompanionTheory.LieCurve

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

def expUnit (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) : GL (Fin a) (Cinf E) where
  val := NormedSpace.exp (t • M)
  inv := NormedSpace.exp (-(t • M))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • M)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • M)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem expUnit_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    (expUnit E a M t).val = NormedSpace.exp (t • M) := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `NormedSpace.exp (-(t • M)) = _`. Rewrite using `[neg_smul]`.
-/
theorem expUnit_inv_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    ((expUnit E a M t)⁻¹).val = NormedSpace.exp ((-t) • M) := by
  change NormedSpace.exp (-(t • M)) = _
  rw [neg_smul]

/- English proof (translation)
Use `haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _`. Conclude with `hasDerivAt_exp_smul_const (𝕂 := ℝ) M t`.
-/
theorem hasDerivAt_exp (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • M)) (NormedSpace.exp (t • M) * M) t := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) M t

/- English proof (translation)
The claim follows from `continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp E a M t).continuousAt`.
-/
theorem continuous_exp_smul (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    Continuous fun t : ℝ => NormedSpace.exp (t • M) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp E a M t).continuousAt

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨continuous_exp_smul E a M, ?_⟩` and prove the remaining obligations. Conclude with `((continuous_exp_smul E a M).comp continuous_neg).congr fun t => (expUnit_inv_val E a M t).symm`.
-/
theorem continuous_expUnit (M : Matrix (Fin a) (Fin a) (Cinf E)) : Continuous (expUnit E a M) := by
  refine Units.continuous_iff.2 ⟨continuous_exp_smul E a M, ?_⟩
  exact ((continuous_exp_smul E a M).comp continuous_neg).congr fun t => (expUnit_inv_val E a M t).symm

/- English proof (translation)
Use `ext1`. Rewrite using `[expUnit_val, zero_smul, NormedSpace.exp_zero]`. Both sides reduce to the same expression.
-/
theorem expUnit_zero (M : Matrix (Fin a) (Fin a) (Cinf E)) : expUnit E a M 0 = 1 := by
  ext1
  rw [expUnit_val, zero_smul, NormedSpace.exp_zero]
  rfl

/- English proof (translation)
Use `ext1`. Rewrite using `[Units.val_mul, expUnit_val, expUnit_val, expUnit_val, add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl M).smul_left s).smul_right t)]`.
-/
theorem expUnit_add (M : Matrix (Fin a) (Fin a) (Cinf E)) (s t : ℝ) :
    expUnit E a M (s + t) = expUnit E a M s * expUnit E a M t := by
  ext1
  rw [Units.val_mul, expUnit_val, expUnit_val, expUnit_val, add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl M).smul_left s).smul_right t)]

/- English proof (translation)
Establish `e : star (NormedSpace.exp (t • M)) = NormedSpace.exp (-(t • M))`. Rewrite using `[Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, h]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mem_unitaryGroup_iff, expUnit_val, e]`. Conclude with `(expUnit E a M t).val_inv`.
-/
theorem expUnit_mem_unitary (M : Matrix (Fin a) (Fin a) (Cinf E)) (h : Mᴴ = -M) (t : ℝ) :
    (expUnit E a M t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := by
  have e : star (NormedSpace.exp (t • M)) = NormedSpace.exp (-(t • M)) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, h]
    simp
  rw [Matrix.mem_unitaryGroup_iff, expUnit_val, e]
  exact (expUnit E a M t).val_inv

def toLieL : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.of.symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toLieL_apply (M : Matrix (Fin a) (Fin a) (Cinf E)) : toLieL E a M = Matrix.of.symm M := rfl

/- English proof (translation)
Establish `h` using `(toLieL E a).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp E a M 0)`. Establish `e : toLieL E a (NormedSpace.exp ((0 : ℝ) • M) * M) = Matrix.of.symm M`. Rewrite using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Both sides reduce to the same expression. Conclude with `h.congr_deriv e`.
-/
theorem hasDerivAt_toL (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    HasDerivAt (fun t : ℝ => toL (expUnit E a M t).val) (Matrix.of.symm M) 0 := by
  have h := (toLieL E a).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp E a M 0)
  have e : toLieL E a (NormedSpace.exp ((0 : ℝ) • M) * M) = Matrix.of.symm M := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]; rfl
  exact h.congr_deriv e

end

/- English proof (translation)
Assemble the required witnesses or components as `⟨expUnit E a (Matrix.of X), continuous_expUnit E a _, expUnit_zero E a _, expUnit_add E a _, hasDerivAt_toL E a _, fun h t => expUnit_mem_unitary E a _ h t⟩`.
-/
theorem exists_curve (E : Type) [Field E] [NumberField E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧
      HasDerivAt (fun t => toL (c t).val) X 0 ∧
      ((Matrix.of X)ᴴ = -(Matrix.of X) → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) :=
  ⟨expUnit E a (Matrix.of X), continuous_expUnit E a _, expUnit_zero E a _, expUnit_add E a _,
    hasDerivAt_toL E a _, fun h t => expUnit_mem_unitary E a _ h t⟩

end GlobalTheory.CompanionTheory.LieCurve

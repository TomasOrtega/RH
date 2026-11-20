import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
/- English proof (translation)
Replace the relevant objects with their definitions. Assume the hypotheses and unpack their components. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem mulMat_stdLat_le {F : Type} [Field F] [NumberField F]
    (A : Matrix (Fin 2) (Fin 2) ℤ) :
    _root_.GlobalTheory.HilbFam.mulMat (_root_.GlobalTheory.HilbFam.stdLat F) A ≤
      _root_.GlobalTheory.HilbFam.stdLat F := by
  unfold _root_.GlobalTheory.HilbFam.mulMat
  rintro _ ⟨y, hy, rfl⟩
  unfold _root_.GlobalTheory.HilbFam.stdLat at hy ⊢
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  simp only [LinearMap.coe_restrictScalars, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hj : y j * (A.map Int.cast) j i = ((A j i : 𝓞 F)) • y j := by
    simp [Algebra.smul_def, mul_comm]
  rw [hj]
  exact Submodule.smul_mem _ _ (hy j (Set.mem_univ j))

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ)
    (L : _root_.GlobalTheory.HilbFam.Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)),
    _root_.GlobalTheory.HilbFam.HasLevel N L → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.twist N L α) := by
  intro F _ _ _ N L α hL
  obtain ⟨_, hle⟩ := hL
  unfold _root_.GlobalTheory.HilbFam.HasLevel _root_.GlobalTheory.HilbFam.twist
  refine ⟨fun x hx => Submodule.mem_sup_right ?_, sup_le ?_ (mulMat_stdLat_le _)⟩
  · unfold _root_.GlobalTheory.HilbFam.mulMat
    convert Submodule.mem_map_of_mem hx using 1
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Matrix.natCast_apply] <;>
      rw [Algebra.smul_def, map_natCast, mul_comm]
  · unfold _root_.GlobalTheory.HilbFam.mulMat
    exact (Submodule.map_mono hle).trans (mulMat_stdLat_le _)

end GlobalTheory.HilbFam

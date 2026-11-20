import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroSmulMemMap
open scoped PowerSeries Pointwise
namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map`. Consider the case `exact _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map`. Consider the case `(apply _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map ..)`.
-/
theorem coeff_zero_smul_mem_map_of_aeval_mul_eq_zero : ∀ {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (T : Module.End O V) (Rp : Polynomial O), Polynomial.aeval T Rp * T = 0 → ∀ (Z : Submodule O V), (∀ z ∈ Z, T z ∈ Z) → ∀ w ∈ Z, w ∈ LinearMap.range T → Rp.coeff 0 • w ∈ Z.map T := by
  first
  | exact @_root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map
  | exact _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map
  | (apply _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map ..)

end GlobalTheory

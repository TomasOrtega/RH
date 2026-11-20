import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.VacuumWeight

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.sum_apply]`. Simplify using `only [Matrix.smul_apply, Eab, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Matrix.diagonal_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h]`. Use `symm`. Conclude with `Finset.sum_eq_zero fun c _ => if_neg fun hc => h (hc.1.symm.trans hc.2)`.
-/
theorem diagonal_eq_sum_Eab {r s : ℕ} (D : Ix r s → ℂ) :
    Matrix.diagonal D = ∑ c, D c • Eab c c := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Eab, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]; symm
    exact Finset.sum_eq_zero fun c _ => if_neg fun hc => h (hc.1.symm.trans hc.2)

/- English proof (translation)
Apply the tactic sequence `rcases c with c | c <;> simp [Fintype.sum_sum_type, lineSign] <;> ring`.
-/
theorem sum_lineSign {p q r s : ℕ} (c : Ix r s) :
    ∑ a : Ix p q, lineSign a c = ((p : ℂ) - q) * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c := by
  rcases c with c | c <;> simp [Fintype.sum_sum_type, lineSign] <;> ring

/- English proof (translation)
Establish `h1 : (1 : Formalism.BasicNotions.TH.Pol p q r s) = MvPolynomial.monomial 0 1` using `rfl`. Rewrite using `[diagonal_eq_sum_Eab, map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, h1, cartan2, smul_smul]`. Use `congr 1`.

Simplify using `only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add]`. Rewrite using `[← Finset.sum_mul, sum_lineSign]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockAct2_diagonal_one (p q r s : ℕ) (D : Ix r s → ℂ) :
    fockAct2 p q r s (Matrix.diagonal D) (1 : Formalism.BasicNotions.TH.Pol p q r s) =
    ((((p : ℂ) - q) / 2) * ∑ c, D c * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c) • (1 : Formalism.BasicNotions.TH.Pol p q r s) := by
  have h1 : (1 : Formalism.BasicNotions.TH.Pol p q r s) = MvPolynomial.monomial 0 1 := rfl
  rw [diagonal_eq_sum_Eab, map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, LinearMap.smul_apply, h1, cartan2, smul_smul]
  congr 1
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add]
  rw [← Finset.sum_mul, sum_lineSign]
  ring

end GlobalTheory.VacuumWeight

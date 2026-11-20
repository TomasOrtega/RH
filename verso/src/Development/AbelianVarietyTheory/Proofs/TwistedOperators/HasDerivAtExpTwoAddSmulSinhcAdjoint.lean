import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KroneckerTransposeMulVecVecM
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpAddSmulDuhamel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralExpOneSubTwoMulSmul

noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [adMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply, smul_sub]`. Use `congr 1`. Rewrite using `[smul_mul_assoc]`. Rewrite using `[mul_smul_comm]`.
-/
theorem adMat_real_smul {p q : ℕ} (u : ℝ) (Y : Mat p q) : adMat (u • Y) = u • adMat Y := by
  ext i j
  simp only [adMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, smul_sub]
  congr 1
  · rw [smul_mul_assoc]
  · rw [mul_smul_comm]

def sandwichAct {p q : ℕ} (P V Q : Mat p q) :
    Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →ₗ[ℝ] Mat p q where
  toFun M := P * (Matrix.of fun a b => (M *ᵥ vecM V) (a, b)) * Q
  map_add' M N := by
    rw [← add_mul, ← mul_add]
    congr 2
    ext a b; simp [Matrix.add_mulVec]
  map_smul' t M := by
    rw [RingHom.id_apply, ← smul_mul_assoc, ← mul_smul_comm]
    congr 2
    ext a b; simp [Matrix.smul_mulVec]

/- English proof (translation)
Rewrite using `[add_smul]`. Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left u).smul_right v)`.
-/
theorem exp_real_smul_add {p q : ℕ} (Y : Mat p q) (u v : ℝ) :
    NormedSpace.exp ((u + v) • Y) = NormedSpace.exp (u • Y) * NormedSpace.exp (v • Y) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left u).smul_right v)

/- English proof (translation)
Establish `hl : (1 - s) • (Y + Y) = ((1 : ℝ) + (1 - 2 * s)) • Y`. Rewrite using `[← two_smul ℝ Y, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hr : s • (Y + Y) = (-(1 - 2 * s) + (1 : ℝ)) • Y`.

Rewrite using `[← two_smul ℝ Y, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hof : ∀ W : Mat p q, (Matrix.of fun a b => vecM W (a, b)) = W` using `fun W => by`. Use extensionality with `a b`.

Both sides reduce to the same expression. Rewrite using `[hl, hr, exp_real_smul_add, exp_real_smul_add, one_smul, neg_smul]`. Simplify using `only [sandwichAct, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[← adMat_real_smul, exp_adMat_mulVec, hof]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem duhamel_integrand_eq {p q : ℕ} (Y V : Mat p q) (s : ℝ) :
    NormedSpace.exp ((1 - s) • (Y + Y)) * V * NormedSpace.exp (s • (Y + Y)) =
      sandwichAct (NormedSpace.exp Y) V (NormedSpace.exp Y)
        (NormedSpace.exp ((1 - 2 * s) • adMat Y)) := by
  have hl : (1 - s) • (Y + Y) = ((1 : ℝ) + (1 - 2 * s)) • Y := by
    rw [← two_smul ℝ Y, smul_smul]; congr 1; ring
  have hr : s • (Y + Y) = (-(1 - 2 * s) + (1 : ℝ)) • Y := by
    rw [← two_smul ℝ Y, smul_smul]; congr 1; ring
  have hof : ∀ W : Mat p q, (Matrix.of fun a b => vecM W (a, b)) = W := fun W => by
    ext a b; rfl
  rw [hl, hr, exp_real_smul_add, exp_real_smul_add, one_smul, neg_smul]
  simp only [sandwichAct, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← adMat_real_smul, exp_adMat_mulVec, hof]
  simp only [Matrix.mul_assoc]

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Set `L : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →L[ℝ] Mat p q` to `LinearMap.toContinuousLinearMap (sandwichAct (NormedSpace.exp Y) V (NormedSpace.exp Y))`. Establish `hcont : Continuous fun s : ℝ => NormedSpace.exp ((1 - 2 * s) • adMat Y)` using `NormedSpace.exp_continuous.comp ((by fun_prop : Continuous fun s : ℝ => 1 - 2 * s).smul continuous_const)`. Establish `hsin : sinhcAd Y = ∑' k : ℕ, (((2 * k + 1).factorial : ℝ)⁻¹) • adMat Y ^ (2 * k)`. Simplify using `only [sinhcAd]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[← Complex.coe_smul]`. Use `push_cast`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `s`. Conclude with `duhamel_integrand_eq Y V s`. Use `_ = L (∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • adMat Y)) := L.intervalIntegral_comp_comm (hcont.intervalIntegrable 0 1)`. Use `_ = NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y := by`.

Establish `hI : ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • adMat Y) = sinhcAd Y`. Rewrite using `[hsin]`. Conclude with `integral_exp_one_sub_two_mul_smul _ (adMat Y)`. Rewrite using `[hI]`. Both sides reduce to the same expression.
-/
theorem integral_duhamel_eq_sAd {p q : ℕ} (Y V : Mat p q) :
    ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • (Y + Y)) * V * NormedSpace.exp (s • (Y + Y)) =
      NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y := by
  let L : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →L[ℝ] Mat p q :=
    LinearMap.toContinuousLinearMap (sandwichAct (NormedSpace.exp Y) V (NormedSpace.exp Y))
  have hcont : Continuous fun s : ℝ => NormedSpace.exp ((1 - 2 * s) • adMat Y) :=
    NormedSpace.exp_continuous.comp ((by fun_prop : Continuous fun s : ℝ => 1 - 2 * s).smul
      continuous_const)
  have hsin : sinhcAd Y =
      ∑' k : ℕ, (((2 * k + 1).factorial : ℝ)⁻¹) • adMat Y ^ (2 * k) := by
    simp only [sinhcAd]
    congr 1
    funext k
    rw [← Complex.coe_smul]
    push_cast
    rfl
  calc ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • (Y + Y)) * V * NormedSpace.exp (s • (Y + Y))
      = ∫ s in (0 : ℝ)..1, L (NormedSpace.exp ((1 - 2 * s) • adMat Y)) := by
        congr 1
        funext s
        exact duhamel_integrand_eq Y V s
    _ = L (∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • adMat Y)) :=
        L.intervalIntegral_comp_comm (hcont.intervalIntegrable 0 1)
    _ = NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y := by
        have hI : ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • adMat Y) = sinhcAd Y := by
          rw [hsin]
          exact integral_exp_one_sub_two_mul_smul _ (adMat Y)
        rw [hI]
        rfl

/- English proof (translation)
Use `letI : NormedRing (Mat p q) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Mat p q) := Matrix.linftyOpNormedAlgebra`. Establish `hD0` using `GlobalTheory.hasDerivAt_exp_add_smul_duhamel (Mat p q) (Y + Y) V`. Establish `hD : HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + Y + t • V)) (NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y) 0`. Rewrite using `[← integral_duhamel_eq_sAd Y V]`.

Conclude with `hD0`. Set `e : Mat p q →ₗ[ℝ] ℂ` to `{ toFun := fun M => M a b map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Conclude with `(LinearMap.toContinuousLinearMap e).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD`.
-/
theorem hasDerivAt_exp_two_add_smul (p q : ℕ) (Y V : Mat p q) (a b : Ix p q) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + Y + t • V) a b)
      ((NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y) a b) 0 := by
  letI : NormedRing (Mat p q) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat p q) := Matrix.linftyOpNormedAlgebra
  have hD0 := GlobalTheory.hasDerivAt_exp_add_smul_duhamel (Mat p q) (Y + Y) V
  have hD : HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + Y + t • V))
      (NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y) 0 := by
    rw [← integral_duhamel_eq_sAd Y V]
    exact hD0
  let e : Mat p q →ₗ[ℝ] ℂ :=
    { toFun := fun M => M a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap e).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD

end GlobalTheory.PolarU

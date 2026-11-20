import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm.P

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

def lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ[X] := 1 + (X : ℂ[X]) • A.map C

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem cf_lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    cf k (lin A) = if k = 0 then 1 else if k = 1 then A else 0 := by
  ext i j
  rcases k with _ | _ | k <;> by_cases h : i = j <;>
    simp [cf, lin, Matrix.one_apply, h, Polynomial.coeff_one, Polynomial.coeff_C]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coeffMatrix_zero_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 0 (lin A) = 1 := by
  simp [cf_lin]
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coeffMatrix_one_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 1 (lin A) = A := by
  simp [cf_lin]
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coeffMatrix_two_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 2 (lin A) = 0 := by
  simp [cf_lin]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cf_submatrix {α β γ δ : Type*} (k : ℕ) (P : Matrix α β ℂ[X]) (f : γ → α) (g : δ → β) :
    cf k (P.submatrix f g) = (cf k P).submatrix f g := rfl

abbrev Dc : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => (D k : ℂ)

abbrev Ym : Matrix (Fin m) (Fin m) ℂ := Y.submatrix (Fin.castLE hm) (Fin.castLE hm)

abbrev Dm : Matrix (Fin m) (Fin m) ℂ := diagonal fun i => (D (Fin.castLE hm i) : ℂ)

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Dc_sub : (Dc D).submatrix (Fin.castLE hm) (Fin.castLE hm) = Dm hm D := by
  ext i j
  by_cases h : i = j <;> simp [Dc, Dm, Matrix.diagonal_apply, h]

def GP (t : ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  (lin ((starRingEnd ℂ t) • Yᴴ) * ((Dc D).map C * lin (t • Y))).submatrix (Fin.castLE hm) (Fin.castLE hm)

def GnP (t : ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  lin (-((starRingEnd ℂ t) • (Ym hm Y)ᴴ)) * (GP hm D Y t * lin (-(t • Ym hm Y)))

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem coeffMatrix_zero_lineGramPoly (t : ℂ) : cf 0 (GP hm D Y t) = Dm hm D := by
  rw [GP, cf_submatrix, cf_mul_zero, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, one_mul, mul_one, Dc_sub]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeffMatrix_one_lineGramPoly (t : ℂ) : cf 1 (GP hm D Y t) =
    (starRingEnd ℂ t) • ((Ym hm Y)ᴴ * Dm hm D) + t • (Dm hm D * Ym hm Y) := by
  rw [GP, cf_submatrix, cf_mul_one, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly,
    one_mul, mul_one]
  ext i j
  simp [Dc, Dm, Ym, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem coeffMatrix_two_lineGramPoly (t : ℂ) : cf 2 (GP hm D Y t) =
    ((starRingEnd ℂ t) * t) • (Yᴴ * Dc D * Y).submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  rw [GP, cf_submatrix, cf_mul_two, cf_mapC_mul, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly,
    coeffMatrix_two_linearMatrixPoly, coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, one_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  rw [mul_comm t]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem coeffMatrix_zero_correctedLineGramPoly (t : ℂ) : cf 0 (GnP hm D Y t) = Dm hm D := by
  rw [GnP, cf_mul_zero, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, one_mul, mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem coeffMatrix_one_correctedLineGramPoly (t : ℂ) : cf 1 (GnP hm D Y t) = 0 := by
  rw [GnP, cf_mul_one, cf_mul_one, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, coeffMatrix_one_lineGramPoly]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.add_mul]
  abel

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem coeffMatrix_two_correctedLineGramPoly (t : ℂ) : cf 2 (GnP hm D Y t) =
    ((starRingEnd ℂ t) * t) • ((Yᴴ * Dc D * Y).submatrix (Fin.castLE hm) (Fin.castLE hm) -
      (Ym hm Y)ᴴ * Dm hm D * Ym hm Y) - t ^ 2 • (Dm hm D * Ym hm Y * Ym hm Y) -
      (starRingEnd ℂ t) ^ 2 • ((Ym hm Y)ᴴ * (Ym hm Y)ᴴ * Dm hm D) := by
  rw [GnP, cf_mul_two, cf_mul_two, cf_mul_one, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly,
    coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, coeffMatrix_one_lineGramPoly, coeffMatrix_two_lineGramPoly]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, smul_smul]
  module

def Gz (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((1 + ζ • Y)ᴴ * Dc D * (1 + ζ • Y)).submatrix (Fin.castLE hm) (Fin.castLE hm)

def Gnz (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (1 - ζ • Ym hm Y)ᴴ * (Gz hm D Y ζ * (1 - ζ • Ym hm Y))

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

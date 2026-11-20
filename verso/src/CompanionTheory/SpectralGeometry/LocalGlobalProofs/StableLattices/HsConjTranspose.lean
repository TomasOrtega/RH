import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineFacts
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport

noncomputable section

open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag

namespace GlobalTheory.CompanionTheory.UGeo

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

local notation "hs" => Formalism.REAL.hs

def Pz (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := 1 - A * A

def nsq (y : Fin n → ℂ) : ℝ := ∑ i, ‖y i‖ ^ 2

def tauG (A g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  -(1 / 2) * Real.log (Formalism.REAL.hs (g * Pm A) * (1 + Formalism.REAL.hs (g * Pz A)))

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem Pp_sub_Pm : Pp A - Pm A = A := by
  simp only [Pp, Pm, ← smul_sub]
  rw [show A * A + A - (A * A - A) = (2 : ℂ) • A by rw [two_smul]; abel, smul_smul]
  norm_num

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem Pp_add_Pm : Pp A + Pm A = A * A := by
  simp only [Pp, Pm, ← smul_add]
  rw [show A * A + A + (A * A - A) = (2 : ℂ) • (A * A) by rw [two_smul]; abel, smul_smul]
  norm_num

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem sum_proj : Pm A + Pz A + Pp A = 1 := by
  have := Pp_add_Pm (A := A)
  simp only [Pz]
  rw [← this]; abel

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem Pp_conj (hA : IsGrad ε A) : (Pp A)ᴴ = Pp A := by
  simp [Pp, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hA.2.1]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem Pz_conj (hA : IsGrad ε A) : (Pz A)ᴴ = Pz A := by
  simp [Pz, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA.2.1]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem four (hA : IsGrad ε A) : A * A * (A * A) = A * A := by
  have h := hA.2.2.1
  rw [← Matrix.mul_assoc, h]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem Pm_Pp (hA : IsGrad ε A) : Pm A * Pp A = 0 := by
  have h := Pp_Pm hA
  have := congrArg conjTranspose h
  rwa [conjTranspose_mul, Pm_conj hA, Pp_conj hA, conjTranspose_zero] at this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem A_Pm (hA : IsGrad ε A) : A * Pm A = -Pm A := by
  have h := hA.2.2.1
  have h4 := four hA
  simp only [Pm, Matrix.mul_smul, Matrix.mul_sub, ← Matrix.mul_assoc, h, ← smul_neg, neg_sub]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem A_Pp (hA : IsGrad ε A) : A * Pp A = Pp A := by
  have h := hA.2.2.1
  simp only [Pp, Matrix.mul_smul, Matrix.mul_add, ← Matrix.mul_assoc, h]
  rw [add_comm]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem Pm_idem (hA : IsGrad ε A) : Pm A * Pm A = Pm A := by
  have e := Pp_sub_Pm (A := A)
  have h1 : Pm A * (Pp A - Pm A) = - (Pm A * Pm A) := by
    rw [Matrix.mul_sub, Pm_Pp hA, zero_sub]
  have h2 : (Pp A - Pm A) * Pm A = -Pm A := by rw [e]; exact A_Pm hA
  rw [Matrix.sub_mul, Pp_Pm hA, zero_sub] at h2
  exact neg_injective h2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem Pp_idem (hA : IsGrad ε A) : Pp A * Pp A = Pp A := by
  have e := Pp_sub_Pm (A := A)
  have h2 : (Pp A - Pm A) * Pp A = Pp A := by rw [e]; exact A_Pp hA
  rwa [Matrix.sub_mul, Pm_Pp hA, sub_zero] at h2

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem Pz_eq : Pz A = 1 - Pm A - Pp A := by
  rw [← sum_proj (A := A)]; abel

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem Pz_Pm (hA : IsGrad ε A) : Pz A * Pm A = 0 := by
  rw [Pz_eq, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Pm_idem hA, Pp_Pm hA]; simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem Pm_Pz (hA : IsGrad ε A) : Pm A * Pz A = 0 := by
  rw [Pz_eq, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Pm_idem hA, Pm_Pp hA]; simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem Pz_Pp (hA : IsGrad ε A) : Pz A * Pp A = 0 := by
  rw [Pz_eq, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Pp_idem hA, Pm_Pp hA]; simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem Pp_Pz (hA : IsGrad ε A) : Pp A * Pz A = 0 := by
  rw [Pz_eq, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Pp_idem hA, Pp_Pm hA]; simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem Pz_idem (hA : IsGrad ε A) : Pz A * Pz A = Pz A := by
  have e : Pz A * Pz A = (1 - Pm A - Pp A) * Pz A := by rw [← Pz_eq]
  rw [e, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Pm_Pz hA, Pp_Pz hA]
  simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem A_Pz (hA : IsGrad ε A) : A * Pz A = 0 := by
  have e : A * Pz A = (Pp A - Pm A) * Pz A := by rw [Pp_sub_Pm]
  rw [e, Matrix.sub_mul, Pp_Pz hA, Pm_Pz hA, sub_zero]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem Pp_J (hA : IsGrad ε A) : Pp A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Pm A := by
  have h := Pm_J hA
  have := congrArg conjTranspose h
  simpa [conjTranspose_mul, Pm_conj hA, Pp_conj hA, Formalism.REAL.Jm_conjTranspose] using this.symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem Pz_J (hA : IsGrad ε A) : Pz A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Pz A := by
  rw [Pz_eq, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Pp_J hA, Pm_J hA, Matrix.one_mul,
    Matrix.mul_one]
  abel

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hs_nonneg (M : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs M := Formalism.REAL.frobenius_nonneg M

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hs_mul_le (M N : Matrix (Fin n) (Fin n) ℂ) : hs (M * N) ≤ hs M * hs N := Formalism.REAL.frobenius_mul_le M N

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem hs_eq_trace (M : Matrix (Fin n) (Fin n) ℂ) : hs M = (Matrix.trace (M * Mᴴ)).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : M i j * star (M i j) = ((‖M i j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, Complex.ofReal_re]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem hs_split {P : Matrix (Fin n) (Fin n) ℂ} (h1 : Pᴴ = P) (h2 : P * P = P) (M : Matrix (Fin n) (Fin n) ℂ) :
    hs M = hs (M * P) + hs (M * (1 - P)) := by
  have e1 : (M * P) * (M * P)ᴴ = M * P * Mᴴ := by
    rw [conjTranspose_mul, h1, Matrix.mul_assoc, ← Matrix.mul_assoc P, h2, Matrix.mul_assoc]
  have e2 : (M * (1 - P)) * (M * (1 - P))ᴴ = M * (1 - P) * Mᴴ := by
    have h3 : (1 - P) * (1 - P) = 1 - P := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h2]; abel
    rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, h1, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - P), h3,
      Matrix.mul_assoc]
  rw [hs_eq_trace, hs_eq_trace (M * P), hs_eq_trace (M * (1 - P)), e1, e2, ← Complex.add_re, ← Matrix.trace_add,
    ← Matrix.add_mul, ← Matrix.mul_add]
  simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hs_three (hA : IsGrad ε A) (M : Matrix (Fin n) (Fin n) ℂ) :
    hs M = hs (M * Pm A) + hs (M * Pz A) + hs (M * Pp A) := by
  have h1 := hs_split (Pm_conj hA) (Pm_idem hA) M
  have h2 := hs_split (Pp_conj hA) (Pp_idem hA) (M * (1 - Pm A))
  have e1 : M * (1 - Pm A) * Pp A = M * Pp A := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Pm_Pp hA, Matrix.one_mul, sub_zero]
  have e2 : M * (1 - Pm A) * (1 - Pp A) = M * Pz A := by
    rw [Matrix.mul_assoc, Pz_eq]
    congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Pm_Pp hA, sub_zero]
  rw [e1, e2] at h2
  linarith

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hs_smul (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : hs (c • M) = ‖c‖ ^ 2 * hs M := by
  simp only [Formalism.REAL.hs, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hs_conjTranspose (M : Matrix (Fin n) (Fin n) ℂ) : hs Mᴴ = hs M := by
  simp only [Formalism.REAL.hs, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem hs_add_le (M N : Matrix (Fin n) (Fin n) ℂ) : hs (M + N) ≤ 2 * hs M + 2 * hs N := by
  simp only [Formalism.REAL.hs, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h := norm_add_le (M i j) (N i j)
  have h1 : ‖(M + N) i j‖ ^ 2 ≤ (‖M i j‖ + ‖N i j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖M i j‖ - ‖N i j‖)]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem hs_J_mul (M : Matrix (Fin n) (Fin n) ℂ) : hs (Formalism.REAL.Jm ε * M) = hs M := by
  have h : ∀ a, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
  simp only [Formalism.REAL.hs, Formalism.REAL.Jm, Matrix.diagonal_mul, norm_mul, h, one_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem hs_mul_J (M : Matrix (Fin n) (Fin n) ℂ) : hs (M * Formalism.REAL.Jm ε) = hs M := by
  rw [← hs_conjTranspose, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose, hs_J_mul, hs_conjTranspose]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hs_one : hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  simp [Formalism.REAL.hs, Matrix.one_apply, apply_ite, Finset.sum_ite_eq]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hs_proj_le {P : Matrix (Fin n) (Fin n) ℂ} (h1 : Pᴴ = P) (h2 : P * P = P) : hs P ≤ n := by
  have := hs_split h1 h2 1
  rw [hs_one, Matrix.one_mul, Matrix.one_mul] at this
  linarith [hs_nonneg (1 - P)]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem hs_eq_zero {M : Matrix (Fin n) (Fin n) ℂ} (h : hs M = 0) : M = 0 := by
  ext i j
  have h1 : ∀ a ∈ Finset.univ, 0 ≤ ∑ b, ‖M a b‖ ^ 2 := fun a _ => Finset.sum_nonneg fun _ _ => by positivity
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg h1).1 h i (Finset.mem_univ _)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).1 h2 j (Finset.mem_univ _)
  simpa using h3

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hs_pos {M : Matrix (Fin n) (Fin n) ℂ} (h : M ≠ 0) : 0 < hs M :=
  lt_of_le_of_ne (hs_nonneg M) fun e => h (hs_eq_zero e.symm)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_le_hs {P : Matrix (Fin n) (Fin n) ℂ} (h2 : P * P = P) (h0 : P ≠ 0) : 1 ≤ hs P := by
  have h := hs_mul_le P P
  rw [h2] at h
  have hp := hs_pos h0
  nlinarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem Pm_ne_zero (hA : IsGrad ε A) : Pm A ≠ 0 := by
  intro h
  have h1 : Formalism.REAL.Jm ε * Pp A = 0 := by rw [← Pm_J hA, h, Matrix.zero_mul]
  have h2 : Pp A = 0 := by
    have := congrArg (Formalism.REAL.Jm ε * ·) h1
    simpa [← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self] using this
  exact hA.2.2.2 (by rw [← Pp_sub_Pm (A := A), h, h2, sub_zero])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem Pp_ne_zero (hA : IsGrad ε A) : Pp A ≠ 0 := by
  intro h
  have h1 : Formalism.REAL.Jm ε * Pm A = 0 := by rw [← Pp_J hA, h, Matrix.zero_mul]
  have h2 : Pm A = 0 := by
    have := congrArg (Formalism.REAL.Jm ε * ·) h1
    simpa [← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self] using this
  exact Pm_ne_zero hA h2

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem aT_mul_of_eigen {P : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (h : A * P = c • P) (t : ℝ) :
    aT A t * P = Complex.exp (t * c) • P := by
  ext i j
  have h1 : ((t : ℂ) • A) *ᵥ (fun k => P k j) = ((t : ℂ) * c) • (fun k => P k j) := by
    funext a
    have := congrFun (congrFun h a) j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc, ← Finset.mul_sum, this]
  have h2 := congrFun (GlobalTheory.CompanionTheory.GradLine.exp_mulVec_of_eigen h1) i
  simpa [aT, Matrix.mulVec, dotProduct, Matrix.mul_apply] using h2

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Reduce the equality to equality of the corresponding arguments.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem aT_Pm (hA : IsGrad ε A) (t : ℝ) : aT A t * Pm A = ((Real.exp (-t) : ℝ) : ℂ) • Pm A := by
  have h : A * Pm A = (-1 : ℂ) • Pm A := by rw [A_Pm hA]; simp
  rw [aT_mul_of_eigen h]
  congr 1
  push_cast
  congr 1
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Reduce the equality to equality of the corresponding arguments.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem aT_Pp (hA : IsGrad ε A) (t : ℝ) : aT A t * Pp A = ((Real.exp t : ℝ) : ℂ) • Pp A := by
  have h : A * Pp A = (1 : ℂ) • Pp A := by rw [A_Pp hA]; simp
  rw [aT_mul_of_eigen h]
  congr 1
  push_cast
  congr 1
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem aT_Pz (hA : IsGrad ε A) (t : ℝ) : aT A t * Pz A = Pz A := by
  have h : A * Pz A = (0 : ℂ) • Pz A := by rw [A_Pz hA]; simp
  rw [aT_mul_of_eigen h]
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem toM_inv_eq (x : S7.UJ ε) : (S7.toM x)⁻¹ = S7.toM x⁻¹ :=
  Matrix.inv_eq_right_inv (by
    show ((x : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * ((x⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = 1
    simp)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hs_Pp_inv (hA : IsGrad ε A) (x : S7.UJ ε) : hs (Pp A * S7.toM x⁻¹) = hs (S7.toM x * Pm A) := by
  rw [S7.toM_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  show hs (Pp A * Formalism.REAL.Jm ε * (S7.toM x)ᴴ * Formalism.REAL.Jm ε) = _
  rw [hs_mul_J, Pp_J hA, Matrix.mul_assoc, hs_J_mul, ← hs_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
    Pm_conj hA]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hs_Pz_inv (hA : IsGrad ε A) (x : S7.UJ ε) : hs (Pz A * S7.toM x⁻¹) = hs (S7.toM x * Pz A) := by
  rw [S7.toM_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  show hs (Pz A * Formalism.REAL.Jm ε * (S7.toM x)ᴴ * Formalism.REAL.Jm ε) = _
  rw [hs_mul_J, Pz_J hA, Matrix.mul_assoc, hs_J_mul, ← hs_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
    Pz_conj hA]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem toM_mul_ne_zero (x : S7.UJ ε) {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ≠ 0) : S7.toM x * P ≠ 0 := by
  intro h
  apply hP
  have h1 := congrArg (S7.toM x⁻¹ * ·) h
  have h2 : S7.toM x⁻¹ * S7.toM x = 1 := by
    show ((x⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val * ((x : (Matrix (Fin n) (Fin n) ℂ)ˣ)).val = 1
    simp
  simpa [← Matrix.mul_assoc, h2] using h1

end GlobalTheory.CompanionTheory.UGeo

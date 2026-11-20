import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.OffDiagUnitary

def Pm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun a => if ε a then 1 else 0

def Qm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun a => if ε a then 0 else 1

/- English proof (translation)
By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
lemma Pm_eq {n : ℕ} (ε : Fin n → Bool) : Pm ε = (1/2 : ℂ) • (1 + Jm ε) := by
  ext i j
  by_cases h : i = j
  · subst h; cases hε : ε i <;> simp [Pm, Jm, hε] <;> norm_num
  · simp [Pm, Jm, h, diagonal_apply_ne _ h, one_apply_ne h]

/- English proof (translation)
By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
lemma Qm_eq {n : ℕ} (ε : Fin n → Bool) : Qm ε = 1 - Pm ε := by
  ext i j
  by_cases h : i = j
  · subst h; cases hε : ε i <;> simp [Pm, Qm, hε]
  · simp [Pm, Qm, h, diagonal_apply_ne _ h, one_apply_ne h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma comm_Pm {n : ℕ} {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ}
    (h : a * Jm ε = Jm ε * a) : a * Pm ε = Pm ε * a := by
  rw [Pm_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, h,
    Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma comm_Qm {n : ℕ} {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ}
    (h : a * Jm ε = Jm ε * a) : a * Qm ε = Qm ε * a := by
  rw [Qm_eq, Matrix.mul_sub, Matrix.sub_mul, comm_Pm h, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
lemma sum_sq_norm_eq_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) = trace (Mᴴ * M) := by
  simp only [trace, diag, mul_apply, conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma trace_unitary_conj {n : ℕ} (a b h : Matrix (Fin n) (Fin n) ℂ) (ha : aᴴ * a = 1)
    (hb : bᴴ * b = 1) : trace ((a * h * b)ᴴ * (a * h * b)) = trace (hᴴ * h) := by
  have hb' : b * bᴴ = 1 := mul_eq_one_comm.mp hb
  have e : (a * h * b)ᴴ * (a * h * b) = bᴴ * ((hᴴ * h) * b) := by
    rw [conjTranspose_mul, conjTranspose_mul]
    calc bᴴ * (hᴴ * aᴴ) * (a * h * b) = bᴴ * (hᴴ * (aᴴ * a) * h * b) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, trace_mul_comm, Matrix.mul_assoc, hb', Matrix.mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma off_sum_eq {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2
      = ∑ i, ∑ j, ‖(Pm ε * M * Qm ε) i j‖ ^ 2 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun z : Fin n × Fin n => ε z.1 = true ∧ ε z.2 = false)
      (by simp) (fun z => ‖M z.1 z.2‖ ^ 2), Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pm, Qm, diagonal_mul, mul_diagonal]
  cases ε i <;> cases ε j <;> simp

end GlobalTheory.OffDiagUnitary

open GlobalTheory.OffDiagUnitary in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem GlobalTheory.offDiag_sum_sq_norm_unitary_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (a b g : Matrix (Fin n) (Fin n) ℂ), aᴴ * a = 1 → a * Jm ε = Jm ε * a → bᴴ * b = 1 → b * Jm ε = Jm ε * b → ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(a * g * b) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(g) z.1.1 z.1.2‖ ^ 2 := by
  intro n ε a b g ha haJ hb hbJ
  rw [off_sum_eq, off_sum_eq]
  have e : Pm ε * (a * g * b) * Qm ε = a * (Pm ε * g * Qm ε) * b := by
    calc Pm ε * (a * g * b) * Qm ε = (Pm ε * a) * g * (b * Qm ε) := by simp only [Matrix.mul_assoc]
      _ = (a * Pm ε) * g * (Qm ε * b) := by rw [comm_Pm haJ, comm_Qm hbJ]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  apply Complex.ofReal_injective
  rw [sum_sq_norm_eq_trace, sum_sq_norm_eq_trace, trace_unitary_conj _ _ _ ha hb]

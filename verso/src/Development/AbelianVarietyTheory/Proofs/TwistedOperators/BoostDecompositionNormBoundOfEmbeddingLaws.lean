import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPositiveBlockColumnEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIndefiniteUnitaryBoostHilbertSchmidtStatement

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.BoostHilbertSchmidtTrace

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem house : ∀ (m : ℕ) (ε : Fin m → Bool) (z : Fin m) (u : Fin m → ℂ), ε z = true → (∀ i, ε i = false → u i = 0) → ∑ i, ‖u i‖ ^ 2 = 1 → ∃ k ∈ UJset ε, kᴴ * k = 1 ∧ ∀ i, k i z = u i := GlobalTheory.T.exists_unitary_positiveBlock_column_eq

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem boostMat : ∀ (m : ℕ) (ε : Fin m → Bool) (a b : Fin m → ℂ), (∀ i, ε i = false → a i = 0) → (∀ i, ε i = true → b i = 0) → ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2 → ∃ A ∈ UJset ε, (∀ i, ∑ j, A i j * a j = (Real.sqrt (∑ j, ‖a j‖ ^ 2) : ℂ) * (a i + b i)) ∧ hsn A ^ 2 ≤ (m : ℝ) + 2 * ∑ i, ‖a i + b i‖ ^ 2 := GlobalTheory.T.exists_indefiniteUnitary_boost_hilbertSchmidt

end GlobalTheory.SepReal.BoostHilbertSchmidtTrace

namespace GlobalTheory.SepReal.BoostHilbertSchmidtTrace

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hsn_sq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : hsn M ^ 2 = ∑ a, ∑ b, ‖M a b‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem hsn_sq_eq_trace {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : ((hsn M ^ 2 : ℝ) : ℂ) = (M * Mᴴ).trace := by
  rw [hsn_sq, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.mul_conj']
  rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem hsn_mul_unitary {m : ℕ} (M U : Matrix (Fin m) (Fin m) ℂ) (hU : Uᴴ * U = 1) : hsn (M * U) = hsn M := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have h : ((hsn (M * U) ^ 2 : ℝ) : ℂ) = ((hsn M ^ 2 : ℝ) : ℂ) := by
    rw [hsn_sq_eq_trace, hsn_sq_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU', Matrix.one_mul]
  have h2 : hsn (M * U) ^ 2 = hsn M ^ 2 := by exact_mod_cast h
  have h0 : 0 ≤ hsn (M * U) := Real.sqrt_nonneg _
  have h1 : 0 ≤ hsn M := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (hsn (M * U) - hsn M), sq_nonneg (hsn (M * U) + hsn M)]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem inv_eq {m : ℕ} {ε : Fin m → Bool} {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ = Jm ε * gᴴ * Jm ε ∧ g * (Jm ε * gᴴ * Jm ε) = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hl : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Jm_mul_self]
  exact ⟨Matrix.inv_eq_left_inv hl, mul_eq_one_comm.mp hl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem inv_mem {m : ℕ} {ε : Fin m → Bool} {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UJset ε) : g⁻¹ ∈ UJset ε := by
  obtain ⟨hi, hr⟩ := inv_eq hg
  have hJ : g * Jm ε * gᴴ = Jm ε := by
    have := congrArg (· * Jm ε) hr
    simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Matrix.one_mul] at this
    simpa [Matrix.mul_assoc] using this
  show (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε
  rw [hi, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]
  calc Jm ε * (g * Jm ε) * Jm ε * (Jm ε * gᴴ * Jm ε) = Jm ε * (g * (Jm ε * Jm ε) * (Jm ε * gᴴ)) * Jm ε := by
        simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [Jm_mul_self, Matrix.mul_one, ← Matrix.mul_assoc g, hJ, Jm_mul_self, Matrix.one_mul]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem mul_mem {m : ℕ} {ε : Fin m → Bool} {g h : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) :
    g * h ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg', hh']

end GlobalTheory.SepReal.BoostHilbertSchmidtTrace

namespace GlobalTheory.SepReal.BoostHilbertSchmidtTrace

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem transit {m : ℕ} (ε : Fin m → Bool) (z : Fin m) (hz : ε z = true) (y : Fin m → ℂ)
    (hy : ∑ i, (if ε i then (1 : ℝ) else -1) * ‖y i‖ ^ 2 = 1) :
    ∃ c ∈ UJset ε, (∀ i, c i z = y i) ∧ hsn c ^ 2 ≤ (m : ℝ) + 2 * ∑ i, ‖y i‖ ^ 2 := by
  set a : Fin m → ℂ := fun i => if ε i then y i else 0 with ha
  set b : Fin m → ℂ := fun i => if ε i then 0 else y i with hb
  have hab : ∀ i, a i + b i = y i := fun i => by by_cases h : ε i <;> simp [ha, hb, h]
  have hn : ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2 := by
    rw [← hy, ← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : ε i <;> simp [ha, hb, h]
  have ha0 : ∀ i, ε i = false → a i = 0 := fun i h => by simp [ha, h]
  have hb0 : ∀ i, ε i = true → b i = 0 := fun i h => by simp [hb, h]
  set ch : ℝ := Real.sqrt (∑ j, ‖a j‖ ^ 2) with hch
  have hch1 : 1 ≤ ch := by
    rw [hch, Real.one_le_sqrt]
    rw [hn]; have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖b i‖); linarith
  have hch0 : (ch : ℂ) ≠ 0 := by exact_mod_cast (show ch ≠ 0 by linarith)
  set u : Fin m → ℂ := fun i => (ch : ℂ)⁻¹ * a i with hu
  have hu1 : ∑ i, ‖u i‖ ^ 2 = 1 := by
    have hs : ch ^ 2 = ∑ j, ‖a j‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    simp only [hu, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ch), mul_pow,
      ← Finset.mul_sum, ← hs, inv_pow]
    field_simp
  have hu0 : ∀ i, ε i = false → u i = 0 := fun i h => by simp [hu, ha0 i h]
  obtain ⟨k, hk, hkU, hkz⟩ := house m ε z u hz hu0 hu1
  obtain ⟨A, hA, hAa, hAn⟩ := boostMat m ε a b ha0 hb0 hn
  refine ⟨A * k, mul_mem hA hk, fun i => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    simp only [hkz, hu]
    have := hAa i
    rw [← hab i]
    calc ∑ j, A i j * ((ch : ℂ)⁻¹ * a j) = (ch : ℂ)⁻¹ * ∑ j, A i j * a j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ = a i + b i := by rw [this, ← hch]; field_simp
  · rw [hsn_mul_unitary A k hkU]
    simpa only [hab] using hAn

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
theorem col_inv_norm {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (hz : ε (e none) = true)
    (g : Mat (n + 1)) (hg : g ∈ UJset ε) :
    ∑ i, (if ε i then (1 : ℝ) else -1) * ‖g⁻¹ i (e none)‖ ^ 2 = 1 := by
  have h : (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε := inv_mem hg
  have h2 := congrFun (congrFun h (e none)) (e none)
  simp only [Matrix.mul_apply, Jm, Matrix.diagonal_apply, Matrix.conjTranspose_apply, hz, if_true] at h2
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  have h3 : ((∑ i, (if ε i then (1 : ℝ) else -1) * ‖g⁻¹ i (e none)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.mul_conj']
    by_cases hi : ε i <;> simp [hi] <;> ring
  exact_mod_cast h3

end GlobalTheory.SepReal.BoostHilbertSchmidtTrace

namespace GlobalTheory.SepReal

open BoostHilbertSchmidtTrace in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem boost_of_embLaws : EmbLaws → Boost := by
  intro hE n e ε ε' hS g hg
  obtain ⟨-, -, -, -, -, hstab, -, -, -, -, -, hinvn, -⟩ := hE n e ε ε' hS
  obtain ⟨c, hc, hcz, hcn⟩ := transit ε (e none) hS.1 (fun i => g⁻¹ i (e none)) (col_inv_norm e ε hS.1 g hg)
  have hgi : g * g⁻¹ = 1 := by rw [(inv_eq hg).1]; exact (inv_eq hg).2
  have hgc : g * c ∈ UJset ε := mul_mem hg hc
  have hcol : ∀ i, (g * c) i (e none) = if i = e none then 1 else 0 := fun i => by
    rw [Matrix.mul_apply]
    simp only [hcz]
    rw [← Matrix.mul_apply, hgi, Matrix.one_apply]
  obtain ⟨h, hh, hgh⟩ := hstab (g * c) hgc hcol
  have hci : c * c⁻¹ = 1 := by rw [(inv_eq hc).1]; exact (inv_eq hc).2
  refine ⟨h, hh, c⁻¹, inv_mem hc, ?_, ?_⟩
  · rw [← hgh, Matrix.mul_assoc, hci, Matrix.mul_one]
  · rw [(hinvn c hc).2, colLen, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simpa using hcn
end GlobalTheory.SepReal

end

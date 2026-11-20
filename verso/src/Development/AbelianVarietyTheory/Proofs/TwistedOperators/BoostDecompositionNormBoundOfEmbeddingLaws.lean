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
The claim follows from `GlobalTheory.T.exists_unitary_positiveBlock_column_eq`.
-/
theorem house : ∀ (m : ℕ) (ε : Fin m → Bool) (z : Fin m) (u : Fin m → ℂ), ε z = true → (∀ i, ε i = false → u i = 0) → ∑ i, ‖u i‖ ^ 2 = 1 → ∃ k ∈ UJset ε, kᴴ * k = 1 ∧ ∀ i, k i z = u i := GlobalTheory.T.exists_unitary_positiveBlock_column_eq

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_indefiniteUnitary_boost_hilbertSchmidt`.
-/
theorem boostMat : ∀ (m : ℕ) (ε : Fin m → Bool) (a b : Fin m → ℂ), (∀ i, ε i = false → a i = 0) → (∀ i, ε i = true → b i = 0) → ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2 → ∃ A ∈ UJset ε, (∀ i, ∑ j, A i j * a j = (Real.sqrt (∑ j, ‖a j‖ ^ 2) : ℂ) * (a i + b i)) ∧ hsn A ^ 2 ≤ (m : ℝ) + 2 * ∑ i, ‖a i + b i‖ ^ 2 := GlobalTheory.T.exists_indefiniteUnitary_boost_hilbertSchmidt

end GlobalTheory.SepReal.BoostHilbertSchmidtTrace

namespace GlobalTheory.SepReal.BoostHilbertSchmidtTrace

/- English proof (translation)
The claim follows from `Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)`.
-/
theorem hsn_sq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : hsn M ^ 2 = ∑ a, ∑ b, ‖M a b‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/- English proof (translation)
Rewrite using `[hsn_sq, Matrix.trace]`. Use `push_cast`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[← Complex.mul_conj']`. Both sides reduce to the same expression.
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
Establish `hU' : U * Uᴴ = 1` using `mul_eq_one_comm.mp hU`. Establish `h : ((hsn (M * U) ^ 2 : ℝ) : ℂ) = ((hsn M ^ 2 : ℝ) : ℂ)`. Rewrite using `[hsn_sq_eq_trace, hsn_sq_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU', Matrix.one_mul]`. Establish `h2 : hsn (M * U) ^ 2 = hsn M ^ 2` using `by exact_mod_cast h`. Establish `h0 : 0 ≤ hsn (M * U)` using `Real.sqrt_nonneg _`.

Establish `h1 : 0 ≤ hsn M` using `Real.sqrt_nonneg _`. Use polynomial arithmetic with `[sq_nonneg (hsn (M * U) - hsn M), sq_nonneg (hsn (M * U) + hsn M)]`.
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
Establish `hg' : gᴴ * Jm ε * g = Jm ε` using `hg`. Establish `hl : (Jm ε * gᴴ * Jm ε) * g = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Jm_mul_self]`. Conclude with `⟨Matrix.inv_eq_left_inv hl, mul_eq_one_comm.mp hl⟩`.
-/
theorem inv_eq {m : ℕ} {ε : Fin m → Bool} {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ = Jm ε * gᴴ * Jm ε ∧ g * (Jm ε * gᴴ * Jm ε) = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hl : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Jm_mul_self]
  exact ⟨Matrix.inv_eq_left_inv hl, mul_eq_one_comm.mp hl⟩

/- English proof (translation)
Take `⟨hi, hr⟩` from `inv_eq hg`. Establish `hJ : g * Jm ε * gᴴ = Jm ε`. Use `congrArg (· * Jm ε) hr` as an intermediate fact. Simplify using `only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Matrix.one_mul] at this`. Simplify `this` using `[Matrix.mul_assoc]`.

Use `show (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε`. Rewrite using `[hi, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Jm ε := by rw [Jm_mul_self, Matrix.mul_one, ← Matrix.mul_assoc g, hJ, Jm_mul_self, Matrix.one_mul]`.
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
Establish `hg' : gᴴ * Jm ε * g = Jm ε` using `hg`. Establish `hh' : hᴴ * Jm ε * h = Jm ε` using `hh`. Use `show (g * h)ᴴ * Jm ε * (g * h) = Jm ε`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
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
Use `set a : Fin m → ℂ := fun i => if ε i then y i else 0 with ha`. Use `set b : Fin m → ℂ := fun i => if ε i then 0 else y i with hb`. Apply the tactic sequence `have hab : ∀ i, a i + b i = y i := fun i => by by_cases h : ε i <;> simp [ha, hb, h]`. Establish `hn : ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2`. Rewrite using `[← hy, ← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : ε i <;> simp [ha, hb, h]`. Establish `ha0 : ∀ i, ε i = false → a i = 0` using `fun i h => by simp [ha, h]`. Establish `hb0 : ∀ i, ε i = true → b i = 0` using `fun i h => by simp [hb, h]`. Use `set ch : ℝ := Real.sqrt (∑ j, ‖a j‖ ^ 2) with hch`.

Establish `hch1 : 1 ≤ ch`. Rewrite using `[hch, Real.one_le_sqrt]`. Rewrite using `[hn]`. Use `Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖b i‖)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hch0 : (ch : ℂ) ≠ 0` using `by exact_mod_cast (show ch ≠ 0 by linarith)`. Use `set u : Fin m → ℂ := fun i => (ch : ℂ)⁻¹ * a i with hu`. Establish `hu1 : ∑ i, ‖u i‖ ^ 2 = 1`. Establish `hs : ch ^ 2 = ∑ j, ‖a j‖ ^ 2` using `Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)`. Simplify using `only [hu, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ch), mul_pow, ← Finset.mul_sum, ← hs, inv_pow]`.

Clear the denominators using the available nonvanishing facts. Establish `hu0 : ∀ i, ε i = false → u i = 0` using `fun i h => by simp [hu, ha0 i h]`. Take `⟨k, hk, hkU, hkz⟩` from `house m ε z u hz hu0 hu1`. Take `⟨A, hA, hAa, hAn⟩` from `boostMat m ε a b ha0 hb0 hn`. Use `⟨A * k, mul_mem hA hk, fun i => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hkz, hu]`. Use `hAa i` as an intermediate fact. Rewrite using `[← hab i]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring`. Use `_ = a i + b i := by rw [this, ← hch]; field_simp`. Rewrite using `[hsn_mul_unitary A k hkU]`. Simplify `hAn` using `only [hab]`.
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
Establish `h : (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε` using `inv_mem hg`. Establish `h2` using `congrFun (congrFun h (e none)) (e none)`. Simplify using `only [Matrix.mul_apply, Jm, Matrix.diagonal_apply, Matrix.conjTranspose_apply, hz, if_true] at h2`. Simplify using `only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2`. Establish `h3 : ((∑ i, (if ε i then (1 : ℝ) else -1) * ‖g⁻¹ i (e none)‖ ^ 2 : ℝ) : ℂ) = 1`.

Rewrite using `[← h2]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.mul_conj']`. Apply the tactic sequence `by_cases hi : ε i <;> simp [hi] <;> ring`.

Conclude with `h3` after adjusting the coercions.
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
Introduce `hE n e ε ε' hS g hg`. Take `⟨-, -, -, -, -, hstab, -, -, -, -, -, hinvn, -⟩` from `hE n e ε ε' hS`. Take `⟨c, hc, hcz, hcn⟩` from `transit ε (e none) hS.1 (fun i => g⁻¹ i (e none)) (col_inv_norm e ε hS.1 g hg)`. Establish `hgi : g * g⁻¹ = 1` using `by rw [(inv_eq hg).1]; exact (inv_eq hg).2`. Establish `hgc : g * c ∈ UJset ε` using `mul_mem hg hc`.

Establish `hcol : ∀ i, (g * c) i (e none) = if i = e none then 1 else 0` using `fun i => by`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hcz]`. Rewrite using `[← Matrix.mul_apply, hgi, Matrix.one_apply]`. Take `⟨h, hh, hgh⟩` from `hstab (g * c) hgc hcol`.

Establish `hci : c * c⁻¹ = 1` using `by rw [(inv_eq hc).1]; exact (inv_eq hc).2`. Use `⟨h, hh, c⁻¹, inv_mem hc, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hgh, Matrix.mul_assoc, hci, Matrix.mul_one]`. Rewrite using `[(hinvn c hc).2, colLen, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Simplify using `using hcn`.
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

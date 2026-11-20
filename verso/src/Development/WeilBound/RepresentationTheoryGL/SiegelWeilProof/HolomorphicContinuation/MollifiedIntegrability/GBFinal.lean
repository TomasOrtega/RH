import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Lagr

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm, star_add, star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem cls_zero (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    cls s 0 p q R = fun y => Fr s p q R (herm y) := by
  funext y
  simp [cls, Fr, evUV, uM, vM]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem herm_spectral (y : E n) : ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ lam : Fin n → ℝ,
    herm y = k * Matrix.diagonal (fun i => (lam i : ℂ)) * kᴴ := by
  have hH := herm_isHermitian y
  refine ⟨hH.eigenvectorUnitary, hH.eigenvectorUnitary.2, hH.eigenvalues, ?_⟩
  conv_lhs => rw [hH.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.
-/
theorem conj_det (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (A : Mc n) : (k * A * kᴴ).det = A.det := by
  have h1 : k * kᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (k.det), mul_assoc, ← Matrix.det_mul, h1, Matrix.det_one, mul_one]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.
-/
theorem one_sub_conj (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (c : ℂ) (A : Mc n) :
    (1 : Mc n) + c • (k * A * kᴴ) = k * (1 + c • A) * kᴴ := by
  have h1 : k * kᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem det_one_add_herm (y : E n) : ∃ lam : Fin n → ℝ, ∀ c : ℂ,
    ((1 : Mc n) + c • herm y).det = ∏ i, (1 + c * lam i) ∧ ((1 : Mc n) + herm y * herm y).det = ∏ i, (1 + (lam i : ℂ) ^ 2) := by
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  have h1 : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff'.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨lam, fun c => ⟨?_, ?_⟩⟩
  · rw [hy, one_sub_conj k hk, conj_det k hk]
    rw [show (1 : Mc n) + c • Matrix.diagonal (fun i => (lam i : ℂ)) = Matrix.diagonal (fun i => 1 + c * lam i) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h]]
    simp
  · have : herm y * herm y = k * (Matrix.diagonal (fun i => (lam i : ℂ)) * Matrix.diagonal (fun i => (lam i : ℂ))) * kᴴ := by
      rw [hy]
      calc k * diagonal (fun i => (lam i : ℂ)) * kᴴ * (k * diagonal (fun i => (lam i : ℂ)) * kᴴ)
          = k * diagonal (fun i => (lam i : ℂ)) * (kᴴ * k) * diagonal (fun i => (lam i : ℂ)) * kᴴ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, show (1 : Mc n) + k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ =
        (1 : Mc n) + (1 : ℂ) • (k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ) by simp,
      one_sub_conj k hk, conj_det k hk, Matrix.diagonal_mul_diagonal]
    rw [show (1 : Mc n) + (1 : ℂ) • diagonal (fun i => (lam i : ℂ) * lam i) = diagonal (fun i => 1 + (lam i : ℂ) ^ 2) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, sq]]
    simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.
-/
theorem dP_eq (y : E n) : ∃ lam : Fin n → ℝ, dP y = ∏ i, (1 + lam i ^ 2) ∧
    (((dP y : ℝ) : ℂ) = ((1 : Mc n) + herm y * herm y).det) ∧
    ∀ c : ℂ, ((1 : Mc n) + c • herm y).det = ∏ i, (1 + c * lam i) := by
  obtain ⟨lam, h⟩ := det_one_add_herm y
  have h2 := (h 0).2
  have hre : dP y = ∏ i, (1 + lam i ^ 2) := by
    simp only [dP, h2]
    rw [show (∏ i, (1 + (lam i : ℂ) ^ 2)) = ((∏ i, (1 + lam i ^ 2) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  refine ⟨lam, hre, ?_, fun c => (h c).1⟩
  rw [hre, h2]; push_cast; rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem dP_pos (y : E n) : 0 < dP y := by
  obtain ⟨lam, h, -⟩ := dP_eq y
  rw [h]; exact Finset.prod_pos fun i _ => by positivity

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem herm_mem_Ugood (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : herm y ∈ Ugood s := by
  obtain ⟨lam, -, -, h⟩ := dP_eq y
  have key : ∀ c : ℂ, (c = 1 ∨ c = -1) → ((1 : Mc n) + (c * (Complex.I * s)) • herm y).det ≠ 0 := by
    intro c hc
    rw [h, Finset.prod_ne_zero_iff]
    intro i _ h0
    have h1 := congrArg Complex.re h0
    rcases hc with rfl | rfl <;> rcases hs with rfl | rfl <;> simp at h1
  refine ⟨isUnit_iff_ne_zero.2 ?_, isUnit_iff_ne_zero.2 ?_⟩
  · have := key (-1) (Or.inr rfl); rwa [neg_one_mul, neg_smul, ← sub_eq_add_neg] at this
  · have := key 1 (Or.inl rfl); rwa [one_mul] at this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dP_of_spectral (y : E n) (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (lam : Fin n → ℝ)
    (hy : herm y = k * Matrix.diagonal (fun i => (lam i : ℂ)) * kᴴ) : dP y = ∏ i, (1 + lam i ^ 2) := by
  have h1 : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff'.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  have : herm y * herm y = k * (Matrix.diagonal (fun i => (lam i : ℂ)) * Matrix.diagonal (fun i => (lam i : ℂ))) * kᴴ := by
    rw [hy]
    calc k * diagonal (fun i => (lam i : ℂ)) * kᴴ * (k * diagonal (fun i => (lam i : ℂ)) * kᴴ)
        = k * diagonal (fun i => (lam i : ℂ)) * (kᴴ * k) * diagonal (fun i => (lam i : ℂ)) * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h2 : ((1 : Mc n) + herm y * herm y).det = ((∏ i, (1 + lam i ^ 2) : ℝ) : ℂ) := by
    rw [this, show (1 : Mc n) + k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ =
        (1 : Mc n) + (1 : ℂ) • (k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ) by simp,
      one_sub_conj k hk, conj_det k hk, Matrix.diagonal_mul_diagonal]
    rw [show (1 : Mc n) + (1 : ℂ) • diagonal (fun i => (lam i : ℂ) * lam i) = diagonal (fun i => 1 + (lam i : ℂ) ^ 2) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, sq]]
    simp
  simp only [dP, h2, Complex.ofReal_re]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation.
-/
theorem det_u_mul_det_v (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) :
    (uM s y).det * (vM s y).det = (((dP y : ℝ) : ℂ))⁻¹ := by
  obtain ⟨lam, -, hdP, -⟩ := dP_eq y
  have hg := herm_mem_Ugood s hs y
  have hprod : ((1 : Mc n) - (Complex.I * s) • herm y) * (1 + (Complex.I * s) • herm y) = 1 + herm y * herm y := by
    have hs2 : (Complex.I * s) * (Complex.I * s) = -1 := by
      rcases hs with rfl | rfl <;> simp [← sq, Complex.I_sq] <;> ring_nf <;> simp [Complex.I_sq]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs2]
    simp [neg_smul]; abel
  have h1 := Matrix.det_nonsing_inv_mul_det (A := (1 : Mc n) - (Complex.I * s) • herm y) hg.1
  have h2 := Matrix.det_nonsing_inv_mul_det (A := (1 : Mc n) + (Complex.I * s) • herm y) hg.2
  rw [hdP, ← hprod, Matrix.det_mul]
  simp only [uM, vM]
  apply eq_inv_of_mul_eq_one_left
  calc ((1 - (Complex.I * s) • herm y)⁻¹).det * ((1 + (Complex.I * s) • herm y)⁻¹).det *
        ((1 - (Complex.I * s) • herm y).det * (1 + (Complex.I * s) • herm y).det)
      = (((1 - (Complex.I * s) • herm y)⁻¹).det * (1 - (Complex.I * s) • herm y).det) *
        (((1 + (Complex.I * s) • herm y)⁻¹).det * (1 + (Complex.I * s) • herm y).det) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cls_nat (s : ℂ) (hs : s = 1 ∨ s = -1) (i p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    cls s (i : ℂ) p q R = cls s 0 (p + i) (q + i) R := by
  funext y
  have h := det_u_mul_det_v s hs y
  simp only [cls, neg_zero, Complex.cpow_zero, one_mul, Complex.cpow_neg, Complex.cpow_natCast, pow_add]
  rw [show ((((dP y : ℝ) : ℂ)) ^ i)⁻¹ = ((uM s y).det * (vM s y).det) ^ i by rw [h, inv_pow]]
  ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem prod_flatMap_real {α : Type} (l : List α) (f : α → List ℝ) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.
-/
theorem prod_blocks (N : ℕ) (g : Fin N → Fin n → ℝ) :
    ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => g j k).prod = ∏ j, ∏ k, g j k := by
  rw [prod_flatMap_real, Fin.prod_univ_def]
  congr 1

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem length_blocks {α : Type} (N : ℕ) (g : Fin N → Fin n → α) :
    ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => g j k).length = N * n := by
  simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
-/
theorem prod_sqrt_perm (σ : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∏ k, Real.sqrt (w (σ k) * w k) = ∏ k, w k := by
  have h1 : ∀ k, Real.sqrt (w (σ k) * w k) = Real.sqrt (w (σ k)) * Real.sqrt (w k) := fun k =>
    Real.sqrt_mul (hw _).le _
  simp_rw [h1, Finset.prod_mul_distrib, Equiv.prod_comp σ (fun k => Real.sqrt (w k)), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => Real.mul_self_sqrt (hw k).le

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conj_mem_Ugood (s : ℂ) (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (b : Mc n) (hb : b ∈ Ugood s) :
    k * b * kᴴ ∈ Ugood s := by
  refine ⟨?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul, one_sub_conj k hk, conj_det k hk, neg_smul, ← sub_eq_add_neg]; exact hb.1
  · rw [one_sub_conj k hk, conj_det k hk]; exact hb.2

def conjL (k : Mc n) : Mc n →ₗ[ℂ] Mc n := (LinearMap.mulLeft ℂ k).comp (LinearMap.mulRight ℂ kᴴ)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem conjL_apply (k c : Mc n) : conjL k c = k * c * kᴴ := by
  simp [conjL, Matrix.mul_assoc]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem contDiff_conj (k : Mc n) : ContDiff ℂ (⊤ : ℕ∞) (fun c : Mc n => k * c * kᴴ) := by
  have : (fun c : Mc n => k * c * kᴴ) = (LinearMap.toContinuousLinearMap (conjL k) : Mc n → Mc n) := by
    funext c; simp [conjL_apply]
  rw [this]; exact ContinuousLinearMap.contDiff _

end PositivityTheory.Rg.Sw.WR.K.GB

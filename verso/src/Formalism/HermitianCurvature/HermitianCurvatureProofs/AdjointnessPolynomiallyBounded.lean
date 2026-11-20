import Formalism.HermitianCurvature.StatementB

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

namespace B2

/- English proof (translation)
Replace the relevant objects with their definitions. Check the signs of the components of the expression.
-/
theorem AB_nonneg (k r : ℕ) : (0 : ℝ) ≤ AB k r := by
  unfold AB
  positivity

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem aDil_inv (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (aDil k r t)⁻¹ = aDil k r t⁻¹ := by
  have hp : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht
  apply Matrix.inv_eq_left_inv
  unfold aDil
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs with h1 h2
  · rw [← Complex.ofReal_mul, inv_pow, inv_mul_cancel₀ (hp _), Complex.ofReal_one]
  · exact mul_one 1
  · rw [← Complex.ofReal_mul, inv_pow, inv_inv, mul_inv_cancel₀ (hp _), Complex.ofReal_one]

end B2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Supply the required witnesses or components.
-/
theorem bessel_lemma_from_reductions : Formalism.FourierDecayAlt.B.LemmaBFromSteps := by
  intro hFC hAe hFat hCC hDil hJ hRB hRA hU hJC hDB hPA hRP hEq hAdj
  unfold StepRegBound StepRegAverage StepUnfold StepJCont StepDilBeta at *
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A hA hInt hConj hDJ hCCI hCoef hXi
  have h0A : 0 ≤ A := (B2.AB_nonneg k r).trans hA
  have h12 := hEq hFC hAe hFat hCC hDil hJ k r Wp Wq D A h0A
    (by apply hRB <;> assumption) (by apply hRA <;> assumption) (by apply hU <;> assumption)
    (by apply hJC <;> assumption) (by apply hDB <;> assumption)
  exact ⟨h12.1, h12.2, hAdj hPA hRP k r Wp Wq D A h12.2⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem adjointness_of_bessel_transform : Formalism.FourierDecayAlt.B.AssembleAdj := by
  intro hPA hRP k r Wp Wq _ _ _ _ _ _ D A hB2 UU Θ hStab hSm hCom F F' hCk hCk' hS hS' h1 h2 h3 h4 hIC
  have hT : ∀ τ, betaInfTau D τ (opApply Θ F) F' = betaInfTau D τ F (opAdj Θ F') := fun τ =>
    hRP k r Wp Wq D τ _ _ _ _ (hPA k r Wp Wq D UU Θ hStab hSm hCom F F' hCk hCk' hS hS' hIC)
  rw [hB2 _ _ h3 h2, hB2 _ _ h1 h4]
  first
  | (unfold betaInf; simp only [hT])
  | (simp only [betaInf, hT])
  | (unfold betaInf; rw [hT])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem adjointness_polynomially_bounded : Formalism.FourierDecayAlt.B.AssemblePoly := by
  intro hSC k r Wp Wq _ _ _ _ _ _ D A hA hCC hB3 Θ ε d hε hd hSm hCom hPoly F F' hF hF' hsF hsF'
  obtain ⟨hStab, hcl⟩ := hSC k r Wp Wq D A hA hCC
  obtain ⟨hs1, hs2, h1, h2, h3, h4, hIC⟩ := hcl Θ ε d hε hd hSm hPoly F F' hF hF' hsF hsF'
  have hCk : ∀ G : Mat k r → (Wq →L[ℂ] Wp), InCC (A + d) (opOrder Θ + 5) G →
      CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) G := by
    intro G hG
    obtain ⟨c, hc⟩ := hG
    unfold CCle at hc
    first
    | exact hc.1
    | exact hc.2.1
    | exact hc.2.2.1
    | exact hc.1.1
    | exact hc
  exact hB3 (GPos D) Θ hStab hSm hCom F F' (hCk F hF) (hCk F' hF') hs1 hs2 h1 h2 h3 h4 hIC

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Reduce the equality to equality of the corresponding arguments. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Simplify by unfolding definitions. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem bessel_function_trivial_index : Formalism.FourierDecayAlt.B.JtauOne := by
  unfold Formalism.FourierDecayAlt.B.JtauOne
  intro k r Wp Wq _ _ _ _ D F g
  unfold Jtau JF xiTau besselJ RealPlaceData.μSS
  unfold rho sgs
  congr 1
  funext p
  congr 1
  unfold psi cStd
  have hs : ∀ z : ℂ, star (Complex.exp z) = Complex.exp ((starRingEnd ℂ) z) :=
    fun z => (Complex.exp_conj z).symm
  rw [hs, ← Complex.exp_add]
  congr 1
  try unfold lam
  dsimp only
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, one_mul]
  try unfold cStd
  ring_nf
  push_cast
  ring

/- English proof (translation)
A detailed English derivation is pending.
-/
private lemma star_ofReal_eq (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

A detailed English derivation is pending.
-/
theorem dilation_big_cell_formula : Formalism.FourierDecayAlt.B.DilBigCell := by
  unfold Formalism.FourierDecayAlt.B.DilBigCell
  intro k r c μ t₁ t₂ h1 h2
  rw [B2.aDil_inv k r t₁ h1]
  unfold aDil
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold bigCell esI
  beta_reduce
  split_ifs
  all_goals try first
    | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega)
    | rfl
    | (rw [one_mul, mul_one])
    | exact (congrArg (· * (1 : ℂ)) (one_mul _)).trans (mul_one _)
    | (simp; done)
    | (have e : (i : ℕ) - (r + k) = r - (j : ℕ) := by
          (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega
       rw [e]
       try simp only [Fin.val_mk]
       push_cast
       simp only [inv_pow, inv_inv]
       ring)
    | (have e1 : r - (i : ℕ) = (j : ℕ) - (r + k) := by
          (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega
       have e2 : r - (2 * r + k - (j : ℕ)) = (j : ℕ) - (r + k) := by omega
       simp only [Fin.val_mk, e1, e2, star_mul', star_ofReal_eq]
       push_cast
       ring)

/- English proof (translation)
A detailed English derivation is pending.
-/
private lemma star_ofReal_eq_self (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem dilation_mem_group : Formalism.FourierDecayAlt.B.DilMem := by
  unfold Formalism.FourierDecayAlt.B.DilMem
  intro k r t ht
  have hp : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht
  unfold GV UH aDil
  rw [Set.mem_setOf_eq, Matrix.diagonal_conjTranspose]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  unfold Hpk
  beta_reduce
  split_ifs
  all_goals (try simp only [star_ofReal_eq_self, star_one, mul_one, one_mul, mul_zero, zero_mul, mul_neg])
  all_goals try first
    | rfl
    | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega)
    | (rw [show (j : ℕ) - (r + k) = r - (i : ℕ) by omega, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (hp _), Complex.ofReal_one])
    | (rw [show (i : ℕ) - (r + k) = r - (j : ℕ) by omega, ← Complex.ofReal_mul,
          inv_mul_cancel₀ (hp _), Complex.ofReal_one])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem bessel_lemma_closed_form : Formalism.FourierDecayAlt.B.LemmaBClosedFromParts := by
  intro hXi hLB hSC hAP k r Wp Wq _ _ _ _ _ _ D A hA hInt hConj hDJ hCCI
  obtain ⟨Ξ, hCB, hXI⟩ := hXi k r Wp Wq D A hA
  have h0A : 0 ≤ A := (B2.AB_nonneg k r).trans hA
  obtain ⟨h1, h2, h3⟩ := hLB k r Wp Wq D Ξ A hA hInt hConj hDJ hCCI hCB hXI
  exact ⟨h1, h2, h3, hAP hSC k r Wp Wq D A h0A hCCI h3⟩

end Formalism.FourierDecayAlt.P

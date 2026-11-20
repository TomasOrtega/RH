import Mathlib

open Matrix

open scoped MatrixOrder ComplexOrder in
/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.frame_pos {N j : ℕ} (S : Matrix (Fin N) (Fin N) ℂ)
    (K : Submodule ℂ (Fin N → ℂ)) (hS : S.IsHermitian) (hj : j ≤ Module.finrank ℂ K)
    (hK : ∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) :
    ∃ B : Matrix (Fin N) (Fin j) ℂ, Bᴴ * S * B = 1 ∧ ∀ v, B.mulVec v ∈ K := by
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank hj
  have hb' : LinearIndependent ℂ (fun i => (b i : Fin N → ℂ)) :=
    hb.map' K.subtype (Submodule.ker_subtype K)
  let C : Matrix (Fin N) (Fin j) ℂ := Matrix.of fun r i => (b i : Fin N → ℂ) r
  have hC : ∀ v, C.mulVec v = ∑ i, v i • (b i : Fin N → ℂ) := by
    intro v
    ext r
    simp [C, Matrix.mulVec, dotProduct, mul_comm]
  have hmem : ∀ v, C.mulVec v ∈ K := fun v => by
    rw [hC]
    exact K.sum_mem fun i _ => K.smul_mem _ (b i).2
  have hne : ∀ v, v ≠ 0 → C.mulVec v ≠ 0 := fun v hv h => by
    rw [hC] at h
    exact hv (funext (Fintype.linearIndependent_iff.mp hb' v h))
  have hH : (Cᴴ * S * C).IsHermitian := isHermitian_conjTranspose_mul_mul C hS
  have hG : (Cᴴ * S * C).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have h1 := hK _ (hmem x) (hne x hx)
    have h2 := hH.im_star_dotProduct_mulVec_self x
    have h3 : star x ⬝ᵥ (Cᴴ * S * C) *ᵥ x = star (C *ᵥ x) ⬝ᵥ S *ᵥ C *ᵥ x := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
    rw [← h3] at h1
    exact Complex.pos_iff.mpr ⟨h1, Eq.symm h2⟩
  obtain ⟨D, hD, hGD⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  obtain ⟨E, hE⟩ := hD.exists_right_inv
  refine ⟨C * E, ?_, fun v => ?_⟩
  · calc (C * E)ᴴ * S * (C * E) = Eᴴ * (Cᴴ * S * C) * E := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (D * E)ᴴ * (D * E) := by
          rw [hGD, star_eq_conjTranspose]
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hE]; simp
  · rw [← mulVec_mulVec]
    exact hmem _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.
-/
theorem UpperTheory.signature_block_diagonal :
    ∀ {N j j' : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (K K' : Submodule ℂ (Fin N → ℂ)),
        S.IsHermitian → j ≤ Module.finrank ℂ K → j' ≤ Module.finrank ℂ K' →
        (∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) →
        (∀ y ∈ K', y ≠ 0 → (dotProduct (star y) (S.mulVec y)).re < 0) →
        (∀ y ∈ K, ∀ y' ∈ K', dotProduct (star y') (S.mulVec y) = 0) →
        ∃ A : Matrix (Fin N) (Fin j ⊕ Fin j') ℂ,
          A.conjTranspose * S * A = Matrix.fromBlocks 1 0 0 (-1) ∧
          (∀ v : Fin j → ℂ, A.mulVec (Sum.elim v (0 : Fin j' → ℂ)) ∈ K) ∧
          ∀ v : Fin j' → ℂ, A.mulVec (Sum.elim (0 : Fin j → ℂ) v) ∈ K' := by
  intro N j j' S K K' hS hj hj' hK hK' hO
  obtain ⟨B, hB, hBK⟩ := UpperTheory.frame_pos S K hS hj hK
  obtain ⟨B', hB', hBK'⟩ := UpperTheory.frame_pos (-S) K' hS.neg hj' (fun y hy h0 => by
    have := hK' y hy h0
    simpa [neg_mulVec] using this)
  have h22 : B'ᴴ * S * B' = -1 := by
    rw [← hB']
    simp
  have h21 : B'ᴴ * S * B = 0 := by
    ext a c
    have h := hO _ (hBK (Pi.single c 1)) _ (hBK' (Pi.single a 1))
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec] at h
    simpa [← Pi.single_star] using h
  have h12 : Bᴴ * S * B' = 0 := by
    have h := congrArg conjTranspose h21
    simpa [conjTranspose_mul, hS.eq, Matrix.mul_assoc] using h
  refine ⟨fromCols B B', ?_, fun v => ?_, fun v => ?_⟩
  · rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols,
      hB, h12, h21, h22]
  · simpa using hBK v
  · simpa using hBK' v

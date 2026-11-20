import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootAnchorNonzeroAlt

/- English proof (translation)
Establish an intermediate fact. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem anchorMinor_eq_one {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  have he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 =
      Fin.castLEOrderEmb (Nat.le_add_right j m) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨x, rfl⟩
  have : colsOf (onePipe Z) (plAnchor j m) = 1 := by
    ext a b
    simp only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]
    have : (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b := rfl
    rw [this, Fin.append_left]
  rw [this, Matrix.det_one]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Replace the chosen expression with an arbitrary variable. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem rootCoord_isIntegral {f j m : ℕ} {ζ : Fin f → Matrix (Fin j) (Fin m) ℂ} (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  classical
  apply IsIntegral.det
  intro a b
  simp only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]
  generalize p.2.1.orderEmbOfFin p.2.2 b = c
  refine Fin.addCases (fun c => ?_) (fun c => ?_) c
  · rw [Fin.append_left]
    by_cases h : a = c
    · subst h; rw [Matrix.one_apply_eq]; exact isIntegral_one
    · rw [Matrix.one_apply_ne h]; exact isIntegral_zero
  · rw [Fin.append_right]
    obtain ⟨k, hk, hpow⟩ := hζ p.1 a c
    exact IsIntegral.of_pow hk (by rw [hpow]; exact isIntegral_one)

def homForm {f j m : ℕ} (q : Polynomial ℤ) (τ : Fin f) (I : PlIdx j m) : MRing (plBlocks f j m) :=
  ∑ k ∈ Finset.range (q.natDegree + 1),
    C (q.coeff k) * X ⟨τ, I⟩ ^ k * X ⟨τ, plAnchor j m⟩ ^ (q.natDegree - k)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem homForm_mem {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (q : Polynomial ℤ) (τ : Fin f)
    (I : PlIdx j m) (hq : Polynomial.aeval (rootCoord ζ ⟨τ, I⟩) q = 0) :
    homForm q τ I ∈ rootPointIdeal ζ := by
  show mConeMap (rootCoord ζ) (homForm q τ I) = 0
  have hA : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1 := anchorMinor_eq_one j m (ζ τ)
  simp only [homForm, mConeMap, map_sum, map_mul, map_pow, aeval_X, aeval_C, hA, map_one, one_mul]
  rw [Polynomial.aeval_eq_sum_range] at hq
  calc _ = ∑ k ∈ Finset.range (q.natDegree + 1),
        C (q.coeff k • rootCoord ζ ⟨τ, I⟩ ^ k) * (X τ : MvPolynomial (Fin f) ℂ) ^ q.natDegree := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [← pow_mul_pow_sub (X τ : MvPolynomial (Fin f) ℂ) hk', zsmul_eq_mul, map_mul, map_pow,
          eq_intCast, map_intCast, mul_pow]
        ring
    _ = 0 := by rw [← Finset.sum_mul, ← map_sum, hq, map_zero, zero_mul]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules.
-/
theorem eval_homForm {f j m : ℕ} {q : Polynomial ℤ} (hq : q.Monic) {τ : Fin f} {I : PlIdx j m}
    {z : (Σ _ : Fin f, PlIdx j m) → ℂ} (hz : z ⟨τ, plAnchor j m⟩ = 0) :
    eval z (map (Int.castRingHom ℂ) (homForm q τ I)) = z ⟨τ, I⟩ ^ q.natDegree := by
  simp only [homForm, map_sum, map_mul, map_pow, map_C, map_X, eval_C, eval_X, hz]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp [hq.coeff_natDegree]
  · intro k hk
    have : q.natDegree - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
    simp [zero_pow this]

end RootAnchorNonzeroAlt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem RootAnchorNonzero.proof : RootAnchorNonzero.Statement := by
  intro f j m ζ hζ z hz τ h0
  obtain ⟨I, hI⟩ := hz.1 τ
  obtain ⟨q, hqm, hq⟩ := RootAnchorNonzeroAlt.rootCoord_isIntegral hζ ⟨τ, I⟩
  have hmem := RootAnchorNonzeroAlt.homForm_mem ζ q τ I (by rwa [Polynomial.aeval_def])
  have h := hz.2 _ hmem
  rw [RootAnchorNonzeroAlt.eval_homForm hqm h0] at h
  exact hI (pow_eq_zero_iff'.mp h).1

end

end GroundTheory.Heights₂.Heights

import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Wedge

/- English proof (translation)
Use extensionality with `j l`. Distinguish the cases in `h : j = k`. Substitute `h` using the available equality. Simplify using `[Matrix.updateRow_apply, Function.update_self]`. Simplify using `[Matrix.updateRow_apply, h, Function.update_of_ne h]`.
-/
theorem updateRow_submatrix_eq {K ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ K) (s : κ → ι) (k : κ) (i : ι) :
    (U.submatrix s id).updateRow k (U i) = U.submatrix (Function.update s k i) id := by
  ext j l
  by_cases h : j = k
  · subst h
    simp [Matrix.updateRow_apply, Function.update_self]
  · simp [Matrix.updateRow_apply, h, Function.update_of_ne h]

/- English proof (translation)
Use extensionality with `i l`. Rewrite using `[Matrix.mul_apply]`. Establish `key : ∀ k, (U.submatrix (Function.update s k i) id).det = Matrix.cramer (U.submatrix s id).transpose (U i) k`. Introduce `k`. Rewrite using `[← updateRow_submatrix_eq, Matrix.cramer_apply, Matrix.updateCol_transpose, Matrix.det_transpose]`.

Establish `hv` using `Matrix.mulVec_cramer (U.submatrix s id).transpose (U i)`. Rewrite `hv` using `[Matrix.mulVec_transpose, Matrix.det_transpose]`. Establish `hl` using `congrFun hv l`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hl`. Simplify using `only [Matrix.of_apply, key, mul_assoc]`.

Rewrite using `[← Finset.mul_sum, hl, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]`.
-/
theorem eq_mul_of_det_ne_zero {K ι κ : Type} [Field K] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ K) (s : κ → ι) (hd : (U.submatrix s id).det ≠ 0) :
    U = (Matrix.of fun i k => (U.submatrix s id).det⁻¹ *
      (U.submatrix (Function.update s k i) id).det) * U.submatrix s id := by
  ext i l
  rw [Matrix.mul_apply]
  have key : ∀ k, (U.submatrix (Function.update s k i) id).det
      = Matrix.cramer (U.submatrix s id).transpose (U i) k := by
    intro k
    rw [← updateRow_submatrix_eq, Matrix.cramer_apply, Matrix.updateCol_transpose,
      Matrix.det_transpose]
  have hv := Matrix.mulVec_cramer (U.submatrix s id).transpose (U i)
  rw [Matrix.mulVec_transpose, Matrix.det_transpose] at hv
  have hl := congrFun hv l
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hl
  simp only [Matrix.of_apply, key, mul_assoc]
  rw [← Finset.mul_sum, hl, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/- English proof (translation)
Introduce `hM`. Unfold `PairF`. Introduce `K ι κ _ _ _ _ _ U W`. Establish `hsz0 : ∀ {a b : Type} (g : Matrix a b K), 0 ≤ sz g`. Introduce `a b g`.

Unfold `sz`. Conclude with `Real.iSup_nonneg (fun p => norm_nonneg _)`. Establish `hnF0 : ∀ (X : Matrix ι κ K), 0 ≤ nF X`. Introduce `X`. Unfold `nF`.

Conclude with `Real.iSup_nonneg (fun s => norm_nonneg _)`. Establish `hdetT : (Uᵀ * W).det = (Wᵀ * U).det`. Rewrite using `[← Matrix.det_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]`. Distinguish the cases in `h : ∃ s : κ → ι, (U.submatrix s id).det ≠ 0`. Use `haveI : Nonempty (κ → ι) := ⟨h.choose⟩`.

Take `⟨s₀, hs₀⟩` from `Finite.exists_max (fun s : κ → ι => ‖(U.submatrix s id).det‖)`. Establish `hd : (U.submatrix s₀ id).det ≠ 0`. Take `⟨s, hs⟩` from `h`. Introduce `h0`. Establish `h1` using `hs₀ s`.

Simplify using `only [h0, norm_zero] at h1`. Conclude with `hs (norm_le_zero_iff.mp h1)`. Establish `hnU : nF U = ‖(U.submatrix s₀ id).det‖`. Unfold `nF`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `ciSup_le hs₀`. Conclude with `le_ciSup (f := fun s : κ → ι => ‖(U.submatrix s id).det‖) (Set.finite_range _).bddAbove s₀`. Use `set G : Matrix ι κ K := Matrix.of fun i k => (U.submatrix s₀ id).det⁻¹ * (U.submatrix (Function.update s₀ k i) id).det with hG`. Establish `hUG : U = G * U.submatrix s₀ id` using `eq_mul_of_det_ne_zero U s₀ hd`. Establish `hszG : sz Gᵀ ≤ 1`.

Unfold `sz`. Apply `Real.iSup_le ?_ zero_le_one` to reduce the goal to its premises. Introduce `p`. Simplify using `only [Matrix.transpose_apply, hG, Matrix.of_apply, norm_mul, norm_inv]`. Rewrite using `[inv_mul_le_iff₀ (norm_pos_iff.mpr hd), mul_one]`.

Conclude with `hs₀ _`. Establish `hmain : ‖(Gᵀ * W).det‖ ≤ nF W`. Establish `h1` using `(hM K ι κ κ W).1 Gᵀ`. Establish `h2` using `(hM K ι κ κ W).2.2 (Gᵀ * W)`. Rewrite `h1` using `[h2]`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (hnF0 W)` to reduce the goal to its premises. Conclude with `pow_le_one₀ (hsz0 _) hszG`. Use `_ = nF W := one_mul _`. Establish `hfac : (Uᵀ * W).det = (U.submatrix s₀ id).det * (Gᵀ * W).det` using `by conv_lhs => rw [hUG]`.

Rewrite using `[Matrix.transpose_mul, Matrix.mul_assoc, Matrix.det_mul, Matrix.det_transpose]`. Rewrite using `[hfac, norm_mul, hnU]`. Conclude with `mul_le_mul_of_nonneg_left hmain (norm_nonneg _)`. Simplify using `only [not_exists, not_not] at h`. Establish `hnU : nF U = 0`.

Unfold `nF`. Simplify using `only [h, norm_zero]`. Use `first`. Consider the case `exact Real.iSup_const_zero`. Consider the case `simp`.

Establish `h1` using `(hM K ι κ κ U).1 Wᵀ`. Establish `h2` using `(hM K ι κ κ U).2.2 (Wᵀ * U)`. Rewrite `h1` using `[h2, hnU, mul_zero]`. Rewrite using `[hdetT, hnU, zero_mul]`. Conclude with `h1`.
-/
theorem pairF_of_mulF : MulF → PairF := by
  intro hM
  unfold PairF
  intro K ι κ _ _ _ _ _ U W
  classical
  have hsz0 : ∀ {a b : Type} (g : Matrix a b K), 0 ≤ sz g := by
    intro a b g
    unfold sz
    exact Real.iSup_nonneg (fun p => norm_nonneg _)
  have hnF0 : ∀ (X : Matrix ι κ K), 0 ≤ nF X := by
    intro X
    unfold nF
    exact Real.iSup_nonneg (fun s => norm_nonneg _)
  have hdetT : (Uᵀ * W).det = (Wᵀ * U).det := by
    rw [← Matrix.det_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  by_cases h : ∃ s : κ → ι, (U.submatrix s id).det ≠ 0
  · haveI : Nonempty (κ → ι) := ⟨h.choose⟩
    obtain ⟨s₀, hs₀⟩ := Finite.exists_max (fun s : κ → ι => ‖(U.submatrix s id).det‖)
    have hd : (U.submatrix s₀ id).det ≠ 0 := by
      obtain ⟨s, hs⟩ := h
      intro h0
      have h1 := hs₀ s
      simp only [h0, norm_zero] at h1
      exact hs (norm_le_zero_iff.mp h1)
    have hnU : nF U = ‖(U.submatrix s₀ id).det‖ := by
      unfold nF
      apply le_antisymm
      · exact ciSup_le hs₀
      · exact le_ciSup (f := fun s : κ → ι => ‖(U.submatrix s id).det‖)
          (Set.finite_range _).bddAbove s₀
    set G : Matrix ι κ K := Matrix.of fun i k => (U.submatrix s₀ id).det⁻¹ *
      (U.submatrix (Function.update s₀ k i) id).det with hG
    have hUG : U = G * U.submatrix s₀ id := eq_mul_of_det_ne_zero U s₀ hd
    have hszG : sz Gᵀ ≤ 1 := by
      unfold sz
      apply Real.iSup_le ?_ zero_le_one
      intro p
      simp only [Matrix.transpose_apply, hG, Matrix.of_apply, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hd), mul_one]
      exact hs₀ _
    have hmain : ‖(Gᵀ * W).det‖ ≤ nF W := by
      have h1 := (hM K ι κ κ W).1 Gᵀ
      have h2 := (hM K ι κ κ W).2.2 (Gᵀ * W)
      rw [h2] at h1
      calc ‖(Gᵀ * W).det‖ ≤ sz Gᵀ ^ Fintype.card κ * nF W := h1
        _ ≤ 1 * nF W := by
          apply mul_le_mul_of_nonneg_right _ (hnF0 W)
          exact pow_le_one₀ (hsz0 _) hszG
        _ = nF W := one_mul _
    have hfac : (Uᵀ * W).det = (U.submatrix s₀ id).det * (Gᵀ * W).det := by
      conv_lhs => rw [hUG]
      rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.det_mul, Matrix.det_transpose]
    rw [hfac, norm_mul, hnU]
    exact mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
  · simp only [not_exists, not_not] at h
    have hnU : nF U = 0 := by
      unfold nF
      simp only [h, norm_zero]
      first
        | exact Real.iSup_const_zero
        | simp
    have h1 := (hM K ι κ κ U).1 Wᵀ
    have h2 := (hM K ι κ κ U).2.2 (Wᵀ * U)
    rw [h2, hnU, mul_zero] at h1
    rw [hdetT, hnU, zero_mul]
    exact h1

end GlobalTheory.CompanionTheory.Wedge

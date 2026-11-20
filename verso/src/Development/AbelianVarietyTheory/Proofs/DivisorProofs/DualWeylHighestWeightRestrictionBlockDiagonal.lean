import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

/- English proof (translation)
Establish `key : lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) = (Algebra.TensorProduct.includeLeft (R` using `ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ)) (lpMinor ℚ s hs hs) := rfl`. Rewrite using `[key, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]`.

Establish `hi : (Fin.castLE h1 i : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs i)` using `Fin.ext rfl`. Establish `hj : (Fin.castLE h2 j : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs j)` using `Fin.ext rfl`. Rewrite using `[hi, hj, resT, aeval_X]`. Simplify using `[resVarT]`.
-/
theorem resT_lpMinor_le (p q s : ℕ) (h1 : s ≤ p + q) (h2 : s ≤ p + q) (hs : s ≤ p) :
    resT ℚ p q (lpMinor ℚ s h1 h2) = lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) := by
  have key : lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) =
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ))
        (lpMinor ℚ s hs hs) := rfl
  rw [key, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  have hi : (Fin.castLE h1 i : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs i) := Fin.ext rfl
  have hj : (Fin.castLE h2 j : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs j) := Fin.ext rfl
  rw [hi, hj, resT, aeval_X]
  simp [resVarT]

/- English proof (translation)
Establish `key : lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu = (Algebra.TensorProduct.includeLeft (R` using `ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ)) (lpMinor ℚ p le_rfl le_rfl) * (Algebra.TensorProduct.includeRight (R := ℚ) (A := MvPolynomial (Fin p × Fin p) ℚ)) (lpMinor ℚ u hu hu) := by`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[key, lpMinor, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det, AlgHom.map_det, ← Matrix.det_submatrix_equiv_self finSumFinEquiv, ← Matrix.det_fromBlocks_zero₂₁ (B := 0)]`. Use `congr 1`. Use extensionality with `(a | a) (b | b)`.

Simplify using `only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]`. Establish `hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl a)` using `Fin.ext rfl`. Establish `hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl b)` using `Fin.ext rfl`. Rewrite using `[hi, hj, resT, aeval_X]`. Simplify using `[resVarT]`.

Simplify using `only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]`. Establish `hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q a` using `Fin.ext rfl`. Establish `hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b)` using `Fin.ext rfl`. Rewrite using `[hi, hj, resT, aeval_X]`. Simplify using `[resVarT]`.

Simplify using `only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]`. Establish `hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a)` using `Fin.ext rfl`. Establish `hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q b` using `Fin.ext rfl`. Rewrite using `[hi, hj, resT, aeval_X]`. Simplify using `[resVarT]`.

Simplify using `only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]`. Establish `hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a)` using `Fin.ext rfl`. Establish `hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b)` using `Fin.ext rfl`. Rewrite using `[hi, hj, resT, aeval_X]`. Simplify using `[resVarT]`.
-/
theorem resT_lpMinor_ge (p q u : ℕ) (h1 : p + u ≤ p + q) (h2 : p + u ≤ p + q) (hu : u ≤ q) :
    resT ℚ p q (lpMinor ℚ (p + u) h1 h2) = lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu := by
  have key : lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu =
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ))
        (lpMinor ℚ p le_rfl le_rfl) *
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := MvPolynomial (Fin p × Fin p) ℚ))
        (lpMinor ℚ u hu hu) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [key, lpMinor, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det, AlgHom.map_det,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, ← Matrix.det_fromBlocks_zero₂₁ (B := 0)]
  congr 1
  ext (a | a) (b | b)
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
    have hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    have hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q a := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    have hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q b := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]
    have hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]

/- English proof (translation)
Unfold `nuNext`. Simplify using `only [Fin.val_natAdd]`. Use `split_ifs with h h' h'`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem nuNext_natAdd (p q : ℕ) (ν : Fin (p + q) → ℕ) (j : Fin q) :
    nuNext ν (Fin.natAdd p j) = nuNext (fun j => ν (Fin.natAdd p j)) j := by
  unfold nuNext
  simp only [Fin.val_natAdd]
  split_ifs with h h' h'
  · congr 1
  · omega
  · omega
  · rfl

/- English proof (translation)
Unfold `nuNext`. Simplify using `only [Fin.val_castAdd]`. Rewrite using `[dif_pos (by omega), dif_pos hi]`. Both sides reduce to the same expression.
-/
theorem nuNext_castAdd (p q : ℕ) (ν : Fin (p + q) → ℕ) (i : Fin p) (hi : (i : ℕ) + 1 < p) :
    nuNext ν (Fin.castAdd q i) = nuNext (fun i => ν (Fin.castAdd q i)) i := by
  unfold nuNext
  simp only [Fin.val_castAdd]
  rw [dif_pos (by omega), dif_pos hi]
  rfl

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simp [nuNext]`. Consider the case `succ q ih`. Rewrite using `[Fin.sum_univ_succ]`. Establish `h1 : ∀ j : Fin (q + 1), nuNext μ j.succ = nuNext (fun j => μ j.succ) j`.

Introduce `j`. Unfold `nuNext`. Simplify using `only [Fin.val_succ]`. Apply the tactic sequence `split_ifs with h h' h' <;> first | omega | rfl`. Repeatedly rewrite using `[h1]`.

Rewrite using `[ih (fun j => μ j.succ) (fun a b hab => hμ (Fin.succ_le_succ_iff.mpr hab))]`. Establish `h0 : nuNext μ 0 = μ (Fin.succ 0)`. Unfold `nuNext; rw [dif_pos (by simp)]; rfl`. Rewrite using `[h0]`. Use `hμ (Fin.zero_le (Fin.succ 0 : Fin (q + 2)))` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem sum_sub_nuNext (q : ℕ) (μ : Fin (q + 1) → ℕ) (hμ : Antitone μ) :
    ∑ j, (μ j - nuNext μ j) = μ 0 := by
  induction q with
  | zero => simp [nuNext]
  | succ q ih =>
    rw [Fin.sum_univ_succ]
    have h1 : ∀ j : Fin (q + 1), nuNext μ j.succ = nuNext (fun j => μ j.succ) j := by
      intro j
      unfold nuNext
      simp only [Fin.val_succ]
      split_ifs with h h' h' <;> first | omega | rfl
    simp_rw [h1]
    rw [ih (fun j => μ j.succ) (fun a b hab => hμ (Fin.succ_le_succ_iff.mpr hab))]
    have h0 : nuNext μ 0 = μ (Fin.succ 0) := by
      unfold nuNext; rw [dif_pos (by simp)]; rfl
    rw [h0]
    have := hμ (Fin.zero_le (Fin.succ 0 : Fin (q + 2)))
    omega

/- English proof (translation)
Substitute `hs` using the available equality. Conclude with `resT_lpMinor_ge p q u h1 h2 hu`.
-/
theorem resT_lpMinor_ge' (p q s u : ℕ) (h1 : s ≤ p + q) (h2 : s ≤ p + q) (hu : u ≤ q) (hs : s = p + u) :
    resT ℚ p q (lpMinor ℚ s h1 h2) = lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu := by
  subst hs
  exact resT_lpMinor_ge p q u h1 h2 hu

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [Algebra.TensorProduct.one_def]`. Consider the case `insert x s hx ih => rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx, ih, Algebra.TensorProduct.tmul_mul_tmul]`.
-/
theorem prod_tmul_prod {ι A B : Type} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (s : Finset ι) (a : ι → A) (b : ι → B) :
    ∏ i ∈ s, (a i ⊗ₜ[ℚ] b i) = (∏ i ∈ s, a i) ⊗ₜ[ℚ] (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Algebra.TensorProduct.one_def]
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

/- English proof (translation)
Break down `p with _ | p` into its components or cases. Simplify using `[hw, lpMinor, Matrix.det_isEmpty]`. Rewrite using `[hw, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]`. Simplify using `only [Fin.val_last]`. Rewrite using `[← pow_add]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[nuNext_castAdd (p + 1) q ν k.castSucc (by simp)]`. Establish `hl : nuNext (fun i => ν (Fin.castAdd q i)) (Fin.last p) = 0`. Unfold `nuNext; rw [dif_neg (by simp)]`.

Rewrite using `[hl, Nat.sub_zero]`. Use `congr 1`. Repeatedly rewrite using `[nuNext_natAdd]`. Break down `q with _ | q` into its components or cases. Simplify using `[nuNext]`.

Rewrite using `[sum_sub_nuNext q (fun j => ν (Fin.natAdd (p + 1) j)) (fun a b hab => hν (by rw [Fin.le_def] at hab ⊢; simp only [Fin.val_natAdd]; omega))]`. Establish `h0 : nuNext ν (Fin.castAdd (q + 1) (Fin.last p)) = ν (Fin.natAdd (p + 1) 0)`. Apply the tactic sequence `unfold nuNext; rw [dif_pos (by simp <;> omega)]; congr 1`. Use `hν (show Fin.castAdd (q + 1) (Fin.last p) ≤ Fin.natAdd (p + 1) 0 by` as an intermediate fact. Simplify using `[Fin.le_def])`.

Rewrite using `[h0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem hw_first (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) :
    (∏ i : Fin p, lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^
        (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) *
      lpMinor ℚ p le_rfl le_rfl ^ (∑ j : Fin q, (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) =
      hw ℚ le_rfl (fun i => ν (Fin.castAdd q i)) := by
  rcases p with _ | p
  · simp [hw, lpMinor, Matrix.det_isEmpty]
  · rw [hw, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
    simp only [Fin.val_last]
    rw [← pow_add]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      rw [nuNext_castAdd (p + 1) q ν k.castSucc (by simp)]
    · have hl : nuNext (fun i => ν (Fin.castAdd q i)) (Fin.last p) = 0 := by
        unfold nuNext; rw [dif_neg (by simp)]
      rw [hl, Nat.sub_zero]
      congr 1
      simp_rw [nuNext_natAdd]
      rcases q with _ | q
      · simp [nuNext]
      · rw [sum_sub_nuNext q (fun j => ν (Fin.natAdd (p + 1) j))
          (fun a b hab => hν (by rw [Fin.le_def] at hab ⊢; simp only [Fin.val_natAdd]; omega))]
        have h0 : nuNext ν (Fin.castAdd (q + 1) (Fin.last p)) = ν (Fin.natAdd (p + 1) 0) := by
          unfold nuNext; rw [dif_pos (by simp <;> omega)]; congr 1
        have := hν (show Fin.castAdd (q + 1) (Fin.last p) ≤ Fin.natAdd (p + 1) 0 by
          simp [Fin.le_def])
        rw [h0]
        omega

/- English proof (translation)
Introduce `p q ν hν`. Rewrite using `[hw, map_prod, Fin.prod_univ_add]`. Establish `e1 : ∀ i : Fin p, resT ℚ p q (lpMinor ℚ ((Fin.castAdd q i : ℕ) + 1) (by omega) (by omega) ^ (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) = (lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^ (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × …`. Introduce `i`. Apply the tactic sequence `rw [map_pow, resT_lpMinor_le p q _ _ _ (by simp <;> omega), Algebra.TensorProduct.tmul_pow, one_pow]`.

Both sides reduce to the same expression. Establish `e2 : ∀ j : Fin q, resT ℚ p q (lpMinor ℚ ((Fin.natAdd p j : ℕ) + 1) (by omega) (by omega) ^ (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) = (lpMinor ℚ p le_rfl le_rfl ^ (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) ⊗ₜ[ℚ] (lpMinor ℚ ((j : ℕ) + 1) (by omega) (by omega) ^ ((f …`. Introduce `j`. Apply the tactic sequence `rw [map_pow, resT_lpMinor_ge' p q _ ((j : ℕ) + 1) _ _ (by omega) (by simp <;> omega), Algebra.TensorProduct.tmul_pow, nuNext_natAdd]`. Rewrite using `[Finset.prod_congr rfl fun i _ => e1 i, Finset.prod_congr rfl fun j _ => e2 j, prod_tmul_prod, prod_tmul_prod, Algebra.TensorProduct.tmul_mul_tmul, Finset.prod_const_one, one_mul, Finset.prod_pow_eq_pow_sum, hw_first p q ν hν]`.

Both sides reduce to the same expression.
-/
theorem resHw_holds : ResHw := by
  intro p q ν hν
  rw [hw, map_prod, Fin.prod_univ_add]
  have e1 : ∀ i : Fin p, resT ℚ p q (lpMinor ℚ ((Fin.castAdd q i : ℕ) + 1) (by omega) (by omega) ^
      (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) =
      (lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^ (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) ⊗ₜ[ℚ]
        (1 : MvPolynomial (Fin q × Fin q) ℚ) := by
    intro i
    rw [map_pow, resT_lpMinor_le p q _ _ _ (by simp <;> omega), Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  have e2 : ∀ j : Fin q, resT ℚ p q (lpMinor ℚ ((Fin.natAdd p j : ℕ) + 1) (by omega) (by omega) ^
      (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) =
      (lpMinor ℚ p le_rfl le_rfl ^ (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) ⊗ₜ[ℚ]
        (lpMinor ℚ ((j : ℕ) + 1) (by omega) (by omega) ^
          ((fun j => ν (Fin.natAdd p j)) j - nuNext (fun j => ν (Fin.natAdd p j)) j)) := by
    intro j
    rw [map_pow, resT_lpMinor_ge' p q _ ((j : ℕ) + 1) _ _ (by omega) (by simp <;> omega),
      Algebra.TensorProduct.tmul_pow, nuNext_natAdd]
  rw [Finset.prod_congr rfl fun i _ => e1 i, Finset.prod_congr rfl fun j _ => e2 j, prod_tmul_prod,
    prod_tmul_prod, Algebra.TensorProduct.tmul_mul_tmul, Finset.prod_const_one, one_mul,
    Finset.prod_pow_eq_pow_sum, hw_first p q ν hν]
  rfl

end GlobalTheory.LeviCut

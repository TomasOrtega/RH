import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.ExactSecondDegreeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionPartitionTotal

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial PI.EagonNorthcott

def nn (m : ℕ) (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => m
  | j + 1 => r (j + 1)

def BB {D m : ℕ} (e0 : Fin m → W D) (r : ℕ → ℕ) (b : ∀ j, Fin (r j) → W D) : ∀ j, Fin (nn m r j) → W D
  | 0 => e0
  | j + 1 => b (j + 1)

/- English proof (translation)
Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ct_Phi {D r : ℕ} (b : Fin r → W D) (v : Fin r → S D) (i : Fin D) (J : Finset (Fin D)) :
    ct i (Phi b v) J = ∑ k, inx (v k) * ct i (b k) J := by
  simp only [ct, Phi]
  split_ifs
  · simp
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem inx_X {D : ℕ} (i : Fin D) : inx (X i : S D) = xs i := by simp [inx, xs]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem mu_inx {D : ℕ} (s : S D) : mu (inx s) = s := by
  simp only [mu, inx]
  rw [aeval_rename, Sum.elim_comp_inl, aeval_X_left_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mu_ys {D : ℕ} (i : Fin D) : mu (ys i : P D) = X i := by simp [mu, ys]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem frame_of (hE : LEnum) (hB0 : LBasis0) (hB : LBasis) (hV : LVan) (hI : LInj) (hR : LRan) (hC : LCt)
    (hX : LKx) : Frame := by
  intro D a
  obtain ⟨m, e, he, hae⟩ := hE D a
  choose r b hb using hB D a
  have hBB : ∀ j, IsZBasis a j (BB (b0 e) r b j) := by
    intro j
    cases j with
    | zero => exact hB0 D a m e he hae
    | succ j => exact hb (j + 1)
  have hmem : ∀ j (i : Fin D) (k : Fin (nn m r (j + 1))), ∃ c : Fin (nn m r j) → ℤ,
      ∑ p, c p • BB (b0 e) r b j p = ct i (BB (b0 e) r b (j + 1) k) := by
    intro j i k
    rw [← Submodule.mem_span_range_iff_exists_fun]
    exact ((hBB j).2 _).1 (hC D a j i _ (((hBB (j + 1)).2 _).2 (Submodule.subset_span ⟨k, rfl⟩)))
  choose c hc using hmem
  refine ⟨nn m r, e, fun j => Matrix.of fun p k i => c j i k p, fun j => Phi (BB (b0 e) r b j), ⟨?_, he, hae⟩,
    fun j => hI D a j _ _ (hBB j), fun j => ?_, fun j ω => hR D a j _ _ (hBB j) ω, fun j v => ?_, fun v => ?_⟩
  · intro j hj
    by_contra hne
    have k : Fin (nn m r j) := ⟨0, Nat.pos_of_ne_zero hne⟩
    exact (hBB j).1.ne_zero k (hV D a j hj _ (((hBB j).2 _).2 (Submodule.subset_span ⟨k, rfl⟩)))
  · funext J
    simp [Phi]
  · funext J
    have key : ∀ i k, ct i (BB (b0 e) r b (j + 1) k) J = ∑ p, (c j i k p : P D) * BB (b0 e) r b j p J := by
      intro i k
      rw [← hc j i k, Finset.sum_apply]
      simp [zsmul_eq_mul]
    rw [hX D]
    simp only [Phi, dmap, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
      lin, map_sum, map_mul, map_intCast, inx_X, ct_Phi, key, Finset.mul_sum, Finset.sum_mul]
    conv_lhs =>
      rw [Finset.sum_comm]
      arg 2
      ext k
      rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => by ring
  · simp only [aug, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
      Phi, BB, b0, if_true, map_sum, map_mul, mu_inx, map_prod, map_pow, mu_ys]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end PI.EagonNorthcottZ

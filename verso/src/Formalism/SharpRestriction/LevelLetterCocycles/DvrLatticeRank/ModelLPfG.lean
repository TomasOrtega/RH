import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfF

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLG

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

variable {LL V' : Type} [Field LL] [AddCommGroup V'] [Module LL V']

def Bdd (F : ℤ → V') (m₀ : ℤ) : Prop := ∀ i < m₀, F i = 0

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem serMul_eq_sum (P : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) (i : ℤ) (M : ℕ)
    (hM : (i - m₀).toNat + 1 ≤ M) :
    serMul P F i = ∑ k ∈ Finset.range M, PowerSeries.coeff k P • F (i - k) := by
  unfold serMul
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hkM
  apply hk
  rw [hF (i - k) (by omega), smul_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem serMul_bdd (P : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) : Bdd (serMul P F) m₀ := by
  intro i hi
  unfold serMul
  apply finsum_eq_zero_of_forall_eq_zero
  intro k
  rw [hF (i - k) (by omega), smul_zero]

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem serMul_serMul (P Q : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) (i : ℤ) :
    serMul P (serMul Q F) i = serMul (P * Q) F i := by
  set N := (i - m₀).toNat + 1 with hN
  rw [serMul_eq_sum P (serMul_bdd Q hF) i N le_rfl, serMul_eq_sum (P * Q) hF i N le_rfl]
  have hL : ∀ k ∈ Finset.range N, PowerSeries.coeff k P • serMul Q F (i - k) =
      ∑ j ∈ Finset.range (N - k), (PowerSeries.coeff k P * PowerSeries.coeff j Q) • F (i - (k + j : ℕ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [serMul_eq_sum Q hF (i - k) (N - k) (by omega), Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_smul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hL]
  have hR : ∀ s ∈ Finset.range N, PowerSeries.coeff s (P * Q) • F (i - s) =
      ∑ k ∈ Finset.Ico 0 (s + 1), (PowerSeries.coeff k P * PowerSeries.coeff (s - k) Q) • F (i - s) := by
    intro s _
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_smul,
      Finset.range_eq_Ico]
  rw [Finset.sum_congr rfl hR, Finset.range_eq_Ico, ← Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.add_sub_cancel_left]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem serMul_X_pow (h : ℕ) (F : ℤ → V') (i : ℤ) :
    serMul (PowerSeries.X ^ h : PowerSeries LL) F i = F (i - h) := by
  unfold serMul
  rw [finsum_eq_single _ h (fun k hk => by rw [PowerSeries.coeff_X_pow, if_neg hk, zero_smul])]
  rw [PowerSeries.coeff_X_pow, if_pos rfl, one_smul]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the hypotheses and the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem serMul_rescale (u : LL) (hu : u ≠ 0) (P : PowerSeries LL) (F : ℤ → V') (i : ℤ) :
    u ^ i • serMul P F i = serMul (PowerSeries.rescale u P) (fun j => u ^ j • F j) i := by
  unfold serMul
  rw [smul_finsum]
  refine finsum_congr (fun k => ?_)
  rw [PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  rw [show u ^ i = u ^ (k : ℤ) * u ^ (i - k) by rw [← zpow_add₀ hu]; ring_nf, zpow_natCast]
  ring

end Formalism.MainNotions.N.Ln34.MLG

end

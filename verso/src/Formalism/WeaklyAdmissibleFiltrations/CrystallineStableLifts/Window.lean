import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pht_window_sum_Ico_telescope (f : ℤ → ℤ) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, (f a - f (a + 1)) = f m - f k := by
  induction k, hmk using Int.le_induction with
  | base => simp
  | succ k hk ih =>
    have hs : Finset.Ico m (k + 1) = insert k (Finset.Ico m k) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hs, Finset.sum_insert (by simp), ih]
    ring

variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem pht_window_mult_lo (F : FilPhi LL D n Emb) (D' : Submodule LL D) (τ : Emb) (a : ℤ)
    (ha : a < F.lo) : F.mult D' τ a = 0 := by
  unfold FilPhi.mult
  rw [F.Fil_lo τ a ha.le, F.Fil_lo τ (a + 1) (by omega)]
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem pht_window_mult_hi (F : FilPhi LL D n Emb) (D' : Submodule LL D) (τ : Emb) (a : ℤ)
    (ha : F.hi ≤ a) : F.mult D' τ a = 0 := by
  unfold FilPhi.mult
  rw [F.Fil_hi τ a ha, F.Fil_hi τ (a + 1) (by omega)]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Use symmetry to reverse the relation.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem thWindow_part : THWindow := by
  intro LL _ D _ _ _ n Emb _ F D' l h hl hh
  unfold FilPhi.tH FilPhi.tHw
  apply Finset.sum_congr rfl
  intro τ _
  symm
  apply Finset.sum_subset
  · intro a ha
    simp only [Finset.mem_Ico] at ha ⊢
    omega
  · intro a _ hna
    simp only [Finset.mem_Ico, not_and, not_lt] at hna
    rcases lt_or_ge a F.lo with h1 | h1
    · rw [pht_window_mult_lo F D' τ a h1, mul_zero]
    · rw [pht_window_mult_hi F D' τ a (hna h1), mul_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem multiplicitySum_holds : DimSum := by
  intro LL _ D _ _ _ n Emb _ F D' τ
  have key : ∑ a ∈ Finset.Ico F.lo F.hi, ((finrank LL ↥(F.Fil τ a ⊓ D') : ℤ) -
      (finrank LL ↥(F.Fil τ (a + 1) ⊓ D') : ℤ)) =
      (finrank LL ↥(F.Fil τ F.lo ⊓ D') : ℤ) - (finrank LL ↥(F.Fil τ F.hi ⊓ D') : ℤ) :=
    pht_window_sum_Ico_telescope (fun a => (finrank LL ↥(F.Fil τ a ⊓ D') : ℤ)) F.lo F.hi F.lo_le
  unfold FilPhi.mult
  rw [key, F.Fil_lo τ F.lo le_rfl, F.Fil_hi τ F.hi le_rfl]
  simp

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem hodgeDegreeWindow_and_multiplicitySum : THWindow ∧ DimSum := ⟨thWindow_part, multiplicitySum_holds⟩

end Formalism.WeaklyAdmissibleFiltrations

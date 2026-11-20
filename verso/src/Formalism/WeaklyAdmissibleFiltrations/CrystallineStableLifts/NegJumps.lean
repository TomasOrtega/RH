import Formalism.WeaklyAdmissibleFiltrations.DpcrisStable

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem negJumps_Ico_telescope (f : ℤ → ℤ) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, (f a - f (a + 1)) = f m - f k := by
  induction k, hmk using Int.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [← Finset.Ico_union_Ico_eq_Ico hk (by omega),
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive m k (k + 1)), ih]
    have h1 : Finset.Ico k (k + 1) = {k} := by
      ext z
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [h1, Finset.sum_singleton]
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem negativeJumpsSum_holds : NegJumps := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ τ lo _ hlo hF
  have h1 := negJumps_Ico_telescope (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) lo 0 hlo
  unfold multV
  rw [h1, hF]

end Formalism.WeaklyAdmissibleFiltrations

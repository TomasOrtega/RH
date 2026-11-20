import Formalism.WeaklyAdmissibleFiltrations.WindowCount

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem windowCount_Ico_telescope (f : ℤ → ℤ) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, (f a - f (a + 1)) = f m - f k := by
  induction k, hmk using Int.le_induction with
  | base => simp
  | succ k hk ih =>
    have hset : Finset.Ico m (k + 1) = insert k (Finset.Ico m k) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hset, Finset.sum_insert (by simp), ih]
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem windowCountAlt : WindowCount := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ τ lo hi hlh
  unfold multV
  exact windowCount_Ico_telescope (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) lo hi hlh

end Formalism.WeaklyAdmissibleFiltrations

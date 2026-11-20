import Formalism.WeaklyAdmissibleFiltrations.WindowCount

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

/- English proof (translation)
Proceed by induction on `k, hmk using Int.le_induction with`. Consider the case `base => simp`. Consider the case `succ k hk ih`. Establish `hset : Finset.Ico m (k + 1) = insert k (Finset.Ico m k)`. Use extensionality with `x`.

Simplify using `only [Finset.mem_Ico, Finset.mem_insert]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hset, Finset.sum_insert (by simp), ih]`. Expand and normalize the polynomial expressions, which then agree.
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
Introduce `G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ τ lo hi hlh`. Unfold `multV`. Conclude with `windowCount_Ico_telescope (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) lo hi hlh`.
-/
theorem windowCountAlt : WindowCount := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ τ lo hi hlh
  unfold multV
  exact windowCount_Ico_telescope (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) lo hi hlh

end Formalism.WeaklyAdmissibleFiltrations

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.WalkEnds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.RsParLamMinus
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.InterlacesULt

namespace ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Introduce `k r u v b h t P hk hpar hint hhalf hlow hstep hP`. Take `⟨e1, e2, e3⟩` from `walkEnds k r u v b t`. Establish `hR : ∀ j, 1 ≤ j → j ≤ 2 * r + 2 → P (raisePar k r u b t j)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => intro h1`. Use linear arithmetic over natural numbers and integers. Consider the case `succ j ih`. Introduce `h1 h2`. Break down `Nat.eq_or_lt_of_le h1 with h3 | h3` into its components or cases.

Establish `hj : j = 0` using `by omega`. Substitute `hj` using the available equality. Rewrite using `[← e1]`. Conclude with `hP`. Conclude with `raiseStep k r u v b h t P hk hpar hint hhalf hlow hstep j (by omega) (by omega) (ih (by omega) (by omega))`.

Establish `key : ∀ m, m ≤ k → P (walkPar k r u v b (k - m))`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `_`.

Rewrite using `[Nat.sub_zero, ← e2]`. Conclude with `hR (2 * r + 2) (by omega) le_rfl`. Consider the case `succ m ih`. Introduce `hm`. Establish `h1` using `ih (by omega)`.

Establish `heq : k - m = (k - (m + 1)) + 1` using `by omega`. Rewrite `h1` using `[heq]`. Conclude with `lowerStep k r u v b h P hk hpar hint hhalf hlow hstep (k - (m + 1)) (by omega) h1`. Establish `h0` using `key k le_rfl`. Rewrite `h0` using `[Nat.sub_self, e3]`.

Conclude with `h0`.
-/
theorem walk : WalkStatement := by
  intro k r u v b h t P hk hpar hint hhalf hlow hstep hP
  obtain ⟨e1, e2, e3⟩ := walkEnds k r u v b t
  have hR : ∀ j, 1 ≤ j → j ≤ 2 * r + 2 → P (raisePar k r u b t j) := by
    intro j
    induction j with
    | zero => intro h1; omega
    | succ j ih =>
      intro h1 h2
      rcases Nat.eq_or_lt_of_le h1 with h3 | h3
      · have hj : j = 0 := by omega
        subst hj
        rw [← e1]
        exact hP
      · exact raiseStep k r u v b h t P hk hpar hint hhalf hlow hstep j (by omega) (by omega)
          (ih (by omega) (by omega))
  have key : ∀ m, m ≤ k → P (walkPar k r u v b (k - m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero, ← e2]
      exact hR (2 * r + 2) (by omega) le_rfl
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have heq : k - m = (k - (m + 1)) + 1 := by omega
      rw [heq] at h1
      exact lowerStep k r u v b h P hk hpar hint hhalf hlow hstep (k - (m + 1)) (by omega) h1
  have h0 := key k le_rfl
  rw [Nat.sub_self, e3] at h0
  exact h0

end ReciprocityTheory.ChartRestriction.DS.Lap

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDoubleComplexVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

/- English proof (translation)
Introduce `C _ P δ κ R hδP hκP hδδ hδκ hκκ hsurj hex hzero hacyc`. Establish `triv : ∀ p n, R ≤ p → ∀ x ∈ P p (n + 1), (∃ y ∈ P (p + 1) (n + 1), κ p (n + 1) y = x) → ∃ w ∈ P p n, δ p n w = x ∧ ∃ w' ∈ P (p + 1) n, κ p n w' = w`. Introduce and unpack `p n hp x - ⟨y, hy, rfl⟩`. Rewrite using `[hzero (p + 1) (n + 1) (by omega) y hy, map_zero]`. Conclude with `⟨0, zero_mem _, map_zero _, 0, zero_mem _, map_zero _⟩`.

Establish `claim : ∀ k p n, R ≤ p + k → ∀ x ∈ P p (n + 1), δ p (n + 1) x = 0 → (∃ y ∈ P (p + 1) (n + 1), κ p (n + 1) y = x) → ∃ w ∈ P p n, δ p n w = x ∧ ∃ w' ∈ P (p + 1) n, κ p n w' = w`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact fun p n hp x hx _ hy => triv p n (by omega) x hx hy`. Consider the case `succ k ih`.

Introduce `p n hp x hx hdx hy0`. Distinguish the cases in `hRp : R ≤ p`. Conclude with `triv p n hRp x hx hy0`. Take `⟨y, hy, hyx⟩` from `hy0`. Establish `hdy : δ (p + 1) (n + 1) y ∈ P (p + 1) (n + 2)` using `hδP _ _ y hy`.

Establish `hk : κ p (n + 2) (δ (p + 1) (n + 1) y) = 0`. Rewrite using `[← hδκ p (n + 1) y hy, hyx, hdx]`. Take `⟨w, hw, hwe, w', hw', hw'e⟩` from `ih (p + 1) (n + 1) (by omega) _ hdy (hδδ _ _ y hy) (hex p (n + 2) _ hdy hk)`. Establish `hdyw : δ (p + 1) (n + 1) (y - w) = 0` using `by rw [map_sub, hwe, sub_self]`. Take `⟨v, hv, hve⟩` from `hacyc (p + 1) (by omega) (by omega) n (y - w) (sub_mem hy hw) hdyw`.

Use `⟨κ p n v, hκP _ _ v hv, ?_, v, hv, rfl⟩` and prove the remaining obligations. Rewrite using `[hδκ p n v hv, hve, map_sub, hyx, ← hw'e, hκκ p (n + 1) w' hw', sub_zero]`. Introduce `n x hx hdx`. Take `⟨w, hw, hwe, -⟩` from `claim R 0 n (by omega) x hx hdx (hsurj (n + 1) x hx)`. Conclude with `⟨w, hw, hwe⟩`.
-/
theorem DoubleComplexVanish.proof : DoubleComplexVanish.Statement := by
  intro C _ P δ κ R hδP hκP hδδ hδκ hκκ hsurj hex hzero hacyc

  have triv : ∀ p n, R ≤ p → ∀ x ∈ P p (n + 1), (∃ y ∈ P (p + 1) (n + 1), κ p (n + 1) y = x) →
      ∃ w ∈ P p n, δ p n w = x ∧ ∃ w' ∈ P (p + 1) n, κ p n w' = w := by
    rintro p n hp x - ⟨y, hy, rfl⟩
    rw [hzero (p + 1) (n + 1) (by omega) y hy, map_zero]
    exact ⟨0, zero_mem _, map_zero _, 0, zero_mem _, map_zero _⟩
  have claim : ∀ k p n, R ≤ p + k → ∀ x ∈ P p (n + 1), δ p (n + 1) x = 0 →
      (∃ y ∈ P (p + 1) (n + 1), κ p (n + 1) y = x) →
      ∃ w ∈ P p n, δ p n w = x ∧ ∃ w' ∈ P (p + 1) n, κ p n w' = w := by
    intro k
    induction k with
    | zero => exact fun p n hp x hx _ hy => triv p n (by omega) x hx hy
    | succ k ih =>
      intro p n hp x hx hdx hy0
      by_cases hRp : R ≤ p
      · exact triv p n hRp x hx hy0
      obtain ⟨y, hy, hyx⟩ := hy0
      have hdy : δ (p + 1) (n + 1) y ∈ P (p + 1) (n + 2) := hδP _ _ y hy
      have hk : κ p (n + 2) (δ (p + 1) (n + 1) y) = 0 := by
        rw [← hδκ p (n + 1) y hy, hyx, hdx]
      obtain ⟨w, hw, hwe, w', hw', hw'e⟩ :=
        ih (p + 1) (n + 1) (by omega) _ hdy (hδδ _ _ y hy) (hex p (n + 2) _ hdy hk)
      have hdyw : δ (p + 1) (n + 1) (y - w) = 0 := by rw [map_sub, hwe, sub_self]
      obtain ⟨v, hv, hve⟩ := hacyc (p + 1) (by omega) (by omega) n (y - w) (sub_mem hy hw) hdyw
      refine ⟨κ p n v, hκP _ _ v hv, ?_, v, hv, rfl⟩
      rw [hδκ p n v hv, hve, map_sub, hyx, ← hw'e, hκκ p (n + 1) w' hw', sub_zero]
  intro n x hx hdx
  obtain ⟨w, hw, hwe, -⟩ := claim R 0 n (by omega) x hx hdx (hsurj (n + 1) x hx)
  exact ⟨w, hw, hwe⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel

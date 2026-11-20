import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `R P _ _ _ _ _ hind f`. Take `⟨n, hn⟩` from `(LinearMap.eventually_isCompl_ker_pow_range_pow f).exists_forall_of_atTop`. Establish `hc` using `hn (n + 1) (Nat.le_succ n)`. Break down `hind _ _ hc with hk | hr` into its components or cases. Use `right`.

Establish `hk1 : LinearMap.ker f = ⊥`. Rewrite using `[eq_bot_iff, ← hk]`. Introduce `x hx`. Establish `hx' : f x = 0` using `hx`. Rewrite using `[LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hx', map_zero]`.

Establish `hr1 : LinearMap.range (f ^ (n + 1)) = ⊤`. Use `hc.sup_eq_top` as an intermediate fact. Rewrite `this` using `[hk, bot_sup_eq]`. Then use the resulting hypothesis. Establish `hs : LinearMap.range f = ⊤`. Rewrite using `[eq_top_iff, ← hr1]`.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `⟨_, rfl⟩`. Conclude with `⟨LinearMap.ker_eq_bot.mp hk1, LinearMap.range_eq_top.mp hs⟩`. Use `left`.

Use `⟨n + 1, ?_⟩` and prove the remaining obligations. Establish `hk1 : LinearMap.ker (f ^ (n + 1)) = ⊤`. Use `hc.sup_eq_top` as an intermediate fact. Rewrite `this` using `[hr, sup_bot_eq]`. Then use the resulting hypothesis. Conclude with `LinearMap.ker_eq_top.mp hk1`.
-/
theorem endo_indecomposable_finite_length_nilpotent_or_bijective :
    ∀ (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
      (∀ A B : Submodule R P, IsCompl A B → A = ⊥ ∨ B = ⊥) →
      ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f := by
  intro R P _ _ _ _ _ hind f
  obtain ⟨n, hn⟩ := (LinearMap.eventually_isCompl_ker_pow_range_pow f).exists_forall_of_atTop
  have hc := hn (n + 1) (Nat.le_succ n)
  rcases hind _ _ hc with hk | hr
  · right
    have hk1 : LinearMap.ker f = ⊥ := by
      rw [eq_bot_iff, ← hk]
      intro x hx
      have hx' : f x = 0 := hx
      rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hx', map_zero]
    have hr1 : LinearMap.range (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hk, bot_sup_eq] at this
    have hs : LinearMap.range f = ⊤ := by
      rw [eq_top_iff, ← hr1]
      rintro _ ⟨x, rfl⟩
      rw [pow_succ', Module.End.mul_apply]
      exact ⟨_, rfl⟩
    exact ⟨LinearMap.ker_eq_bot.mp hk1, LinearMap.range_eq_top.mp hs⟩
  · left
    refine ⟨n + 1, ?_⟩
    have hk1 : LinearMap.ker (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hr, sup_bot_eq] at this
    exact LinearMap.ker_eq_top.mp hk1

end GlobalTheory

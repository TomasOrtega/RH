import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Nondeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.EnlargeStep

namespace PI.Witt

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ B hB hnd`. Establish `key : ∀ (m : ℕ) (U : Submodule K V), Module.finrank K V - Module.finrank K U = m → ∀ f : U →ₗ[K] V, Function.Injective f → (∀ x y : U, B (f x) (f y) = B x y) → ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ x : U, g x = f x`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`.

Introduce `U hm f hinj hf`. Distinguish the cases in `hU : ∀ x ∈ U, (∀ y ∈ U, B x y = 0) → x = 0`. Take `⟨g, hg, hge, -⟩` from `nondeg_extend h1 h2 B hB _ U rfl hU f hf`. Conclude with `⟨g, hg, hge⟩`. Use `push Not at hU`.

Take `⟨r, hrU, hr, hr0⟩` from `hU`. Take `⟨U', hlt, f', hinj', hf', hext⟩` from `enlarge_step B hB hnd U f hinj hf r hrU hr0 hr`. Establish `h3 : Module.finrank K U < Module.finrank K U'` using `Submodule.finrank_lt_finrank_of_lt hlt`. Establish `h4 : Module.finrank K U' ≤ Module.finrank K V` using `Submodule.finrank_le U'`. Take `⟨g, hg, hge⟩` from `ih (Module.finrank K V - Module.finrank K U') (by omega) U' rfl f' hinj' hf'`.

Use `⟨g, hg, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← hext x, ← hge]`. Introduce `U f hinj hf`. Conclude with `key _ U rfl f hinj hf`.
-/
theorem witt_of (h1 : OneVector) (h2 : Anisotropic) : PI.WittExtension := by
  intro K V _ _ _ _ _ _ B hB hnd
  have key : ∀ (m : ℕ) (U : Submodule K V), Module.finrank K V - Module.finrank K U = m →
      ∀ f : U →ₗ[K] V, Function.Injective f → (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ x : U, g x = f x := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro U hm f hinj hf
    by_cases hU : ∀ x ∈ U, (∀ y ∈ U, B x y = 0) → x = 0
    · obtain ⟨g, hg, hge, -⟩ := nondeg_extend h1 h2 B hB _ U rfl hU f hf
      exact ⟨g, hg, hge⟩
    · push Not at hU
      obtain ⟨r, hrU, hr, hr0⟩ := hU
      obtain ⟨U', hlt, f', hinj', hf', hext⟩ := enlarge_step B hB hnd U f hinj hf r hrU hr0 hr
      have h3 : Module.finrank K U < Module.finrank K U' := Submodule.finrank_lt_finrank_of_lt hlt
      have h4 : Module.finrank K U' ≤ Module.finrank K V := Submodule.finrank_le U'
      obtain ⟨g, hg, hge⟩ := ih (Module.finrank K V - Module.finrank K U') (by omega) U' rfl f' hinj' hf'
      refine ⟨g, hg, fun x => ?_⟩
      rw [← hext x, ← hge]
  intro U f hinj hf
  exact key _ U rfl f hinj hf

end PI.Witt

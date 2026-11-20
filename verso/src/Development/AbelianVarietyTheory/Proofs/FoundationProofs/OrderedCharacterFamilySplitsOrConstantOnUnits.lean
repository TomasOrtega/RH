import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

/- English proof (translation)
Apply `h u hu` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem apply_eq_one_of_triv_one_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ : kˣ →* ℂˣ} (h : Triv χ 1) (u : kˣ) (hu : valuation k (u : k) = 1) : χ u = 1 := by
  apply h u hu
  calc valuation k ((u : k) - 1) ≤ max (valuation k (u : k)) (valuation k 1) := Valuation.map_sub _ _ _
    _ = valuation k 1 := by simp [hu]

/- English proof (translation)
Introduce `k _ _ _ _ n ψ hord`. Distinguish the cases in `hc : ∃ m : ℕ, ∃ h : m + 1 < n, ¬ Triv (ψ ⟨m, by omega⟩ / ψ ⟨m + 1, h⟩) 1`. Take `⟨m, hm, hnt⟩` from `hc`. Use `Or.inl ⟨m + 1, by omega, hm, ?_⟩` and prove the remaining obligations. Introduce `i j hi hj htr`.

Establish `h1 : i ≤ (⟨m, by omega⟩ : Fin n)` using `by rw [Fin.le_def]; simp; omega`. Establish `h2 : (⟨m, by omega⟩ : Fin n) ≤ ⟨m + 1, hm⟩` using `by rw [Fin.le_def]; simp`. Establish `h3 : (⟨m + 1, hm⟩ : Fin n) ≤ j` using `by rw [Fin.le_def]; simp; omega`. Conclude with `hnt (hord i _ _ j h1 h2 h3 1 htr)`. Use `push_neg at hc right`.

Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Use `⟨1, fun _ => ?_, fun i => i.elim0⟩` and prove the remaining obligations. Use `show IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ)`. Simplify using the standard rewrite rules.

Use `⟨ψ ⟨0, hn⟩, fun hs => hs _, ?_⟩` and prove the remaining obligations. Establish `key : ∀ m (hm : m < n) (u : kˣ), valuation k (u : k) = 1 → ψ ⟨m, hm⟩ u = ψ ⟨0, hn⟩ u`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _ _ _`.

Both sides reduce to the same expression. Consider the case `succ m ih`. Introduce `hm u hu`. Establish `h1` using `apply_eq_one_of_triv_one_unit (hc m hm) u hu`. Rewrite `h1` using `[MonoidHom.div_apply, div_eq_one]`.

Rewrite using `[← h1, ih (by omega) u hu]`. Introduce `i u hu`. Conclude with `key i.1 i.2 u hu`.
-/
theorem cut_or_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → (∃ r : ℕ, 0 < r ∧ r < n ∧ Cut ψ r) ∨ ∃ χ : kˣ →* ℂˣ, ((∀ i, IsSmoothChar (ψ i)) → IsSmoothChar χ) ∧ Agree ψ (fun _ => χ) := by
  intro k _ _ _ _ n ψ hord
  by_cases hc : ∃ m : ℕ, ∃ h : m + 1 < n, ¬ Triv (ψ ⟨m, by omega⟩ / ψ ⟨m + 1, h⟩) 1
  · obtain ⟨m, hm, hnt⟩ := hc
    refine Or.inl ⟨m + 1, by omega, hm, ?_⟩
    intro i j hi hj htr
    have h1 : i ≤ (⟨m, by omega⟩ : Fin n) := by rw [Fin.le_def]; simp; omega
    have h2 : (⟨m, by omega⟩ : Fin n) ≤ ⟨m + 1, hm⟩ := by rw [Fin.le_def]; simp
    have h3 : (⟨m + 1, hm⟩ : Fin n) ≤ j := by rw [Fin.le_def]; simp; omega
    exact hnt (hord i _ _ j h1 h2 h3 1 htr)
  · push_neg at hc
    right
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨1, fun _ => ?_, fun i => i.elim0⟩
      show IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ)
      simp
    · refine ⟨ψ ⟨0, hn⟩, fun hs => hs _, ?_⟩
      have key : ∀ m (hm : m < n) (u : kˣ), valuation k (u : k) = 1 → ψ ⟨m, hm⟩ u = ψ ⟨0, hn⟩ u := by
        intro m
        induction m with
        | zero => intro _ _ _; rfl
        | succ m ih =>
          intro hm u hu
          have h1 := apply_eq_one_of_triv_one_unit (hc m hm) u hu
          rw [MonoidHom.div_apply, div_eq_one] at h1
          rw [← h1, ih (by omega) u hu]
      intro i u hu
      exact key i.1 i.2 u hu

end GlobalTheory.PsType

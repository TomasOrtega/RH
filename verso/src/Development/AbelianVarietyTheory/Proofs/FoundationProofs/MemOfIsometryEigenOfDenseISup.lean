import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `H _ _ _ U hU E lam hlam hfin hE hd m y hy`. Set `V : H →ₗᵢ[ℂ] H` to `⟨U.toLinearMap, hU⟩`. Establish `hin : ∀ a b : H, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ` using `fun a b => V.inner_map_map a b`. Use `haveI := hfin m`. Take `⟨p, hp, q, hq, rfl⟩` from `(E m).exists_add_mem_mem_orthogonal y`.

Establish `hUq : U q = lam m • q`. Rewrite `hy` using `[map_add, hE m p hp, smul_add]`. Conclude with `add_left_cancel hy`. Establish `horth : ∀ m', ∀ e ∈ E m', ⟪e, q⟫_ℂ = 0`. Introduce `m' e he`.

Distinguish the cases in `hm : m' = m`. Substitute `hm` using the available equality. Conclude with `(Submodule.mem_orthogonal _ _).1 hq e he`. Distinguish the cases in `he0 : e = 0`. Simplify using `[he0]`.

Establish `h1` using `hin e q`. Establish `h2` using `hin e e`. Rewrite `h1` using `[hE m' e he, hUq, inner_smul_left, inner_smul_right]`. Rewrite `h2` using `[hE m' e he, inner_smul_left, inner_smul_right]`. Establish `hee : ⟪e, e⟫_ℂ ≠ 0` using `by simpa using he0`.

Establish `h3 : (starRingEnd ℂ) (lam m') * lam m' = 1`. Apply `mul_right_cancel₀ hee` to reduce the goal to its premises. Rewrite using `[one_mul, mul_assoc, h2]`. Assume the negation of the conclusion as `hne`. Establish `h4 : (starRingEnd ℂ) (lam m') * lam m = 1`.

Apply `mul_right_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[one_mul, mul_assoc, h1]`. Establish `h5 : (starRingEnd ℂ) (lam m') ≠ 0` using `left_ne_zero_of_mul_eq_one h3`. Conclude with `hm (hlam (mul_left_cancel₀ h5 (h3.trans h4.symm)))`. Establish `hle : (⨆ m, E m : Submodule ℂ H) ≤ (ℂ ∙ q)ᗮ`.

Use `iSup_le fun m' e he => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_orthogonal_singleton_iff_inner_left]`. Conclude with `horth m' e he`. Establish `hq0 : q = 0`. Establish `hcl : closure ((⨆ m, E m : Submodule ℂ H) : Set H) ⊆ ((ℂ ∙ q)ᗮ : Submodule ℂ H)` using `closure_minimal hle (Submodule.isClosed_orthogonal _)`.

Use `hcl (hd q)` as an intermediate fact. Rewrite `this` using `[SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]`. Simplify using `using this`. Simplify `hp` using `[hq0]`.
-/
theorem mem_of_isometry_eigen_of_dense_iSup :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H), (∀ v, ‖U v‖ = ‖v‖) → ∀ (E : ℕ → Submodule ℂ H) (lam : ℕ → ℂ), Function.Injective lam → (∀ m, FiniteDimensional ℂ (E m)) → (∀ m, ∀ e ∈ E m, U e = lam m • e) → Dense ((⨆ m, E m : Submodule ℂ H) : Set H) → ∀ (m : ℕ) (y : H), U y = lam m • y → y ∈ E m := by
  intro H _ _ _ U hU E lam hlam hfin hE hd m y hy
  let V : H →ₗᵢ[ℂ] H := ⟨U.toLinearMap, hU⟩
  have hin : ∀ a b : H, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b => V.inner_map_map a b
  haveI := hfin m
  obtain ⟨p, hp, q, hq, rfl⟩ := (E m).exists_add_mem_mem_orthogonal y
  have hUq : U q = lam m • q := by
    rw [map_add, hE m p hp, smul_add] at hy
    exact add_left_cancel hy
  have horth : ∀ m', ∀ e ∈ E m', ⟪e, q⟫_ℂ = 0 := by
    intro m' e he
    by_cases hm : m' = m
    · subst hm
      exact (Submodule.mem_orthogonal _ _).1 hq e he
    by_cases he0 : e = 0
    · simp [he0]
    have h1 := hin e q
    have h2 := hin e e
    rw [hE m' e he, hUq, inner_smul_left, inner_smul_right] at h1
    rw [hE m' e he, inner_smul_left, inner_smul_right] at h2
    have hee : ⟪e, e⟫_ℂ ≠ 0 := by simpa using he0
    have h3 : (starRingEnd ℂ) (lam m') * lam m' = 1 := by
      apply mul_right_cancel₀ hee
      rw [one_mul, mul_assoc, h2]
    by_contra hne
    have h4 : (starRingEnd ℂ) (lam m') * lam m = 1 := by
      apply mul_right_cancel₀ hne
      rw [one_mul, mul_assoc, h1]
    have h5 : (starRingEnd ℂ) (lam m') ≠ 0 := left_ne_zero_of_mul_eq_one h3
    exact hm (hlam (mul_left_cancel₀ h5 (h3.trans h4.symm)))
  have hle : (⨆ m, E m : Submodule ℂ H) ≤ (ℂ ∙ q)ᗮ := by
    refine iSup_le fun m' e he => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact horth m' e he
  have hq0 : q = 0 := by
    have hcl : closure ((⨆ m, E m : Submodule ℂ H) : Set H) ⊆ ((ℂ ∙ q)ᗮ : Submodule ℂ H) :=
      closure_minimal hle (Submodule.isClosed_orthogonal _)
    have := hcl (hd q)
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left] at this
    simpa using this
  simpa [hq0] using hp

end GlobalTheory

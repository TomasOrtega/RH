import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `E F _ _ _ _ _ _ A`. Prove the components needed by the constructor for the conclusion. Introduce `hinj`. Establish `hbot : (LinearMap.range A)ᗮ = ⊥`. Rewrite using `[Submodule.eq_bot_iff]`.

Introduce `v hv`. Establish `h0 : LinearMap.adjoint A v = 0`. Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `e`. Rewrite using `[LinearMap.adjoint_inner_left, inner_zero_left]`.

Conclude with `(Submodule.mem_orthogonal' _ _).mp hv (A e) ⟨e, rfl⟩`. Conclude with `hinj (h0.trans (map_zero _).symm)`. Establish `htop : LinearMap.range A = ⊤` using `Submodule.orthogonal_eq_bot_iff.mp hbot`. Conclude with `LinearMap.range_eq_top.mp htop`. Introduce `U l hl h`.

Establish `key : ∀ l' : ℝ, 0 < l' → l = (l' : ℂ) → ∃ l' : ℝ, 0 < l' ∧ (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = (l' : ℂ) * ⟪x, y⟫_ℂ) ∧ ∀ x ∈ U, A (LinearMap.adjoint A x) = (l' : ℂ) • x`. Introduce `l' hpos hl'`. Substitute `hl'` using the available equality. Use `⟨l', hpos, h, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `v`. Rewrite using `[← LinearMap.adjoint_inner_right, h x hx v, inner_smul_left, Complex.conj_ofReal]`. Distinguish the cases in `hU : U = ⊥`. Use `⟨1, one_pos, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx y`. Rewrite `hx` using `[hU, Submodule.mem_bot]`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Introduce `x hx`.

Rewrite `hx` using `[hU, Submodule.mem_bot]`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Take `⟨x, hxU, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU`. Establish `hxx` using `h x hxU x`.

Rewrite `hxx` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Establish `hn : (0 : ℝ) < ‖x‖ ^ 2` using `by positivity`. Establish `hlval : l = ((‖LinearMap.adjoint A x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ)`. Establish `hne : ((‖x‖ : ℂ)) ^ 2 ≠ 0`. Establish `: (‖x‖ : ℂ) ≠ 0` using `by exact_mod_cast (norm_ne_zero_iff.mpr hx0)`.

Conclude with `pow_ne_zero _ this`. Use `push_cast`. Rewrite using `[eq_div_iff hne]`. Conclude with `hxx.symm`. Apply `key _ _ hlval` to reduce the goal to its premises.

Break down `(div_nonneg (sq_nonneg ‖LinearMap.adjoint A x‖) hn.le).lt_or_eq with hlt | heq` into its components or cases. Conclude with `hlt`. It suffices to derive a contradiction. Apply `hl` to reduce the goal to its premises. Rewrite using `[hlval, ← heq]`.

Simplify using the standard rewrite rules.
-/
theorem adjoint_injective_surjective_and_positive_scalar :
    ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (A : E →ₗ[ℂ] F),
      (Function.Injective (LinearMap.adjoint A) → Function.Surjective A) ∧
      (∀ (U : Submodule ℂ F) (l : ℂ), l ≠ 0 →
        (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = l * ⟪x, y⟫_ℂ) →
        ∃ l' : ℝ, 0 < l' ∧
          (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = (l' : ℂ) * ⟪x, y⟫_ℂ) ∧
          ∀ x ∈ U, A (LinearMap.adjoint A x) = (l' : ℂ) • x) := by
  intro E F _ _ _ _ _ _ A
  constructor
  · intro hinj
    have hbot : (LinearMap.range A)ᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      have h0 : LinearMap.adjoint A v = 0 := by
        apply ext_inner_right ℂ
        intro e
        rw [LinearMap.adjoint_inner_left, inner_zero_left]
        exact (Submodule.mem_orthogonal' _ _).mp hv (A e) ⟨e, rfl⟩
      exact hinj (h0.trans (map_zero _).symm)
    have htop : LinearMap.range A = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
    exact LinearMap.range_eq_top.mp htop
  · intro U l hl h
    have key : ∀ l' : ℝ, 0 < l' → l = (l' : ℂ) →
        ∃ l' : ℝ, 0 < l' ∧
          (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = (l' : ℂ) * ⟪x, y⟫_ℂ) ∧
          ∀ x ∈ U, A (LinearMap.adjoint A x) = (l' : ℂ) • x := by
      intro l' hpos hl'
      subst hl'
      refine ⟨l', hpos, h, ?_⟩
      intro x hx
      apply ext_inner_right ℂ
      intro v
      rw [← LinearMap.adjoint_inner_right, h x hx v, inner_smul_left, Complex.conj_ofReal]
    by_cases hU : U = ⊥
    · refine ⟨1, one_pos, ?_, ?_⟩
      · intro x hx y
        rw [hU, Submodule.mem_bot] at hx
        subst hx
        simp
      · intro x hx
        rw [hU, Submodule.mem_bot] at hx
        subst hx
        simp
    · obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      have hxx := h x hxU x
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hxx
      have hn : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      have hlval : l = ((‖LinearMap.adjoint A x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) := by
        have hne : ((‖x‖ : ℂ)) ^ 2 ≠ 0 := by
          have : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx0)
          exact pow_ne_zero _ this
        push_cast
        rw [eq_div_iff hne]
        exact hxx.symm
      apply key _ _ hlval
      rcases (div_nonneg (sq_nonneg ‖LinearMap.adjoint A x‖) hn.le).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; apply hl; rw [hlval, ← heq]; simp

end GlobalTheory

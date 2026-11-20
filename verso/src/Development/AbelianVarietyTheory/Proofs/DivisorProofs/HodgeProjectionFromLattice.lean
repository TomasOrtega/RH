import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `W _ _ g Λ P F hspan hdim hR hF`. Use `set Ψ : (Λ →₀ ℂ) →ₗ[ℂ] W := Finsupp.linearCombination ℂ (fun x => P x) with hΨ`. Use `set Ψ' : (Λ →₀ ℂ) →ₗ[ℂ] (Fin g → ℂ) := Finsupp.linearCombination ℂ (fun x => (x : Fin g → ℂ)) with hΨ'`. Establish `hF' : ∀ c, Ψ c ∈ F ↔ Ψ' c = 0`. Introduce `c`.

Simplify `hF c` using `[hΨ, hΨ', Finsupp.linearCombination_apply]`. Establish `hsurj : Function.Surjective Ψ`. Rewrite using `[← LinearMap.range_eq_top, hΨ, Finsupp.range_linearCombination]`. Conclude with `hspan`. Establish `hker : LinearMap.ker Ψ ≤ LinearMap.ker Ψ'`.

Introduce `c hc`. Rewrite `hc`, the goal using `[LinearMap.mem_ker]`. Conclude with `(hF' c).1 (by rw [hc]; exact F.zero_mem)`. Set `Q : W →ₗ[ℂ] (Fin g → ℂ)` to `((LinearMap.ker Ψ).liftQ Ψ' hker).comp (Ψ.quotKerEquivOfSurjective hsurj).symm.toLinearMap`. Establish `hQ : ∀ c, Q (Ψ c) = Ψ' c`.

Introduce `c`. Establish `: (Ψ.quotKerEquivOfSurjective hsurj).symm (Ψ c) = (LinearMap.ker Ψ).mkQ c`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [Q, LinearMap.comp_apply, LinearEquiv.coe_coe, this]`.

Both sides reduce to the same expression. Establish `hQP : ∀ x, Q (P x) = x`. Introduce `x`. Use `hQ (Finsupp.single x 1)` as an intermediate fact. Simplify `this` using `[hΨ, hΨ']`.

Establish `hkerQ : LinearMap.ker Q = F`. Use extensionality with `w`. Take `⟨c, rfl⟩` from `hsurj w`. Rewrite using `[LinearMap.mem_ker, hQ, hF']`. Use `⟨Q, hkerQ, hQP, ?_⟩` and prove the remaining obligations.

Establish `hrange : LinearMap.range Q = ⊤`. Establish `h1 : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤ (LinearMap.range Q).restrictScalars ℝ`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Conclude with `⟨P ⟨x, hx⟩, hQP ⟨x, hx⟩⟩`.

Rewrite `h1` using `[hR]`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Conclude with `h1 (Submodule.mem_top : y ∈ (⊤ : Submodule ℝ (Fin g → ℂ)))`. Break down `Nat.eq_zero_or_pos g with hg | hg` into its components or cases.

Substitute `hg` using the available equality. Establish `hP0 : ∀ x, P x = 0`. Introduce `x`. Establish `: x = 0` using `Subsingleton.elim _ _`. Rewrite using `[this, map_zero]`.

Establish `hbot : (⊤ : Submodule ℂ W) = ⊥`. Rewrite using `[← hspan, eq_bot_iff, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Simplify using `[hP0 x]`. Use `haveI : Subsingleton W := by`.

Rewrite using `[← Submodule.subsingleton_iff ℂ]`. Conclude with `subsingleton_of_bot_eq_top hbot.symm`. Conclude with `Module.finrank_zero_of_subsingleton`. Use `haveI : FiniteDimensional ℂ W := Module.finite_of_finrank_pos (by omega)`. Use `LinearMap.finrank_range_add_finrank_ker Q` as an intermediate fact.

Rewrite `this` using `[hrange, finrank_top, Module.finrank_fin_fun, hkerQ, hdim]`. Use linear arithmetic over natural numbers and integers.
-/
theorem spanning_map_factors_through_quotient :
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W)
    (F : Submodule ℂ W), Submodule.span ℂ (Set.range P) = ⊤ → Module.finrank ℂ W = 2 * g →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ c : Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ F ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0) →
    ∃ Q : W →ₗ[ℂ] (Fin g → ℂ), LinearMap.ker Q = F ∧ (∀ x, Q (P x) = x) ∧ Module.finrank ℂ F = g := by
  intro W _ _ g Λ P F hspan hdim hR hF
  set Ψ : (Λ →₀ ℂ) →ₗ[ℂ] W := Finsupp.linearCombination ℂ (fun x => P x) with hΨ
  set Ψ' : (Λ →₀ ℂ) →ₗ[ℂ] (Fin g → ℂ) := Finsupp.linearCombination ℂ (fun x => (x : Fin g → ℂ)) with hΨ'
  have hF' : ∀ c, Ψ c ∈ F ↔ Ψ' c = 0 := by
    intro c
    simpa [hΨ, hΨ', Finsupp.linearCombination_apply] using hF c
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top, hΨ, Finsupp.range_linearCombination]
    exact hspan
  have hker : LinearMap.ker Ψ ≤ LinearMap.ker Ψ' := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    exact (hF' c).1 (by rw [hc]; exact F.zero_mem)
  let Q : W →ₗ[ℂ] (Fin g → ℂ) :=
    ((LinearMap.ker Ψ).liftQ Ψ' hker).comp (Ψ.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hQ : ∀ c, Q (Ψ c) = Ψ' c := by
    intro c
    have : (Ψ.quotKerEquivOfSurjective hsurj).symm (Ψ c) = (LinearMap.ker Ψ).mkQ c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [Q, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  have hQP : ∀ x, Q (P x) = x := by
    intro x
    have := hQ (Finsupp.single x 1)
    simpa [hΨ, hΨ'] using this
  have hkerQ : LinearMap.ker Q = F := by
    ext w
    obtain ⟨c, rfl⟩ := hsurj w
    rw [LinearMap.mem_ker, hQ, hF']
  refine ⟨Q, hkerQ, hQP, ?_⟩
  have hrange : LinearMap.range Q = ⊤ := by
    have h1 : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤ (LinearMap.range Q).restrictScalars ℝ := by
      rw [Submodule.span_le]
      intro x hx
      exact ⟨P ⟨x, hx⟩, hQP ⟨x, hx⟩⟩
    rw [hR] at h1
    rw [eq_top_iff]
    intro y _
    exact h1 (Submodule.mem_top : y ∈ (⊤ : Submodule ℝ (Fin g → ℂ)))
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    have hP0 : ∀ x, P x = 0 := by
      intro x
      have : x = 0 := Subsingleton.elim _ _
      rw [this, map_zero]
    have hbot : (⊤ : Submodule ℂ W) = ⊥ := by
      rw [← hspan, eq_bot_iff, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      simp [hP0 x]
    haveI : Subsingleton W := by
      rw [← Submodule.subsingleton_iff ℂ]
      exact subsingleton_of_bot_eq_top hbot.symm
    exact Module.finrank_zero_of_subsingleton
  · haveI : FiniteDimensional ℂ W := Module.finite_of_finrank_pos (by omega)
    have := LinearMap.finrank_range_add_finrank_ker Q
    rw [hrange, finrank_top, Module.finrank_fin_fun, hkerQ, hdim] at this
    omega

end GlobalTheory

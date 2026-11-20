import Mathlib
open Matrix

namespace GlobalTheory

open scoped Matrix.Norms.L2Operator in

/- English proof (translation)
Establish `hspec` using `spectrum.subset_circle_of_unitary (𝕜 := ℂ) hk`. Establish `hfin` using `Matrix.finite_spectrum k`. Establish `hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k)` using `fun f => hfin.continuousOn f`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ z ∈ spectrum ℂ k, p.eval z = Complex.log z := by`. Use `⟨Lagrange.interpolate hfin.toFinset id Complex.log, fun z hz => ?_⟩` and prove the remaining obligations.

Use `Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) (i := z) Complex.log (Set.injOn_id _) (by simpa using hz)` as an intermediate fact. Simplify using `using this`. Use `⟨cfc Complex.log k, p, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← cfc_star, ← cfc_neg]`. Use `cfc_congr fun z hz => ?_` and prove the remaining obligations.

Establish `h1 : ‖z‖ = 1` using `by simpa using hspec hz`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]`. Rewrite using `[← CFC.complex_exp_eq_normedSpace_exp, ← cfc_comp Complex.exp Complex.log k (hg := (Set.Finite.image _ hfin).continuousOn _) (hf := hcont _)]`. Establish `h0 : ∀ z ∈ spectrum ℂ k, (Complex.exp ∘ Complex.log) z = id z`. Introduce `z hz`.

Establish `h1 : ‖z‖ = 1` using `by simpa using hspec hz`. Establish `: z ≠ 0` using `by rintro rfl; simp at h1`. Simplify using `[Complex.exp_log this]`. Rewrite using `[cfc_congr h0, cfc_id ℂ k]`. Rewrite using `[← cfc_polynomial p k]`.

Conclude with `cfc_congr fun z hz => (hp z hz).symm`.
-/
theorem unitary_submonoid_exists_skewAdjoint_log_polynomial (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ)
    (hk : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      star X = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  classical
  have hspec := spectrum.subset_circle_of_unitary (𝕜 := ℂ) hk
  have hfin := Matrix.finite_spectrum k
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k) := fun f => hfin.continuousOn f
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ z ∈ spectrum ℂ k, p.eval z = Complex.log z := by
    refine ⟨Lagrange.interpolate hfin.toFinset id Complex.log, fun z hz => ?_⟩
    have := Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) (i := z) Complex.log
      (Set.injOn_id _) (by simpa using hz)
    simpa using this
  refine ⟨cfc Complex.log k, p, ?_, ?_, ?_⟩
  · rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    have h1 : ‖z‖ = 1 := by simpa using hspec hz
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
  · rw [← CFC.complex_exp_eq_normedSpace_exp, ← cfc_comp Complex.exp Complex.log k
      (hg := (Set.Finite.image _ hfin).continuousOn _) (hf := hcont _)]
    have h0 : ∀ z ∈ spectrum ℂ k, (Complex.exp ∘ Complex.log) z = id z := by
      intro z hz
      have h1 : ‖z‖ = 1 := by simpa using hspec hz
      have : z ≠ 0 := by rintro rfl; simp at h1
      simp [Complex.exp_log this]
    rw [cfc_congr h0, cfc_id ℂ k]
  · rw [← cfc_polynomial p k]
    exact cfc_congr fun z hz => (hp z hz).symm

/- English proof (translation)
Establish `hmem : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)` using `⟨hk, mul_eq_one_comm.mp hk⟩`. Take `⟨X, p, h1, h2, h3⟩` from `unitary_submonoid_exists_skewAdjoint_log_polynomial n k hmem`. Conclude with `⟨X, p, h1, h2, h3⟩`.
-/
theorem unitary_exists_skew_log (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ) (hk : kᴴ * k = 1) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  have hmem : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨hk, mul_eq_one_comm.mp hk⟩
  obtain ⟨X, p, h1, h2, h3⟩ := unitary_submonoid_exists_skewAdjoint_log_polynomial n k hmem
  exact ⟨X, p, h1, h2, h3⟩

end GlobalTheory

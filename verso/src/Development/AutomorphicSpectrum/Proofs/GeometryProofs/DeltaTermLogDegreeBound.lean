import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropFTop
import Development.AutomorphicSpectrum.RootSurvey.GeometrySurvey.ExistsTopDegreeCoefficientFormAndEqOnTopForms
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpSplit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpInert

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `Ψ _ _ N j p τ fr hj hp`. Use `⟨Bound₂.ep N j p fr, Bound₂.abs_ep_le hj hp fr, fun h => ?_, fun h => ?_, fun Q => Bound₂.delta_one hj p τ fr Q⟩` and prove the remaining obligations. Establish `e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) = fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)`. Use function extensionality and compare the values at `n`. Take `⟨σ, hσ⟩` from `h n`.

Rewrite using `[hσ, inv_pow, div_eq_inv_mul]`. Both sides reduce to the same expression. Unfold `Bound₂.ep`. Rewrite using `[e, (ep_split p j hp).tsum_eq, sub_self]`. Establish `e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) = fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1)`.

Use function extensionality and compare the values at `n`. Rewrite using `[inv_pow, div_eq_inv_mul]`. Use `congr 1`. Break down `hs : fr n with σ | σ` into its components or cases. Establish `: Odd n` using `(h n).1 ⟨σ, hs⟩`.

Rewrite using `[if_pos this.add_one]`. Both sides reduce to the same expression. Establish `: ¬ Odd n` using `fun ho => by`. Take `⟨σ', h'⟩` from `(h n).2 ho`. Rewrite `h'` using `[hs]`.

Consider the cases of `h'`. Rewrite using `[if_neg (by simpa [Nat.even_add_one] using this)]`. Both sides reduce to the same expression. Unfold `Bound₂.ep`. Rewrite using `[e, (ep_inert p N j hp hj).1.tsum_eq]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem deltaTerm_one : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ), j ≤ N → 2 ≤ p → ∃ e : ℝ, |e| ≤ N / ((p : ℝ) - 1) ∧ ((∀ n, ∃ σ, fr n = Sum.inl σ) → e = 0) ∧ ((∀ n, (∃ σ, fr n = Sum.inl σ) ↔ Odd n) → e = ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ ∀ Q : RP Ψ N, deltaTerm j p τ fr 1 Q = e * Real.log p * degFl Q := by
  intro Ψ _ _ N j p τ fr hj hp
  refine ⟨Bound₂.ep N j p fr, Bound₂.abs_ep_le hj hp fr, fun h => ?_, fun h => ?_,
    fun Q => Bound₂.delta_one hj p τ fr Q⟩
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1) := by
      funext n
      obtain ⟨σ, hσ⟩ := h n
      rw [hσ, inv_pow, div_eq_inv_mul]
      rfl
    unfold Bound₂.ep
    rw [e, (ep_split p j hp).tsum_eq, sub_self]
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1) := by
      funext n
      rw [inv_pow, div_eq_inv_mul]
      congr 1
      rcases hs : fr n with σ | σ
      · have : Odd n := (h n).1 ⟨σ, hs⟩
        rw [if_pos this.add_one]
        rfl
      · have : ¬ Odd n := fun ho => by
          obtain ⟨σ', h'⟩ := (h n).2 ho
          rw [hs] at h'
          cases h'
        rw [if_neg (by simpa [Nat.even_add_one] using this)]
        rfl
    unfold Bound₂.ep
    rw [e, (ep_inert p N j hp hj).1.tsum_eq]
    ring

end GlobalTheory.CompanionTheory.Ar.Flat

import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ σ τ _ u f M hu hf β hβ`. Establish `hs : HasSubst u` using `⟨fun i => by rw [hu i]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Rewrite using `[coeff_subst hs]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `d`.

Distinguish the cases in `hd : d.degree < M`. Simplify using `[hf d hd]`. Use `push_neg at hd`. Establish `hord : ((d.degree : ℕ) : ℕ∞) ≤ (d.prod fun s e => u s ^ e).order`. Unfold `Finsupp.prod`.

Use `le_trans ?_ (le_order_prod (fun s => u s ^ d s) d.support)` and prove the remaining obligations. Establish `hdeg : d.degree = ∑ i ∈ d.support, d i` using `rfl`. Rewrite using `[hdeg, Nat.cast_sum]`. Conclude with `Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero (d s) (hu s)`. Establish `h0 : coeff β (d.prod fun s e => u s ^ e) = 0`.

Apply `coeff_of_lt_order` to reduce the goal to its premises. Conclude with `lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le hβ hd)) hord`. Rewrite using `[h0, smul_zero]`.
-/
theorem coeff_subst_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Fintype σ] (u : σ → MvPowerSeries τ R)
      (f : MvPowerSeries σ R) (M : ℕ), (∀ i, constantCoeff (u i) = 0) →
      (∀ α : σ →₀ ℕ, α.degree < M → coeff α f = 0) →
      ∀ β : τ →₀ ℕ, β.degree < M → coeff β (subst u f) = 0 := by
  intro R _ σ τ _ u f M hu hf β hβ
  have hs : HasSubst u := ⟨fun i => by rw [hu i]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  rw [coeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d.degree < M
  · simp [hf d hd]
  · push_neg at hd
    have hord : ((d.degree : ℕ) : ℕ∞) ≤ (d.prod fun s e => u s ^ e).order := by
      unfold Finsupp.prod
      refine le_trans ?_ (le_order_prod (fun s => u s ^ d s) d.support)
      have hdeg : d.degree = ∑ i ∈ d.support, d i := rfl
      rw [hdeg, Nat.cast_sum]
      exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero (d s) (hu s)
    have h0 : coeff β (d.prod fun s e => u s ^ e) = 0 := by
      apply coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le hβ hd)) hord
    rw [h0, smul_zero]

end GlobalTheory

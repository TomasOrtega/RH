import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialCharSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionRestrictionTwoCharactersStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CharPowExp
open Polynomial

/- English proof (translation)
Introduce `i₀`. Assume the negation of the conclusion as `hne`. Establish `hm` using `GlobalTheory.T.exponential_polynomial_char_span G L hL h0 ι χ hχ P i₀ hne`. Establish `hz : (fun s : G => fun t : G => ∑ i, (P i).eval ((L (s * t) : ℝ) : ℂ) * ((χ i (s * t) : ℂˣ) : ℂ)) = fun _ => 0`. Use function extensionality and compare the values at `s t`.

Conclude with `h (s * t)`. Rewrite `hm` using `[hz, Set.range_const, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot]`. Use `congr_fun hm 1` as an intermediate fact. Simplify using `at this`.
-/
theorem charPoly_independent (G : Type) [CommGroup G] (L : G → ℝ) (hL : ∀ x y, L (x * y) = L x + L y) (h0 : ∃ t, L t ≠ 0)
    (ι : Type) [Fintype ι] (χ : ι → G →* ℂˣ) (hχ : Function.Injective χ) (P : ι → ℂ[X])
    (h : ∀ t, ∑ i, (P i).eval ((L t : ℝ) : ℂ) * ((χ i t : ℂˣ) : ℂ) = 0) : ∀ i, P i = 0 := by
  intro i₀
  by_contra hne
  have hm := GlobalTheory.T.exponential_polynomial_char_span G L hL h0 ι χ hχ P i₀ hne
  have hz : (fun s : G => fun t : G => ∑ i, (P i).eval ((L (s * t) : ℝ) : ℂ) * ((χ i (s * t) : ℂˣ) : ℂ))
      = fun _ => 0 := by
    funext s t; exact h (s * t)
  rw [hz, Set.range_const, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hm
  have := congr_fun hm 1
  simp at this

/- English proof (translation)
Introduce `T _ L hL h0 N K χ c hχ Φ hΦ`. Use `set P : Fin N → ℂ[X] := fun i => ∑ k : Fin (K + 1), C (c i k) * X ^ (k : ℕ) with hPdef`. Establish `hPeval : ∀ i x, (P i).eval x = ∑ k : Fin (K + 1), c i k * x ^ (k : ℕ)`. Introduce `i x`. Simplify using `[P, eval_finset_sum]`.

Establish `hcoeff : ∀ i (k : Fin (K + 1)), (P i).coeff k = c i k`. Introduce `i k`. Simplify using `only [P, finset_sum_coeff, coeff_C_mul, coeff_X_pow]`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Fin.val_eq_val, Ne.symm hb]`. Simplify using the standard rewrite rules. Establish `hΦ' : ∀ t, Φ t = ∑ i, (P i).eval ((L t : ℝ) : ℂ) * ((χ i t : ℂˣ) : ℂ)`. Introduce `t`.

Rewrite using `[hΦ]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hPeval, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring`. Establish `hPne : ∀ i k, c i k ≠ 0 → P i ≠ 0`. Introduce `i k hc hP`.

Apply `hc` to reduce the goal to its premises. Rewrite using `[← hcoeff, hP, coeff_zero]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ hinv i k hc`. Establish `hQ` using `charPoly_independent T L hL h0 (Fin N) χ hχ (fun i => C (((χ i γ : ℂˣ) : ℂ) - 1) * P i) (by`.

Introduce `t`. Establish `h1` using `hinv t`. Rewrite `h1` using `[hΦ', hΦ']`. Simplify using `only [eval_mul, eval_C]`. Establish `h2 : ∀ i, (P i).eval ((L (γ * t) : ℝ) : ℂ) * ((χ i (γ * t) : ℂˣ) : ℂ) = (P i).eval ((L t : ℝ) : ℂ) * ((χ i γ : ℂˣ) : ℂ) * ((χ i t : ℂˣ) : ℂ)`.

Introduce `i`. Rewrite using `[hL, hγ, zero_add, map_mul, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h2] at h1`. Rewrite `h1` using `[← sub_eq_zero]`.

Rewrite using `[← h1, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring) i`. Break down `mul_eq_zero.1 hQ with h | h` into its components or cases. Rewrite `h` using `[C_eq_zero, sub_eq_zero]`. Conclude with `Units.val_eq_one.1 h`.

Conclude with `absurd h (hPne i k hc)`. Introduce `i k hc`. Establish `hm` using `GlobalTheory.T.exponential_polynomial_char_span T L hL h0 (Fin N) χ hχ P i (hPne i k hc)`. Establish `hz : (fun s : T => fun t : T => ∑ j, (P j).eval ((L (s * t) : ℝ) : ℂ) * ((χ j (s * t) : ℂˣ) : ℂ)) = fun s t => Φ (s * t)`. Use function extensionality and compare the values at `s t`.

Rewrite using `[hΦ']`. Rewrite `hm` using `[hz]`. Take `⟨d, hd⟩` from `(Finsupp.mem_span_range_iff_exists_finsupp).1 hm`. Use `⟨d.support.card, fun j => (d.support.equivFin.symm j : T), fun j => d (d.support.equivFin.symm j : T), fun t => ?_⟩` and prove the remaining obligations. Establish `ht` using `congr_fun hd t`.

Rewrite using `[← ht, Finsupp.sum, Finset.sum_apply]`. Rewrite using `[Equiv.sum_comp d.support.equivFin.symm (fun x : d.support => d x * Φ ((x : T) * t))]`. Rewrite using `[Finset.sum_coe_sort d.support (fun x => d x * Φ (x * t))]`. Simplify using `[smul_eq_mul]`. Introduce `H ψ₁ ψ₂ hH hloc i k hc`.

Establish `hr` using `GlobalTheory.T.exponential_polynomial_independent (charPoly_independent) T L hL N χ P hχ H ψ₁ ψ₂ hH (by`. Introduce `s`. Take `⟨p, q, hpq⟩` from `hloc s`. Conclude with `⟨p, q, fun x hx => by rw [← hΦ']; exact hpq x hx⟩) i (hPne i k hc)`. Use `⟨?_, hr.2⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hk`. Apply `hc` to reduce the goal to its premises. Rewrite using `[← hcoeff, eq_C_of_derivative_eq_zero hr.1, coeff_C, if_neg hk]`.
-/
theorem charPow_expansion : ∀ (T : Type) [CommGroup T] (L : T → ℝ), (∀ x y, L (x * y) = L x + L y) → (∃ t, L t ≠ 0) → ∀ (N K : ℕ) (χ : Fin N → T →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ → ∀ Φ : T → ℂ, (∀ t, Φ t = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((L t : ℝ) : ℂ) ^ (k : ℕ)) → (∀ γ, L γ = 0 → (∀ t, Φ (γ * t) = Φ t) → ∀ i k, c i k ≠ 0 → χ i γ = 1) ∧ (∀ i k, c i k ≠ 0 → ∃ (n : ℕ) (s : Fin n → T) (b : Fin n → ℂ), ∀ t, ((χ i t : ℂˣ) : ℂ) = ∑ j, b j * Φ (s j * t)) ∧ ∀ (H : Subgroup T) (ψ₁ ψ₂ : T →* ℂˣ), (∃ x ∈ H, L x ≠ 0) → (∀ s, ∃ p q : ℂ, ∀ x ∈ H, Φ (x * s) = p * ((ψ₁ x : ℂˣ) : ℂ) + q * ((ψ₂ x : ℂˣ) : ℂ)) → ∀ i k, c i k ≠ 0 → (k : ℕ) = 0 ∧ ((∀ x ∈ H, χ i x = ψ₁ x) ∨ ∀ x ∈ H, χ i x = ψ₂ x) := by
  intro T _ L hL h0 N K χ c hχ Φ hΦ
  set P : Fin N → ℂ[X] := fun i => ∑ k : Fin (K + 1), C (c i k) * X ^ (k : ℕ) with hPdef
  have hPeval : ∀ i x, (P i).eval x = ∑ k : Fin (K + 1), c i k * x ^ (k : ℕ) := by
    intro i x; simp [P, eval_finset_sum]
  have hcoeff : ∀ i (k : Fin (K + 1)), (P i).coeff k = c i k := by
    intro i k
    simp only [P, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Fin.val_eq_val, Ne.symm hb]
    · simp
  have hΦ' : ∀ t, Φ t = ∑ i, (P i).eval ((L t : ℝ) : ℂ) * ((χ i t : ℂˣ) : ℂ) := by
    intro t; rw [hΦ]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [hPeval, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
  have hPne : ∀ i k, c i k ≠ 0 → P i ≠ 0 := by
    intro i k hc hP; apply hc; rw [← hcoeff, hP, coeff_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ hinv i k hc
    have hQ := charPoly_independent T L hL h0 (Fin N) χ hχ (fun i => C (((χ i γ : ℂˣ) : ℂ) - 1) * P i) (by
      intro t
      have h1 := hinv t
      rw [hΦ', hΦ'] at h1
      simp only [eval_mul, eval_C]
      have h2 : ∀ i, (P i).eval ((L (γ * t) : ℝ) : ℂ) * ((χ i (γ * t) : ℂˣ) : ℂ)
          = (P i).eval ((L t : ℝ) : ℂ) * ((χ i γ : ℂˣ) : ℂ) * ((χ i t : ℂˣ) : ℂ) := by
        intro i; rw [hL, hγ, zero_add, map_mul, Units.val_mul]; ring
      simp only [h2] at h1
      rw [← sub_eq_zero] at h1
      rw [← h1, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring) i
    rcases mul_eq_zero.1 hQ with h | h
    · rw [C_eq_zero, sub_eq_zero] at h; exact Units.val_eq_one.1 h
    · exact absurd h (hPne i k hc)
  · intro i k hc
    have hm := GlobalTheory.T.exponential_polynomial_char_span T L hL h0 (Fin N) χ hχ P i (hPne i k hc)
    have hz : (fun s : T => fun t : T => ∑ j, (P j).eval ((L (s * t) : ℝ) : ℂ) * ((χ j (s * t) : ℂˣ) : ℂ))
        = fun s t => Φ (s * t) := by
      funext s t; rw [hΦ']
    rw [hz] at hm
    obtain ⟨d, hd⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hm
    refine ⟨d.support.card, fun j => (d.support.equivFin.symm j : T),
      fun j => d (d.support.equivFin.symm j : T), fun t => ?_⟩
    have ht := congr_fun hd t
    rw [← ht, Finsupp.sum, Finset.sum_apply]
    rw [Equiv.sum_comp d.support.equivFin.symm (fun x : d.support => d x * Φ ((x : T) * t))]
    rw [Finset.sum_coe_sort d.support (fun x => d x * Φ (x * t))]
    simp [smul_eq_mul]
  · intro H ψ₁ ψ₂ hH hloc i k hc
    have hr := GlobalTheory.T.exponential_polynomial_independent (charPoly_independent) T L hL N χ P hχ H ψ₁ ψ₂ hH (by
      intro s; obtain ⟨p, q, hpq⟩ := hloc s
      exact ⟨p, q, fun x hx => by rw [← hΦ']; exact hpq x hx⟩) i (hPne i k hc)
    refine ⟨?_, hr.2⟩
    by_contra hk
    apply hc
    rw [← hcoeff, eq_C_of_derivative_eq_zero hr.1, coeff_C, if_neg hk]
end GlobalTheory.CharPowExp

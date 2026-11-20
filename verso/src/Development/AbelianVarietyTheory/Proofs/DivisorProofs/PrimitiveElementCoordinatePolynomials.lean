import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `F using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, by simp⟩`. Consider the case `insert a F ha ih`. Take `⟨Δ₀, hΔ₀, hF₀⟩` from `ih (fun y hy => hF y (Finset.mem_insert_of_mem hy))`. Take `⟨r, s, hrs⟩` from `(IntermediateField.mem_adjoin_range_iff k t a).1 (hF a (Finset.mem_insert_self a F))`.

Distinguish the cases in `hs : MvPolynomial.aeval t s = 0`. Use `⟨Δ₀, hΔ₀, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Break down `Finset.mem_insert.1 hy with rfl | hy` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite using `[hrs, hs, div_zero]`. Simplify using the standard rewrite rules. Conclude with `hF₀ y hy`. Use `⟨Δ₀ * s, by simp [hΔ₀, hs], ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Break down `Finset.mem_insert.1 hy with rfl | hy` into its components or cases. Use `⟨Δ₀ * r, ?_⟩` and prove the remaining obligations. Rewrite using `[hrs, map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts. Take `⟨r', hr'⟩` from `hF₀ y hy`.

Use `⟨r' * s, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hr']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem commonDenom_finset {k C : Type} [Field k] [Field C] [Algebra k C] {d : ℕ}
    (t : Fin d → C) (F : Finset C)
    (hF : ∀ y ∈ F, y ∈ IntermediateField.adjoin k (Set.range t)) :
    ∃ Δ : MvPolynomial (Fin d) k, MvPolynomial.aeval t Δ ≠ 0 ∧
      ∀ y ∈ F, ∃ r : MvPolynomial (Fin d) k, MvPolynomial.aeval t r = MvPolynomial.aeval t Δ * y := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a F ha ih =>
    obtain ⟨Δ₀, hΔ₀, hF₀⟩ := ih (fun y hy => hF y (Finset.mem_insert_of_mem hy))
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_range_iff k t a).1
      (hF a (Finset.mem_insert_self a F))
    by_cases hs : MvPolynomial.aeval t s = 0
    · refine ⟨Δ₀, hΔ₀, ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · refine ⟨0, ?_⟩
        rw [hrs, hs, div_zero]; simp
      · exact hF₀ y hy
    · refine ⟨Δ₀ * s, by simp [hΔ₀, hs], ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · refine ⟨Δ₀ * r, ?_⟩
        rw [hrs, map_mul, map_mul]
        field_simp
      · obtain ⟨r', hr'⟩ := hF₀ y hy
        refine ⟨r' * s, ?_⟩
        rw [map_mul, map_mul, hr']; ring

/- English proof (translation)
Introduce `k C _ _ _ d m t θ x hθ hx`. Use `set K0 := IntermediateField.adjoin k (Set.range t) with hK0`. Establish `hp : ∀ j, ∃ p : K0[X], Polynomial.aeval θ p = x j`. Introduce `j`. Establish `h` using `hx j`.

Rewrite `h` using `[← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθ, Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, hp⟩` from `h`. Conclude with `⟨p, hp⟩`. Use `choose p hpx using hp`. Set `F : Finset C` to `Finset.univ.biUnion (fun j => (p j).support.image (fun i => (((p j).coeff i : K0) : C)))`.

Establish `hF : ∀ y ∈ F, y ∈ K0`. Introduce `y hy`. Simplify using `only [F, Finset.mem_biUnion, Finset.mem_image] at hy`. Take `⟨j, -, i, -, rfl⟩` from `hy`. Conclude with `((p j).coeff i).2`.

Take `⟨Δ, hΔ, hΔF⟩` from `commonDenom_finset t F hF`. Establish `hQ : ∀ j, ∃ Q : Polynomial (MvPolynomial (Fin d) k), Q.map (MvPolynomial.aeval t).toRingHom = Polynomial.C (MvPolynomial.aeval t Δ) * (p j).map K0.val.toRingHom`. Introduce `j`. Rewrite using `[← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`.

Rewrite using `[Polynomial.coeff_C_mul, Polynomial.coeff_map]`. Distinguish the cases in `hn : n ∈ (p j).support`. Take `⟨r, hr⟩` from `hΔF _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_image.2 ⟨n, hn, rfl⟩⟩)`. Conclude with `⟨r, by simpa using hr⟩`. Rewrite using `[Polynomial.notMem_support_iff.1 hn]`.

Conclude with `⟨0, by simp⟩`. Use `choose Q hQ using hQ`. Use `⟨Δ, Q, hΔ, ?_⟩` and prove the remaining obligations. Introduce `j`. Rewrite using `[← Polynomial.eval_map, hQ j, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map, ← hpx j, Polynomial.aeval_def]`.

Both sides reduce to the same expression.
-/
theorem commonDenominator :
    ∀ (k C : Type) [Field k] [Field C] [Algebra k C] (d m : ℕ) (t : Fin d → C) (θ : C)
      (x : Fin m → C), IsAlgebraic (IntermediateField.adjoin k (Set.range t)) θ →
      (∀ j, x j ∈ IntermediateField.adjoin (IntermediateField.adjoin k (Set.range t)) {θ}) →
      ∃ (Δ : MvPolynomial (Fin d) k) (Q : Fin m → Polynomial (MvPolynomial (Fin d) k)),
        MvPolynomial.aeval t Δ ≠ 0 ∧
        ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) =
          MvPolynomial.aeval t Δ * x j := by
  intro k C _ _ _ d m t θ x hθ hx
  classical
  set K0 := IntermediateField.adjoin k (Set.range t) with hK0
  have hp : ∀ j, ∃ p : K0[X], Polynomial.aeval θ p = x j := by
    intro j
    have h := hx j
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθ,
      Algebra.adjoin_singleton_eq_range_aeval] at h
    obtain ⟨p, hp⟩ := h
    exact ⟨p, hp⟩
  choose p hpx using hp
  let F : Finset C := Finset.univ.biUnion
    (fun j => (p j).support.image (fun i => (((p j).coeff i : K0) : C)))
  have hF : ∀ y ∈ F, y ∈ K0 := by
    intro y hy
    simp only [F, Finset.mem_biUnion, Finset.mem_image] at hy
    obtain ⟨j, -, i, -, rfl⟩ := hy
    exact ((p j).coeff i).2
  obtain ⟨Δ, hΔ, hΔF⟩ := commonDenom_finset t F hF
  have hQ : ∀ j, ∃ Q : Polynomial (MvPolynomial (Fin d) k),
      Q.map (MvPolynomial.aeval t).toRingHom =
        Polynomial.C (MvPolynomial.aeval t Δ) * (p j).map K0.val.toRingHom := by
    intro j
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
    by_cases hn : n ∈ (p j).support
    · obtain ⟨r, hr⟩ := hΔF _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
        Finset.mem_image.2 ⟨n, hn, rfl⟩⟩)
      exact ⟨r, by simpa using hr⟩
    · rw [Polynomial.notMem_support_iff.1 hn]
      exact ⟨0, by simp⟩
  choose Q hQ using hQ
  refine ⟨Δ, Q, hΔ, ?_⟩
  intro j
  rw [← Polynomial.eval_map, hQ j, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
    ← hpx j, Polynomial.aeval_def]
  rfl

end GlobalTheory

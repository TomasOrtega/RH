import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementD

namespace Formalism.InvariantFactorPaths.L4

open Finset

/- English proof (translation)
Introduce `s ka β c h1 h2`. Establish `key : ∀ a, a < s → ka a + ∑ a' ∈ range (a + 1), (β a' : ℤ) ≤ c`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero`.

Introduce `ha`. Simplify using `using h2 ha`. Consider the case `succ a ih`. Introduce `ha`. Establish `h3` using `h1 a ha`.

Establish `h4` using `ih (by omega)`. Rewrite using `[Finset.sum_range_succ]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `clear h2`. Proceed by induction on `s with`.

Consider the case `zero => simp`. Consider the case `succ s ihs`. Establish `IH` using `ihs (fun i hi => h1 i (by omega)) (fun a ha => key a (by omega))`. Establish `hk` using `key s (by omega)`. Rewrite `hk` using `[Finset.sum_range_succ]`.

Establish `hinner : ∑ a ∈ range s, ((β a : ℤ) + 1) * (β s : ℤ) = (∑ a ∈ range s, (β a : ℤ) + s) * β s`. Rewrite using `[← Finset.sum_mul, Finset.sum_add_distrib]`. Simplify using the standard rewrite rules. Simplify using `only [Finset.sum_range_succ, hinner]`. Establish `hb : (0 : ℤ) ≤ β s` using `Nat.cast_nonneg _`.

Establish `hs : (0 : ℤ) ≤ s` using `Nat.cast_nonneg _`. Use polynomial arithmetic with `[mul_nonneg hb (sub_nonneg.mpr hk), mul_nonneg hb hs]`.
-/
theorem eArith_ge : ∀ (s : ℕ) (ka : ℕ → ℤ) (β : ℕ → ℕ) (c : ℤ),
    (∀ i, i + 1 < s → ka (i + 1) + β (i + 1) ≤ ka i) → (0 < s → ka 0 + β 0 ≤ c) →
    (∑ a ∈ range s, (β a : ℤ)) ≤
      (c - (∑ a ∈ range s, (β a : ℤ)) + 1) * (∑ a ∈ range s, (β a : ℤ)) - (∑ a ∈ range s, (β a : ℤ) * ka a) +
        ∑ b ∈ range s, ∑ a ∈ range b, ((β a : ℤ) + 1) * (β b : ℤ) := by
  intro s ka β c h1 h2
  have key : ∀ a, a < s → ka a + ∑ a' ∈ range (a + 1), (β a' : ℤ) ≤ c := by
    intro a
    induction a with
    | zero =>
      intro ha
      simpa using h2 ha
    | succ a ih =>
      intro ha
      have h3 := h1 a ha
      have h4 := ih (by omega)
      rw [Finset.sum_range_succ]
      linarith
  clear h2
  induction s with
  | zero => simp
  | succ s ihs =>
    have IH := ihs (fun i hi => h1 i (by omega)) (fun a ha => key a (by omega))
    have hk := key s (by omega)
    rw [Finset.sum_range_succ] at hk
    have hinner : ∑ a ∈ range s, ((β a : ℤ) + 1) * (β s : ℤ) = (∑ a ∈ range s, (β a : ℤ) + s) * β s := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      simp
    simp only [Finset.sum_range_succ, hinner]
    have hb : (0 : ℤ) ≤ β s := Nat.cast_nonneg _
    have hs : (0 : ℤ) ≤ s := Nat.cast_nonneg _
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hk), mul_nonneg hb hs]

/- English proof (translation)
Introduce `s ka β c h1 h2 h3`. Establish `h4` using `eArith_ge s ka β c h1 h2`. Establish `h5 : (1 : ℤ) ≤ ∑ a ∈ range s, (β a : ℤ)` using `by exact_mod_cast h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exponent_arithmetic_holds : EArith := by
  intro s ka β c h1 h2 h3
  have h4 := eArith_ge s ka β c h1 h2
  have h5 : (1 : ℤ) ≤ ∑ a ∈ range s, (β a : ℤ) := by exact_mod_cast h3
  linarith

end Formalism.InvariantFactorPaths.L4

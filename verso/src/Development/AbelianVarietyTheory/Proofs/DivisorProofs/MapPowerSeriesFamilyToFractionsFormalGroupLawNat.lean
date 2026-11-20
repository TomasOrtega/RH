import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro i`. Simplify using `[nmul]`. Consider the case `succ n ih`. Introduce `i`.

Establish `h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0`. Introduce `j`. Consider the cases of `j with`. Consider the case `inl j => exact ih j`. Consider the case `inr j => simp`.

Use `show constantCoeff ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1] (fun _ => 0) i) = 0`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)`.
-/
theorem constantCoeff_nmul_zero {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ n ih =>
    intro i
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0 := by
      intro j; cases j with
      | inl j => exact ih j
      | inr j => simp
    show constantCoeff ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1]
      (fun _ => 0) i) = 0
    rw [Function.iterate_succ_apply']
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

/- English proof (translation)
Introduce `R S _ _ _ d μ hμ n`. Proceed by induction on `n with`. Consider the case `zero => funext i`. Simplify using `[up, nmul]`. Consider the case `succ n ih`.

Establish `h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0`. Introduce `j`. Consider the cases of `j with`. Consider the case `inl j => exact constantCoeff_nmul_zero μ hμ n j`. Consider the case `inr j => simp`.

Use function extensionality and compare the values at `i`. Use `show map (algebraMap R S) ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1] (fun _ => 0) i) = (fun v : Fin d → MvPowerSeries (Fin d) S => op (up S μ) v fun i => X i)^[n + 1] (fun _ => 0) i`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply']`. Express the relevant statement in the definitionally equal form `map (algebraMap R S) (subst (Sum.elim (nmul μ n) fun i => X i) (μ i)) =`. Substitute `(Sum.elim (nmul (up S μ) n) fun i => X i) (up S μ i)` using the available equality.

Rewrite using `[map_subst (hasSubst_of_constantCoeff_zero h0), ← ih]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Consider the cases of `j with`. Consider the case `inl j => rfl`.

Consider the case `inr j => simp`.
-/
theorem up_nmul : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) → ∀ n : ℕ, up S (nmul μ n) = nmul (up S μ) n := by
  intro R S _ _ _ d μ hμ n
  induction n with
  | zero => funext i; simp [up, nmul]
  | succ n ih =>
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0 := by
      intro j; cases j with
      | inl j => exact constantCoeff_nmul_zero μ hμ n j
      | inr j => simp
    funext i
    show map (algebraMap R S) ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1]
      (fun _ => 0) i) = (fun v : Fin d → MvPowerSeries (Fin d) S => op (up S μ) v fun i => X i)^[n + 1]
      (fun _ => 0) i
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change map (algebraMap R S) (subst (Sum.elim (nmul μ n) fun i => X i) (μ i)) =
      subst (Sum.elim (nmul (up S μ) n) fun i => X i) (up S μ i)
    rw [map_subst (hasSubst_of_constantCoeff_zero h0), ← ih]
    congr 1
    funext j
    cases j with
    | inl j => rfl
    | inr j => simp

end GlobalTheory.QLog

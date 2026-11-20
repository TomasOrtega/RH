import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C r => simp [aeval_C]`. Consider the case `add p q hp hq`. Establish `h` using `dvd_add hp hq`. Rewrite using `[map_add]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p c hp`. Rewrite using `[map_mul, aeval_X]`. Establish `h2 : (X b - X a : MvPolynomial σ ℝ) ∣ X c - Function.update X b (X a) c`.

Distinguish the cases in `h : c = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`. Establish `e : p * X c - aeval (Function.update X b (X a)) p * Function.update X b (X a) c = (p - aeval (Function.update X b (X a)) p) * X c + aeval (Function.update X b (X a)) p * (X c - Function.update X b (X a) c)` using `by ring`.

Rewrite using `[e]`. Conclude with `dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right h2 _)`.
-/
theorem X_sub_X_dvd_sub_aeval_update_variable {σ : Type} [DecidableEq σ] (a b : σ) (P : MvPolynomial σ ℝ) :
    (X b - X a : MvPolynomial σ ℝ) ∣ P - aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [aeval_C]
  | add p q hp hq =>
    have h := dvd_add hp hq
    rw [map_add]
    convert h using 1
    ring
  | mul_X p c hp =>
    rw [map_mul, aeval_X]
    have h2 : (X b - X a : MvPolynomial σ ℝ) ∣ X c - Function.update X b (X a) c := by
      by_cases h : c = b
      · subst h; simp
      · simp [Function.update_of_ne h]
    have e : p * X c - aeval (Function.update X b (X a)) p * Function.update X b (X a) c
        = (p - aeval (Function.update X b (X a)) p) * X c
          + aeval (Function.update X b (X a)) p * (X c - Function.update X b (X a) c) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right h2 _)

/- English proof (translation)
Introduce `σ _ a b hab P hP`. Establish `hcomp : (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) ∘ (Equiv.swap a b) = Function.update X b (X a)`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply]`. Distinguish the cases in `hia : i = a`.

Substitute `hia` using the available equality. Rewrite using `[Equiv.swap_apply_left, Function.update_self, Function.update_of_ne hab]`. Distinguish the cases in `hib : i = b`. Substitute `hib` using the available equality. Rewrite using `[Equiv.swap_apply_right, Function.update_of_ne hab, Function.update_self]`.

Rewrite using `[Equiv.swap_apply_of_ne_of_ne hia hib]`. Establish `h1 : aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P = - aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P`. Use `congrArg (aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a))) hP` as an intermediate fact. Rewrite `this` using `[aeval_rename, hcomp, map_neg]`. Conclude with `this`.

Establish `h0 : aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P = 0` using `self_eq_neg.mp h1`. Use `X_sub_X_dvd_sub_aeval_update_variable a b P` as an intermediate fact. Rewrite `this` using `[h0, sub_zero]`. Then use the resulting hypothesis.
-/
theorem swap_odd_dvd : ∀ {σ : Type} [DecidableEq σ] (a b : σ), a ≠ b → ∀ P : MvPolynomial σ ℝ,
    rename (Equiv.swap a b) P = -P → (X b - X a : MvPolynomial σ ℝ) ∣ P := by
  intro σ _ a b hab P hP
  have hcomp : (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) ∘ (Equiv.swap a b)
      = Function.update X b (X a) := by
    funext i
    simp only [Function.comp_apply]
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, Function.update_self, Function.update_of_ne hab]
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, Function.update_of_ne hab, Function.update_self]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
  have h1 : aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P = - aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P := by
    have := congrArg (aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a))) hP
    rw [aeval_rename, hcomp, map_neg] at this
    exact this
  have h0 : aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P = 0 := self_eq_neg.mp h1
  have := X_sub_X_dvd_sub_aeval_update_variable a b P
  rwa [h0, sub_zero] at this
end GlobalTheory

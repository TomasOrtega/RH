import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add p r hp hr`. Use `dvd_add hp hr` as an intermediate fact. Simplify using `only [map_add]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p i hp`. Establish `hi : a ∣ (![u, w] i) - (![u', w'] i)` using `by fin_cases i`. Simplify using `using hu`.

Simplify using `using hw`. Use `dvd_add (hp.mul_right (![u, w] i)) (hi.mul_left (MvPolynomial.aeval ![u', w'] p))` as an intermediate fact. Simplify using `only [map_mul, MvPolynomial.aeval_X]`. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dvd_aeval_sub_aeval_two {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a u w u' w' : A) (hu : a ∣ u - u') (hw : a ∣ w - w') (P : MvPolynomial (Fin 2) K) :
    a ∣ MvPolynomial.aeval ![u, w] P - MvPolynomial.aeval ![u', w'] P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr =>
    have := dvd_add hp hr
    simp only [map_add]
    convert this using 1
    ring
  | mul_X p i hp =>
    have hi : a ∣ (![u, w] i) - (![u', w'] i) := by
      fin_cases i
      · simpa using hu
      · simpa using hw
    have := dvd_add (hp.mul_right (![u, w] i)) (hi.mul_left (MvPolynomial.aeval ![u', w'] p))
    simp only [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

/- English proof (translation)
Establish `hu : IsUnit (1 + X : ℂ_[q]⟦X⟧)`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Simplify using the standard rewrite rules. Unfold `DT at hD`. Rewrite `hD` using `[hu.dvd_mul_left, X_pow_dvd_iff]`.

Rewrite using `[X_pow_dvd_iff]`. Introduce `m hm`. Consider the cases of `m with`. Consider the case `zero => simpa using h0`. Consider the case `succ k`.

Use `hD k (by omega)` as an intermediate fact. Rewrite `this` using `[coeff_derivative]`. Establish `hk : ((k : ℂ_[q]) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero k`. Conclude with `(mul_eq_zero.mp this).resolve_right hk`.
-/
theorem X_pow_succ_dvd_of_DT {q : ℕ} [Fact q.Prime] (f : ℂ_[q]⟦X⟧) (n : ℕ)
    (h0 : constantCoeff f = 0) (hD : (X : ℂ_[q]⟦X⟧) ^ n ∣ DT f) :
    (X : ℂ_[q]⟦X⟧) ^ (n + 1) ∣ f := by
  have hu : IsUnit (1 + X : ℂ_[q]⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  unfold DT at hD
  rw [hu.dvd_mul_left, X_pow_dvd_iff] at hD
  rw [X_pow_dvd_iff]
  intro m hm
  cases m with
  | zero => simpa using h0
  | succ k =>
    have := hD k (by omega)
    rw [coeff_derivative] at this
    have hk : ((k : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp this).resolve_right hk

/- English proof (translation)
Introduce `q _ P₁ P₂ u w u' w' h1 h2 h3 h4 hu hw`. Establish `hsub : ∀ f g : ℂ_[q]⟦X⟧, DT (f - g) = DT f - DT g`. Introduce `f g`. Unfold `DT`. Rewrite using `[map_sub, mul_sub]`.

Establish `key : ∀ n : ℕ, (X : ℂ_[q]⟦X⟧) ^ n ∣ u - u' ∧ (X : ℂ_[q]⟦X⟧) ^ n ∣ w - w'`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Prove the components needed by the constructor for the conclusion. Apply `X_pow_succ_dvd_of_DT` to reduce the goal to its premises. Rewrite using `[map_sub, hu, sub_self]`. Rewrite using `[hsub, h1, h3]`. Conclude with `dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _`.

Apply `X_pow_succ_dvd_of_DT` to reduce the goal to its premises. Rewrite using `[map_sub, hw, sub_self]`. Rewrite using `[hsub, h2, h4]`. Conclude with `dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[← sub_eq_zero]`. Use extensionality with `n`. Simplify using `using X_pow_dvd_iff.mp (key (n + 1)).1 n (by omega)`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `n`.

Simplify using `using X_pow_dvd_iff.mp (key (n + 1)).2 n (by omega)`.
-/
theorem ode_unique : ∀ (q : ℕ) [Fact q.Prime] (P₁ P₂ : MvPolynomial (Fin 2) ℂ_[q]) (u w u' w' : ℂ_[q]⟦X⟧), DT u = MvPolynomial.aeval ![u, w] P₁ → DT w = MvPolynomial.aeval ![u, w] P₂ → DT u' = MvPolynomial.aeval ![u', w'] P₁ → DT w' = MvPolynomial.aeval ![u', w'] P₂ → constantCoeff u = constantCoeff u' → constantCoeff w = constantCoeff w' → u = u' ∧ w = w' := by
  intro q _ P₁ P₂ u w u' w' h1 h2 h3 h4 hu hw
  have hsub : ∀ f g : ℂ_[q]⟦X⟧, DT (f - g) = DT f - DT g := by
    intro f g
    unfold DT
    rw [map_sub, mul_sub]
  have key : ∀ n : ℕ, (X : ℂ_[q]⟦X⟧) ^ n ∣ u - u' ∧ (X : ℂ_[q]⟦X⟧) ^ n ∣ w - w' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      constructor
      · apply X_pow_succ_dvd_of_DT
        · rw [map_sub, hu, sub_self]
        · rw [hsub, h1, h3]; exact dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _
      · apply X_pow_succ_dvd_of_DT
        · rw [map_sub, hw, sub_self]
        · rw [hsub, h2, h4]; exact dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _
  constructor
  · rw [← sub_eq_zero]
    ext n
    simpa using X_pow_dvd_iff.mp (key (n + 1)).1 n (by omega)
  · rw [← sub_eq_zero]
    ext n
    simpa using X_pow_dvd_iff.mp (key (n + 1)).2 n (by omega)

end GlobalTheory.MomOne

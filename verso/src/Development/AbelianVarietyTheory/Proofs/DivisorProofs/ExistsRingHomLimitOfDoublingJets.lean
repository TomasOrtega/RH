import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivCompM

open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

/- English proof (translation)
Establish `hdv : ∀ (n : ℕ) (p q : PowerSeries R), (X : PowerSeries R) ^ n ∣ p - q → ∀ k, k < n → coeff k p = coeff k q`. Introduce `n p q h k hk`. Use `(PowerSeries.X_pow_dvd_iff.mp h) k hk` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hstab : ∀ f k j, k ≤ j + 1 → coeff k (φ j f) = coeff k (φ k f)`.

Introduce `f k j hkj`. Break down `Nat.lt_or_ge j k with h | h` into its components or cases. Establish `hk : k = j + 1` using `by omega`. Substitute `hk` using the available equality. Conclude with `(hdv _ _ _ (hc j f) (j + 1) (by omega)).symm`.

Proceed by induction on `j, h using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ j hj ih`. Rewrite using `[hdv _ _ _ (hc j f) k (by omega)]`. Conclude with `ih (by omega)`.

Set `g : A → PowerSeries R` to `fun f => PowerSeries.mk fun k => coeff k (φ k f)`. Establish `hg : ∀ f k j, k ≤ j + 1 → coeff k (g f) = coeff k (φ j f)`. Introduce `f k j hkj`. Simplify using `only [g, PowerSeries.coeff_mk]`. Conclude with `(hstab f k j hkj).symm`.

Establish `gmul : ∀ f h, g (f * h) = g f * g h`. Introduce `f h`. Use extensionality with `k`. Rewrite using `[hg _ k k (by omega), hdv _ _ _ ((hφ k).1.1 f h) k (by omega), coeff_mul, coeff_mul]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations.

Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[hg f x.1 k (by omega), hg h x.2 k (by omega)]`. Establish `gadd : ∀ f h, g (f + h) = g f + g h`. Introduce `f h`. Use extensionality with `k`.

Rewrite using `[hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.1 f h) k (by omega), map_add, map_add, hg f k k (by omega), hg h k k (by omega)]`. Establish `gone : g 1 = 1`. Use extensionality with `k`. Rewrite using `[hg _ k k (by omega), hdv _ _ _ (hφ k).1.2.2.1 k (by omega)]`. Establish `gzero : g 0 = 0`.

Use `gadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Take the linear combination `-this`. Set `γ : A →+* PowerSeries R` to `{ toFun := g, map_one' := gone, map_mul' := gmul, map_zero' := gzero, map_add' := gadd }`. Use `⟨γ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `b k show coeff k (g (π b)) = coeff k (C (β b))`. Rewrite using `[hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.2.2 b) k (by omega)]`. Use extensionality with `f show constantCoeff (g f) = β (ε f)`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hg f 0 0 (by omega), coeff_zero_eq_constantCoeff_apply, (hφ 0).2.2.1 f]`. Introduce `f show coeff 1 (g f) = δ f`.

Rewrite using `[hg f 1 0 (by omega), (hφ 0).2.2.2 f]`. Use extensionality with `f k show coeff k (rescale 2 (g f)) = coeff k (g (m f))`. Rewrite using `[coeff_rescale, hg f k k (by omega), hg (m f) k k (by omega), hdv _ _ _ ((hφ k).2.1 f) k (by omega), coeff_rescale]`.
-/
theorem limit_of_jets (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A)
    (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R) (φ : ℕ → A → PowerSeries R)
    (hφ : ∀ n, IsJet π ε m β δ (n + 2) (φ n))
    (hc : ∀ n f, (X : PowerSeries R) ^ (n + 2) ∣ φ (n + 1) f - φ n f) :
    ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧
      PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧
      (PowerSeries.rescale 2).comp γ = γ.comp m := by

  have hdv : ∀ (n : ℕ) (p q : PowerSeries R), (X : PowerSeries R) ^ n ∣ p - q →
      ∀ k, k < n → coeff k p = coeff k q := by
    intro n p q h k hk
    have := (PowerSeries.X_pow_dvd_iff.mp h) k hk
    rwa [map_sub, sub_eq_zero] at this

  have hstab : ∀ f k j, k ≤ j + 1 → coeff k (φ j f) = coeff k (φ k f) := by
    intro f k j hkj
    rcases Nat.lt_or_ge j k with h | h
    · have hk : k = j + 1 := by omega
      subst hk
      exact (hdv _ _ _ (hc j f) (j + 1) (by omega)).symm
    · induction j, h using Nat.le_induction with
      | base => rfl
      | succ j hj ih =>
        rw [hdv _ _ _ (hc j f) k (by omega)]
        exact ih (by omega)
  let g : A → PowerSeries R := fun f => PowerSeries.mk fun k => coeff k (φ k f)
  have hg : ∀ f k j, k ≤ j + 1 → coeff k (g f) = coeff k (φ j f) := by
    intro f k j hkj
    simp only [g, PowerSeries.coeff_mk]
    exact (hstab f k j hkj).symm
  have gmul : ∀ f h, g (f * h) = g f * g h := by
    intro f h; ext k
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.1 f h) k (by omega), coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hg f x.1 k (by omega), hg h x.2 k (by omega)]
  have gadd : ∀ f h, g (f + h) = g f + g h := by
    intro f h; ext k
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.1 f h) k (by omega), map_add, map_add,
      hg f k k (by omega), hg h k k (by omega)]
  have gone : g 1 = 1 := by
    ext k
    rw [hg _ k k (by omega), hdv _ _ _ (hφ k).1.2.2.1 k (by omega)]
  have gzero : g 0 = 0 := by
    have := gadd 0 0
    rw [add_zero] at this
    linear_combination -this
  let γ : A →+* PowerSeries R :=
    { toFun := g, map_one' := gone, map_mul' := gmul, map_zero' := gzero, map_add' := gadd }
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · ext b k
    show coeff k (g (π b)) = coeff k (C (β b))
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.2.2 b) k (by omega)]
  · ext f
    show constantCoeff (g f) = β (ε f)
    rw [← coeff_zero_eq_constantCoeff_apply, hg f 0 0 (by omega), coeff_zero_eq_constantCoeff_apply,
      (hφ 0).2.2.1 f]
  · intro f
    show coeff 1 (g f) = δ f
    rw [hg f 1 0 (by omega), (hφ 0).2.2.2 f]
  · ext f k
    show coeff k (rescale 2 (g f)) = coeff k (g (m f))
    rw [coeff_rescale, hg f k k (by omega), hg (m f) k k (by omega),
      hdv _ _ _ ((hφ k).2.1 f) k (by omega), coeff_rescale]

end GlobalTheory.Nef.PathJet

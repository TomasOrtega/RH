import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `h`. Establish `hall : ∀ x : F, ∑ τ, a τ * τ x = 0`. Introduce `x`. Establish `halg : IsAlgebraic ℤ x` using `by first`. Consider the case `exact Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x`.

Consider the case `(haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)`. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℚ) x).isAlgebraic.restrictScalars ℤ)`. Take `⟨y, hy, hint⟩` from `halg.exists_integral_multiple`. Establish `h1 : ∑ τ : F →+* ℝ, a τ * τ (y • x) = 0` using `h ⟨y • x, hint⟩`. Rewrite `h1` using `[zsmul_eq_mul]`.

Establish `h2 : ∑ τ : F →+* ℝ, a τ * τ ((y : F) * x) = (y : ℝ) * ∑ τ, a τ * τ x`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[h2]`. Break down `mul_eq_zero.mp h1 with h4 | h4` into its components or cases. Conclude with `absurd (by exact_mod_cast h4) hy`. Conclude with `h4`. Establish `hli : LinearIndependent ℝ (fun τ : F →+* ℝ => ((τ : F →* ℝ) : F → ℝ))` using `(linearIndependent_monoidHom F ℝ).comp (fun τ : F →+* ℝ => (τ : F →* ℝ)) (fun τ σ hτσ => RingHom.ext fun x => DFunLike.congr_fun hτσ x)`.

Use function extensionality and compare the values at `τ`. Use `Fintype.linearIndependent_iff.mp hli a ?_ τ` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify `hall x` using `[Finset.sum_apply, smul_eq_mul]`.
-/
theorem realEmb_linearIndependent_on_integers (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ) :
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := by
  intro h
  have hall : ∀ x : F, ∑ τ, a τ * τ x = 0 := by
    intro x
    have halg : IsAlgebraic ℤ x := by
      first
        | exact Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x
        | (haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
           exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).isAlgebraic.restrictScalars ℤ)
    obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
    have h1 : ∑ τ : F →+* ℝ, a τ * τ (y • x) = 0 := h ⟨y • x, hint⟩
    rw [zsmul_eq_mul] at h1
    have h2 : ∑ τ : F →+* ℝ, a τ * τ ((y : F) * x) = (y : ℝ) * ∑ τ, a τ * τ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, map_intCast]; ring
    rw [h2] at h1
    rcases mul_eq_zero.mp h1 with h4 | h4
    · exact absurd (by exact_mod_cast h4) hy
    · exact h4
  have hli : LinearIndependent ℝ (fun τ : F →+* ℝ => ((τ : F →* ℝ) : F → ℝ)) :=
    (linearIndependent_monoidHom F ℝ).comp (fun τ : F →+* ℝ => (τ : F →* ℝ))
      (fun τ σ hτσ => RingHom.ext fun x => DFunLike.congr_fun hτσ x)
  funext τ
  refine Fintype.linearIndependent_iff.mp hli a ?_ τ
  funext x
  simpa [Finset.sum_apply, smul_eq_mul] using hall x

/- English proof (translation)
Introduce `F _ _ a h` and use `GlobalTheory.realEmb_linearIndependent_on_integers F a h`.
-/
example : ∀ (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ),
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := fun F _ _ a h => GlobalTheory.realEmb_linearIndependent_on_integers F a h

end GlobalTheory

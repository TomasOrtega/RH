import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def CanonKeySt : Prop :=
  ∃ κ : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R], KeyIn R → Rˣ,
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R], GlobalTheory.KeyPow.ClauseH R (fun _ => 1) 1 (κ R)) ∧
    (∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R]
      [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsPrincipalIdealRing R'] (f : R →+* R') (x : KeyIn R) (x' : KeyIn R'),
      KeyPB x' x f → (κ R' x' : R') = f (κ R x)) ∧
    ∀ (x : KeyIn ℂ) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.NormalAt x τ 1 0 0 1 → κ ℂ x = 1

namespace CanonKeySt

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, _⟩`. Distinguish the cases in `h : IsField R`. Conclude with `Or.inl h`. Conclude with `Or.inr { not_a_field' := fun e => h (IsLocalRing.isField_iff_maximalIdeal_eq.2 e) }`.

Introduce and unpack `(h | h)`. Use `letI := h.toField`. Conclude with `⟨inferInstance, inferInstance⟩`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem base_iff (R : Type) [CommRing R] [IsDomain R] :
    (IsLocalRing R ∧ IsPrincipalIdealRing R) ↔ IsField R ∨ IsDiscreteValuationRing R := by
  constructor
  · rintro ⟨_, _⟩
    by_cases h : IsField R
    · exact Or.inl h
    · exact Or.inr { not_a_field' := fun e => h (IsLocalRing.isField_iff_maximalIdeal_eq.2 e) }
  · rintro (h | h)
    · letI := h.toField
      exact ⟨inferInstance, inferInstance⟩
    · exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Simplify using `only [thetaChar, add_zero]`.
-/
theorem thetaChar_zero {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    thetaChar τ 0 0 z = ∑' n : Fin g → ℤ,
      Complex.exp (Real.pi * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec fun i => (n i : ℂ)) +
        2 * Real.pi * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ z)) := by
  simp only [thetaChar, add_zero]

/- English proof (translation)
Rewrite using `[← pow_mul, Nat.mul_comm g 4, pow_mul, pow_mul, mul_pow, Complex.I_pow_four, _root_.mul_one]`.
-/
theorem const_pow (g : ℕ) :
    ((2 * Real.pi * Complex.I : ℂ) ^ g) ^ 4 = (2 * Real.pi : ℂ) ^ (4 * g) := by
  rw [← pow_mul, Nat.mul_comm g 4, pow_mul, pow_mul, mul_pow, Complex.I_pow_four, _root_.mul_one]

end CanonKeySt

end GlobalTheory.Published

abbrev GlobalTheory.KeyPow.CanonKey : Prop := GlobalTheory.Published.CanonKeySt

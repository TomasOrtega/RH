import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]`.
-/
theorem norm_prime_padicComplex (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]

/- English proof (translation)
Introduce `p`. Establish `hI : (NormedField.valuation (K` using `ℂ_[p])).Integers (GlobalTheory.CompanionTheory.Ar.Flat.CPoint.OCp p) := Valuation.valuationSubring.integers _`. Use `⟨hI, ⟨((p : ℕ) : ℂ_[p]), ?_, ?_⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_zero, GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]`. Conclude with `inv_pos.2 (by exact_mod_cast p.2.pos)`.

Rewrite using `[NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one, GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)`. Take `⟨y, rfl⟩` from `RingHom.mem_range.1 hx`. Establish `h` using `hI.map_le_one y`. Rewrite `h` using `[NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]`. Then use the resulting hypothesis.

Use `RingHom.mem_range.2 (hI.exists_of_le_one ?_)` and prove the remaining obligations. Rewrite using `[NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]` and apply the resulting hypothesis.
-/
theorem ocp_integers : ∀ p : Nat.Primes, (NormedField.valuation (K := ℂ_[p])).Integers (OCp p) ∧
    (∃ x : ℂ_[p], 0 < NormedField.valuation (K := ℂ_[p]) x ∧ NormedField.valuation (K := ℂ_[p]) x < 1) ∧
    ∀ x : ℂ_[p], x ∈ (algebraMap (OCp p) ℂ_[p]).range ↔ ‖x‖ ≤ 1 := by
  intro p
  have hI : (NormedField.valuation (K := ℂ_[p])).Integers (GlobalTheory.CompanionTheory.Ar.Flat.CPoint.OCp p) :=
    Valuation.valuationSubring.integers _
  refine ⟨hI, ⟨((p : ℕ) : ℂ_[p]), ?_, ?_⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_zero,
      GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]
    exact inv_pos.2 (by exact_mod_cast p.2.pos)
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one,
      GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
  · obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx
    have h := hI.map_le_one y
    rwa [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one] at h
  · refine RingHom.mem_range.2 (hI.exists_of_le_one ?_)
    rwa [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint

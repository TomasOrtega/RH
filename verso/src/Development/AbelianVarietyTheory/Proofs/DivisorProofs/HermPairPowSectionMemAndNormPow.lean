import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.NuPow

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem pow_mem_H_and_nu_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ n : ℕ, f ^ n ∈ P.H (n * a) (n * b) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (n * a) (n * b) σ y (f ^ n) = P.nu a b σ y f ^ n := by
  intro k _ X _ p P a b f hf n
  induction n with
  | zero =>
    refine ⟨fun x i j _ _ => ⟨1, by simp [Pair.loc]⟩, fun σ y => ?_⟩
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    simp [Pair.nu, Pair.loc, e]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P _ _ a b _ f ih.1 hf
    have ea : ((n + 1 : ℕ) : ℤ) * a = n * a + a := by push_cast; ring
    have eb : ((n + 1 : ℕ) : ℤ) * b = n * b + b := by push_cast; ring
    rw [ea, eb, pow_succ]
    exact ⟨h1, fun σ y => by rw [h2 σ y, ih.2 σ y, pow_succ]⟩

end GlobalTheory.VolBr.NuPow

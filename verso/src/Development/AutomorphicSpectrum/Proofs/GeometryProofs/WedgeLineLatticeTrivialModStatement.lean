import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeTrivialMod
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.DddTriv.trivMod_lineLat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FWedgeLineLatticeTrivialMod.lean&line=443#L443)
-/
theorem _root_.GlobalTheory.T.wedge_line_lattice_trivial_mod : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (ϖ : Ω), IsCptGen ξ → ϖ ≠ 0 → (∀ x, ϖ ∈ regAt ξ x) → A.IsVB p V → B.IsVB q V' → a ≠ 0 → b ≠ 0 → (∃ x f, IsCoeffAt A B p q a b x f) → ExactModLat A B ϖ (p + q) → TrivMod (lineLat A B p q a b) ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DddTriv.trivMod_lineLat | exact GlobalTheory.CompanionTheory.Ar.Flat.DddTriv.trivMod_lineLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DddTriv.trivMod_lineLat <;> assumption)

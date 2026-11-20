import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPairingTorsionFree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.FamEx.gram_invertible_of_unramified` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FHermitianPairingTorsionFree.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.hermitian_pairing_torsion_free : ∀ (E : Type) [Field E] [NumberField E] (cc : E ≃+* E) (p R N : ℕ) [Fact p.Prime], 1 ≤ R → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)), (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv cc a • y)) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ¬ IsUnit (p : O) → ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) → ∃ C : Matrix (Fin N) (Fin N) Ω, (∀ i j, C i j ∈ (algebraMap O Ω).range) ∧ (Matrix.of fun i j => ∑ k, σ (HT.dualInt E k) * ((e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : Ω)) * C = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.gram_invertible_of_unramified | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.gram_invertible_of_unramified | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.gram_invertible_of_unramified <;> assumption)

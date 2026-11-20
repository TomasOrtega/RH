import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationExtensionClosed
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrobFilt.ExtPres.exists_pres_of_shortExact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPresentationExtensionClosed.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.presentation_extension_closed : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), ∀ S : ShortComplex B.X.Modules, S.ShortExact → (∃ P : Pres B, Nonempty (S.X₁ ≅ P.mod)) → (∃ P : Pres B, Nonempty (S.X₃ ≅ P.mod)) → ∃ P : Pres B, Nonempty (S.X₂ ≅ P.mod) := by
  first | exact @GlobalTheory.FrobFilt.ExtPres.exists_pres_of_shortExact | exact GlobalTheory.FrobFilt.ExtPres.exists_pres_of_shortExact | (intros; apply GlobalTheory.FrobFilt.ExtPres.exists_pres_of_shortExact <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomain
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAmpleTwistNormalisedBlowupNoetherianDomain.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.ample_twist_normalisedBlowup_noetherian_domain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X X' N : Scheme.{0}) (s : X ⟶ Sp R) (J : X.IdealSheafData) (b : X' ⟶ X) (ν : N ⟶ X') (EX : EffCartierData N), IsProjOver s → FinalTheorems.Blowup b J → IsFinite ν → EX.idealSheaf = J.comap (ν ≫ b) → ∀ L : LB X, IsAmpleLB L → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → IsAmpleLB (CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (CechPic.dual EX.lb)) := by
  first | exact @GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup | exact GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup | (intros; apply GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup <;> assumption)

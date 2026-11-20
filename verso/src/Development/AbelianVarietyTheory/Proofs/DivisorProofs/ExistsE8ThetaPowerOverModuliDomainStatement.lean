import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8ThetaPowerOverModuliDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsE8ThetaPowerOverModuliDomain.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.exists_e8ThetaPower_over_moduli_domain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (R : Type) [CommRing R] [IsDomain R] (u : Sp R ⟶ F.X), ∃ P : PolAV (Sp R), SharpOver F W P u := by
  first | exact @GlobalTheory.Poinc.exists_sharpOver_domain | exact GlobalTheory.Poinc.exists_sharpOver_domain | (intros; apply GlobalTheory.Poinc.exists_sharpOver_domain <;> assumption)

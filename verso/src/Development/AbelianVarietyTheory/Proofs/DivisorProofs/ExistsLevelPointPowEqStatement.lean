import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPowEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_levelPoint_pow_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLevelPointPowEq.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.exists_levelPoint_pow_eq' : ∀ (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)) (m g : ℕ) (hg : Q.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev : Level Q (m ^ 2) ze) (z : baseOver (Sp K) ⟶ Q.A), 0 < m → z ^ m = 1 → ∃ a : Fin (2 * g) → ZMod (m ^ 2), GlobalTheory.levelPoint lev hg a ^ m = z := by
  first | exact @GlobalTheory.exists_levelPoint_pow_eq | exact GlobalTheory.exists_levelPoint_pow_eq | (intros; apply GlobalTheory.exists_levelPoint_pow_eq <;> assumption)

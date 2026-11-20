import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianFibreDescendsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianFibreDescendsAlgClosed.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.abelian_fibre_descends_alg_closed : ∀ (k₀ k : Type) [Field k₀] [IsAlgClosed k₀] [Field k] [IsAlgClosed k] (ι : k₀ →+* k) (B : Over (Sp k₀)) [GrpObj B] (S : Scheme.{0}) (P : Out.PolAV S) (x : Sp k ⟶ S), IsAbelianScheme B → SameFibre P.A x B (spMap ι) → ∃ P₀ : Out.PolAV (Sp k₀), SameFibre P.A x P₀.A (spMap ι) := by
  first | exact @GlobalTheory.BdDim.PolDescent.exists_polAV_sameFibre | exact GlobalTheory.BdDim.PolDescent.exists_polAV_sameFibre | (intros; apply GlobalTheory.BdDim.PolDescent.exists_polAV_sameFibre <;> assumption)

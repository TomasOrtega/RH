import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagEmb.Stab.exists_stabBasis` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsAffineStableTangentBasis.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.exists_affine_stable_tangent_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (x : X), ∃ (U : X.affineOpens) (n : ℕ) (v : Fin n → Tn t Γ(X, U.1)), x ∈ U.1 ∧ StabBasis t U.2.fromSpec v := by
  first | exact @GlobalTheory.FlagEmb.Stab.exists_stabBasis | exact GlobalTheory.FlagEmb.Stab.exists_stabBasis | (intros; apply GlobalTheory.FlagEmb.Stab.exists_stabBasis <;> assumption)

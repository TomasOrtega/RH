import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ

set_option autoImplicit false

noncomputable section

open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM resM_resM resM_smul)
open GlobalTheory.LB (resG_resG)

namespace GlobalTheory.FlagZ.TautCell

/- English proof (translation)
Establish `hF` using `VB.isFrame_freeFrame X (Fin N)`. Use `VB.isFrame_of_basis (fun V h => (hF.basis (le_top : V ≤ ⊤)).map (Matrix.toLinearEquiv (hF.basis (le_top : V ≤ ⊤)) ((resG X h).mapMatrix M.1) ?_)) fun V h j => ?_` and prove the remaining obligations. Rewrite using `[← RingHom.map_det]`. Conclude with `(Matrix.isUnits_det_units M).map _`. Rewrite using `[Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]`.

Simplify using `only [colOn, map_sum, resM_smul, resM_resM, VB.IsFrame.basis_apply]`. Both sides reduce to the same expression.
-/
theorem isFrame_colOn (N : ℕ) (X : Scheme.{0}) (U : X.Opens) (M : GL (Fin N) Γ(X, U)) :
    GlobalTheory.VB.IsFrame (GlobalTheory.FlagZ.TautCell.colOn M.1) := by
  classical
  have hF := VB.isFrame_freeFrame X (Fin N)
  refine VB.isFrame_of_basis (fun V h =>
    (hF.basis (le_top : V ≤ ⊤)).map
      (Matrix.toLinearEquiv (hF.basis (le_top : V ≤ ⊤)) ((resG X h).mapMatrix M.1) ?_)) fun V h j => ?_
  · rw [← RingHom.map_det]
    exact (Matrix.isUnits_det_units M).map _
  · rw [Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
    simp only [colOn, map_sum, resM_smul, resM_resM, VB.IsFrame.basis_apply]
    rfl

end GlobalTheory.FlagZ.TautCell

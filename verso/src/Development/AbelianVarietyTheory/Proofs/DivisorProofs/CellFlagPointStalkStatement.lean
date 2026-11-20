import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFlagPointStalk
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagZ.Univ.flagPt_germ_cellGL_eq_fromSpecStalk` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCellFlagPointStalk.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.cell_flag_point_stalk : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (y : Fl ι N) (hy : y ∈ cellOpen ι N w), flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (fun τ => Matrix.GeneralLinearGroup.map (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)) = (Fl ι N).fromSpecStalk y := by
  first | exact @GlobalTheory.FlagZ.Univ.flagPt_germ_cellGL_eq_fromSpecStalk | exact GlobalTheory.FlagZ.Univ.flagPt_germ_cellGL_eq_fromSpecStalk | (intros; apply GlobalTheory.FlagZ.Univ.flagPt_germ_cellGL_eq_fromSpecStalk <;> assumption)

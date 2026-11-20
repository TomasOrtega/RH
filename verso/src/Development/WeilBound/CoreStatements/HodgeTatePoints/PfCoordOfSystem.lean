import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PositivityTheory.HtPt.Aig

open ReciprocityTheory.ChartRestriction.G.AI.I2 in

/- English proof (translation)
Introduce and unpack `⟨II, hSys, -, hPF, -⟩`. Introduce `I hI K _ ι _ K' _ ι' _ κ v Ω _ _ y d L L' hv hP' hP hL hL'`. Establish `hU : UniqueStatement` using `GroundTheory.Heights₂.Heights.Inter.ThmIUnique.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero`. Establish `hd : 1 ≤ d`. Break down `Nat.eq_zero_or_pos d with rfl | h` into its components or cases.

Conclude with `absurd hP (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι _)`. Conclude with `h`. Establish `hL's : ∀ j, IsSmoothHerm (L' j)` using `fun j => GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection.isSmoothHerm_pull hv (hL j) (hL' j)`. Establish `e1 : I K' ι' (mCoordIdeal y) d L' = II K' ι' (mCoordIdeal y) d L'` using `hU K' ι' (I K' ι') (II K' ι') (IsIntersectionFamily.isRFamily (hI K' ι')) (IsIntersectionFamily.isRFamily (hSys K' ι')) _ d L' hd hP' hL's`. Establish `e2 : I K ι (imageZ v (mCoordIdeal y)) d L = II K ι (imageZ v (mCoordIdeal y)) d L` using `hU K ι (I K ι) (II K ι) (IsIntersectionFamily.isRFamily (hI K ι)) (IsIntersectionFamily.isRFamily (hSys K ι)) _ d L hd hP hL`.

Rewrite using `[e1, e2]`. Conclude with `hPF K ι K' ι' κ v Ω y d L L' hv hP' hP hL hL'`.
-/
theorem pfCoord_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement := by
  rintro ⟨II, hSys, -, hPF, -⟩
  intro I hI K _ ι _ K' _ ι' _ κ v Ω _ _ y d L L' hv hP' hP hL hL'
  have hU : UniqueStatement :=
    GroundTheory.Heights₂.Heights.Inter.ThmIUnique.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exact absurd hP (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι _)
    · exact h
  have hL's : ∀ j, IsSmoothHerm (L' j) := fun j =>
    GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection.isSmoothHerm_pull hv (hL j) (hL' j)
  have e1 : I K' ι' (mCoordIdeal y) d L' = II K' ι' (mCoordIdeal y) d L' :=
    hU K' ι' (I K' ι') (II K' ι') (IsIntersectionFamily.isRFamily (hI K' ι'))
      (IsIntersectionFamily.isRFamily (hSys K' ι')) _ d L' hd hP' hL's
  have e2 : I K ι (imageZ v (mCoordIdeal y)) d L = II K ι (imageZ v (mCoordIdeal y)) d L :=
    hU K ι (I K ι) (II K ι) (IsIntersectionFamily.isRFamily (hI K ι))
      (IsIntersectionFamily.isRFamily (hSys K ι)) _ d L hd hP hL
  rw [e1, e2]
  exact hPF K ι K' ι' κ v Ω y d L L' hv hP' hP hL hL'

/- English proof (translation)
The claim follows from `pfCoord_of_system`.
-/
theorem pfCoord : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement :=
  pfCoord_of_system

end PositivityTheory.HtPt.Aig

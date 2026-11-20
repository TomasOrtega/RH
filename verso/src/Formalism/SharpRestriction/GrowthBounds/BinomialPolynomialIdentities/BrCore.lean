import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.FinalA
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.RationalBitableauLatticeStatement

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

section B1
/- English proof (translation)
The claim follows from `Formalism.InvariantFactorPaths.ColumnFamilies.Top.lemmaA`.
-/
theorem path_pair_correspondence (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.PathPairCorrespondence D := Formalism.InvariantFactorPaths.ColumnFamilies.Top.lemmaA
end B1

section B2
/- English proof (translation)
The claim follows from `Formalism.InvariantFactorPaths.ColumnFamilies.Top.sBasis`.
-/
theorem admissible_standard_basis (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.admB2 D := Formalism.InvariantFactorPaths.ColumnFamilies.Top.sBasis
end B2

section B9
/- English proof (translation)
Introduce `n _ mu R _ _ hR` and use `Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_one n mu R hR`.
-/
theorem global_sections_schur (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.GlobalSectionsSchur D := fun n _ mu R _ _ hR =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_one n mu R hR
end B9

section lowerOffDiagonalCoeff
/- English proof (translation)
Introduce `n _ mu hmu` and use `Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_two n mu hmu`.
-/
theorem bracket_polynomial_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.BracketPolynomialSpan D := fun n _ mu hmu =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_two n mu hmu
end lowerOffDiagonalCoeff

section Mod

def br_toC {n : ℕ} (M : Formalism.MainNotions.CovariantDegrees.GLMod n) : Formalism.InvariantFactorPaths.ColumnFamilies.GLMod n :=
  { ι := M.ι, fi := M.fi, de := M.de, A := M.A, mul := M.mul, one := M.one }

def br_cfToC {n : ℕ} [NeZero n] {M : Formalism.MainNotions.CovariantDegrees.GLMod n} (CF : Formalism.MainNotions.CovariantDegrees.ColFam M) :
    Formalism.InvariantFactorPaths.ColumnFamilies.ColFam (br_toC M) :=
  { J := CF.J, fJ := CF.fJ, dJ := CF.dJ, mu := CF.mu, dom := CF.dom, ph := CF.ph, equiv := CF.equiv,
    indepP := CF.indepP, indepQ := CF.indepQ, rank := CF.rank }

def br_cfOfC {n : ℕ} [NeZero n] {M : Formalism.MainNotions.CovariantDegrees.GLMod n} (CF : Formalism.InvariantFactorPaths.ColumnFamilies.ColFam (br_toC M)) :
    Formalism.MainNotions.CovariantDegrees.ColFam M :=
  { J := CF.J, fJ := CF.fJ, dJ := CF.dJ, mu := CF.mu, dom := CF.dom, ph := CF.ph, equiv := CF.equiv,
    indepP := CF.indepP, indepQ := CF.indepQ, rank := CF.rank }

end Mod

section B6
/- English proof (translation)
Introduce `n _`. Take `⟨h1, h2, h3⟩` from `Formalism.InvariantFactorPaths.ColumnFamilies.Top.closure_first_part n`. Use `⟨fun M hc hA => ?_, fun M mu β hmu hS => ?_, fun M M' ε hε e he hM => ?_⟩` and prove the remaining obligations. Conclude with `(h1 (br_toC M) hc hA).map br_cfOfC`. Conclude with `(h2 (br_toC M) mu β hmu hS).map br_cfOfC`.

Conclude with `(h3 (br_toC M) (br_toC M') ε hε e he (hM.map br_cfToC)).map br_cfOfC`.
-/
theorem column_family_closure (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.ColumnFamilyClosure D := by
  intro n _
  obtain ⟨h1, h2, h3⟩ := Formalism.InvariantFactorPaths.ColumnFamilies.Top.closure_first_part n
  refine ⟨fun M hc hA => ?_, fun M mu β hmu hS => ?_, fun M M' ε hε e he hM => ?_⟩
  · exact (h1 (br_toC M) hc hA).map br_cfOfC
  · exact (h2 (br_toC M) mu β hmu hS).map br_cfOfC
  · exact (h3 (br_toC M) (br_toC M') ε hε e he (hM.map br_cfToC)).map br_cfOfC
end B6

end Formalism.MainNotions.G.ColumnFamilies

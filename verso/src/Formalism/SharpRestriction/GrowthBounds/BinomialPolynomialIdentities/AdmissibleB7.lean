import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.BrCore
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.ClosureSecondPart

noncomputable section

namespace Formalism.MainNotions.G.ColumnFamilies

/- English proof (translation)
Introduce `n _ M M' b hM`. Take `⟨h1, h2, h3⟩` from `Formalism.InvariantFactorPaths.ColumnFamilies.Top.closure_second_part n (br_toC M) (br_toC M') b (hM.map br_cfToC)`. Conclude with `⟨fun e he => (h1 e he).map br_cfOfC, fun e he => (h2 e he).map br_cfOfC, fun e he => (h3 e he).map br_cfOfC⟩`.
-/
theorem admissible_B7 (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.TensorColumnFamily D := by
  intro n _ M M' b hM
  obtain ⟨h1, h2, h3⟩ := Formalism.InvariantFactorPaths.ColumnFamilies.Top.closure_second_part n (br_toC M) (br_toC M') b (hM.map br_cfToC)
  exact ⟨fun e he => (h1 e he).map br_cfOfC, fun e he => (h2 e he).map br_cfOfC, fun e he => (h3 e he).map br_cfOfC⟩

end Formalism.MainNotions.G.ColumnFamilies

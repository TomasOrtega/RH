import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.NotRealComplex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ComplexBaseChangeOfLiterature
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC

open NumberField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately.
-/
theorem UpperTheory.V.Z.Bc.wbc_of_cbcc (h : UpperTheory.V.Z.Bc.CBCc) : PositivityTheory.Pf1.CLGD.K.WBC := by
  intro F M _ _ _ _ _ _ hF hM hp n hn π
  rcases (h F M hp hF n hn).1 (.cx π) with ⟨η, hη, hi⟩ | ⟨P, hw, hinf, -⟩
  · exact Or.inl ⟨η, hη.1, hη.2.1, hη.2.2, hi⟩
  · cases P with
    | cx P => exact Or.inr ⟨P, hw, fun τ m hm => hinf τ m hm⟩
    | re P => exact (PositivityTheory.Pf1.CLGD.K.LKW.not_real_complex M inferInstance hM).elim

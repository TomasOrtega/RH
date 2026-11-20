import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.G1
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CuspRapid
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.LevSub
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Cj.harmInj :
    UpperTheory.V.Cj.HarmInj := by
  intro E _ _ _ a ha π Ξ r n e he hr q ω ⟨⟨U, u1, u2, u3⟩, _, hco, hV⟩ ⟨U', v1, v2, v3⟩
  cases q with
  | zero => exact v3
  | succ q =>
    have ho : IsOpen ((U ⊓ U' : Subgroup _) : Set (GL (Fin a) (Af E))) := u1.inter v1
    have hc : IsCompact ((U ⊓ U' : Subgroup _) : Set (GL (Fin a) (Af E))) :=
      u2.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1
    have hm := (levSub E a Ξ (q + 1)).2.1
    have hL := (hm U (U ⊓ U') inf_le_left ω).1 u3
    obtain ⟨η, hη, rfl⟩ := (hm U' (U ⊓ U') inf_le_right ω).2 v3
    have hR : Rapid (dCo (smLie Ξ) η) := fun X N => cuspRapid E a π Ξ (q + 1) _ hV [] X N
    obtain ⟨χ, hχ⟩ := twEx E a ha r
    obtain ⟨G, hG⟩ := admEx E a Ξ
    have hd : IsData Ξ r χ G e := ⟨hr, hχ, hG, he⟩
    have hM : Moderate (dCo (smLie Ξ) η) := ⟨0, fun X => by
      obtain ⟨C, hC⟩ := hR X 0
      exact ⟨C, fun g => by simpa using hC g⟩⟩
    have hP := pairFacts E a ha MeasureTheory.Measure.haar _ ho Ξ r χ G n e hd (q + 1)
    exact hP.2.2.1 _ hL (hP.1 _ _ hL hL hR hM)
      (g1 E a ha MeasureTheory.Measure.haar _ ho hc Ξ r χ G n e hd q _ η hL hη hR hco hM)

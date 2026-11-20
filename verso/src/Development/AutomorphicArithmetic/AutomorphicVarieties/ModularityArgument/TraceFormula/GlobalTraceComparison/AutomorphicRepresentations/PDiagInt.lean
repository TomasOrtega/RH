import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.diagInt_pf :
    GFac → HalfTerm → DiagInt := by
  intro hF hH
  unfold DiagInt ForSu
  intro E _ _ _ n ι _ s m
  obtain ⟨p, hp⟩ := hF E n ι s
  have hb := fun b => (hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)).1
  have hsum := MeasureTheory.integrable_finset_sum (Finset.univ : Finset p.B) fun b _ => hb b
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.sum_apply]
  exact (hp m x x).symm

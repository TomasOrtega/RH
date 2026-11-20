import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

/- English proof (translation)
Introduce `hF hH`. Unfold `DiagInt ForSu`. Introduce `E _ _ _ n ι _ s m`. Take `⟨p, hp⟩` from `hF E n ι s`. Establish `hb` using `fun b => (hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)).1`.

Establish `hsum` using `MeasureTheory.integrable_finset_sum (Finset.univ : Finset p.B) fun b _ => hb b`. Use `hsum.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Finset.sum_apply]`. Conclude with `(hp m x x).symm`.
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

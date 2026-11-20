import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

/- English proof (translation)
Introduce `hA hT hC hI hY E _ _ _ n hn D π hπ μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j`. Take `⟨ht, K, W, k1, k2, w1, w2, hl⟩` from `hT E n μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j`. Take `⟨Y, y1, y2, y3⟩` from `hA E n hn π hπ K W k1 w1`. Use `⟨Y, y1, y2, fun u hu φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨s0, s1⟩` from `hI E n hn D π hπ φ hφ`.

Take `⟨s2, s3, -⟩` from `s1 _ u ht hu`. Establish `ty` using `hC E n D K W _ u φ.1 k2 w1 ht hl hu s0.1`. Take `⟨φ', m, e⟩` from `hY E n hn D π hπ K W k1 k2 w1 w2 _ s2 s3 ty`. Use `⟨φ', y3 φ' m ?_, fun x => congrFun e x⟩` and prove the remaining obligations. Rewrite `ty` using `[← e]`.

Conclude with `ty`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.piFinOf_pf :
    PiAdm → TensType → CvType → CvIn → TypeIn → PiFin := by
  intro hA hT hC hI hY E _ _ _ n hn D π hπ μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨ht, K, W, k1, k2, w1, w2, hl⟩ := hT E n μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨Y, y1, y2, y3⟩ := hA E n hn π hπ K W k1 w1
  refine ⟨Y, y1, y2, fun u hu φ hφ => ?_⟩
  obtain ⟨s0, s1⟩ := hI E n hn D π hπ φ hφ
  obtain ⟨s2, s3, -⟩ := s1 _ u ht hu
  have ty := hC E n D K W _ u φ.1 k2 w1 ht hl hu s0.1
  obtain ⟨φ', m, e⟩ := hY E n hn D π hπ K W k1 k2 w1 w2 _ s2 s3 ty
  refine ⟨φ', y3 φ' m ?_, fun x => congrFun e x⟩
  rw [← e] at ty
  exact ty

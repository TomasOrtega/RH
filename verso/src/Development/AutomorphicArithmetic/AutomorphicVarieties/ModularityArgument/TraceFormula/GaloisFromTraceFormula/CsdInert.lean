import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

/- English proof (translation)
Introduce `h E _ _ _ n hn π hd`. Use `filter_upwards [h E n hn π hd] with w hw hns B hB`. Take `⟨B₀, hB₀, hc⟩` from `hw`. Take `rfl` from `CG.HasSat.unique hB hB₀`. Conclude with `CG.HasSat.unique (hc w ⟨rfl, Or.inr hns⟩) hB`.
-/
theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.csdInert :
    GOne.CsdSat → CsdInert := by
  intro h E _ _ _ n hn π hd
  filter_upwards [h E n hn π hd] with w hw hns B hB
  obtain ⟨B₀, hB₀, hc⟩ := hw
  obtain rfl := CG.HasSat.unique hB hB₀
  exact CG.HasSat.unique (hc w ⟨rfl, Or.inr hns⟩) hB

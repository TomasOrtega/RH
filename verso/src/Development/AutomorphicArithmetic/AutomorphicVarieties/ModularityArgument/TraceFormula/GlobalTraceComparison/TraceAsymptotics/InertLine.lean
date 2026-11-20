import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.inertLine :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.InertLine := by
  intro E _ _ _ hU n w _ σ hne hfd
  exact GlobalTheory.CompanionTheory.SphLine.sphOne E hU n w σ hne hfd

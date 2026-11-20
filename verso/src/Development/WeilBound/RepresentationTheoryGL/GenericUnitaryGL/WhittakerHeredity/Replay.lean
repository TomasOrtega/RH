import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
open GlobalTheory.BZMir.Leib

namespace PositivityTheory.rg.gu.hered2

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem whitHeredity_all :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      WhitHeredity k :=
  fun k _ _ _ _ => GlobalTheory.CompanionTheory.Rodier.whitHeredity k

end PositivityTheory.rg.gu.hered2

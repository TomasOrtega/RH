import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialEqZeroOfEventually

namespace RootFieldNumerics

/- English proof (translation)
Introduce `_ _ _ _ hV hne hΦ hc` and use `GlobalTheory.CountableFibres.exists_injective_fderiv hV hne (fun z hz => (hΦ z hz).contDiffAt) hc`.
-/
theorem rankLem : RankLem := fun _ _ _ _ hV hne hΦ hc =>
  GlobalTheory.CountableFibres.exists_injective_fderiv hV hne (fun z hz => (hΦ z hz).contDiffAt) hc

end RootFieldNumerics

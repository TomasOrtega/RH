import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.CoefEig
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa

namespace CompanionTheory.CapEig

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coefEig_of_infChar (hI : PI.DSInfCharCap.DSInfCharCap) : CompanionTheory.LimBd.Main.CoefEig :=
  coefEig_of hI CompanionTheory.D.gk.admitted.k_finite_smooth

end CompanionTheory.CapEig

import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc

namespace CompanionTheory.D.Upq.Sm

/- English proof (translation)
The claim follows from `smoothCyc_of_kFinSmooth CompanionTheory.D.gk.admitted.k_finite_smooth`.
-/
theorem smooth_cyclic_vectors : PI.SmoothCyc := smoothCyc_of_kFinSmooth CompanionTheory.D.gk.admitted.k_finite_smooth

end CompanionTheory.D.Upq.Sm

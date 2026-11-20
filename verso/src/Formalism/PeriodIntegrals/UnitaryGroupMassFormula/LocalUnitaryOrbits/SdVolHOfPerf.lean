import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolWOfCond

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.conductor_inverse_different`.
-/
theorem condAllF_holds : CondAllF := Formalism.L2.SG.Pf.conductor_inverse_different

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
The claim follows from `condV_of_all σ J ψ v condAllF_holds`.
-/
theorem condV_holds : CondV σ J ψ v := condV_of_all σ J ψ v condAllF_holds

/- English proof (translation)
The claim follows from `sdVolW_of_cond σ J ψ v Λ a condAllF_holds hP`.
-/
theorem sdVolW_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : SdVolW σ J ψ v Λ a :=
  sdVolW_of_cond σ J ψ v Λ a condAllF_holds hP

/- English proof (translation)
The claim follows from `sdVolH_of_cond σ J ψ v a condAllF_holds hP`.
-/
theorem sdVolH_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : SdVolH σ J ψ v a :=
  sdVolH_of_cond σ J ψ v a condAllF_holds hP

end PI.OmLocU.SdB

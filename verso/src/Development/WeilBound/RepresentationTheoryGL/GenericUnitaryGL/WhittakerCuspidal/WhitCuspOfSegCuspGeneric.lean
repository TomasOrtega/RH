import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitLeOneOfDict
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.UnipBEqUnipotent
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.RankDual

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.rg.gu.whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `whitLeOne_of_dict k (unipB_eq_unipotent k) (whitChar_eq_psiN k) (fun ρ N θ => rank_twJacquet_le_one_iff ρ N θ) (fun ρ => isAdmissible_iff ρ)`.
-/
theorem whitLeOne : GlobalTheory.BZMir.Whit.WhitLeOne k :=
  whitLeOne_of_dict k (unipB_eq_unipotent k) (whitChar_eq_psiN k)
    (fun ρ N θ => rank_twJacquet_le_one_iff ρ N θ) (fun ρ => isAdmissible_iff ρ)

/- English proof (translation)
Introduce `ψ hψc hψ1 N V _ _ π hs hirr` and use `whitLeOne k N ψ V π hs hirr hψc hψ1`.
-/
theorem whitRankIrr : GlobalTheory.BZSeg.WhitRankIrr k :=
  fun ψ hψc hψ1 N V _ _ π hs hirr => whitLeOne k N ψ V π hs hirr hψc hψ1

end PositivityTheory.rg.gu.whit

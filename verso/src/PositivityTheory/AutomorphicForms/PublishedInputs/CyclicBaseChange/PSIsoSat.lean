import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist

noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.CBC

/- English proof (translation)
Introduce `F _ _ n π π' h w B hB`. Consider the cases of `π with`. Consider the case `cx p`. Consider the cases of `π' with`. Consider the case `cx p'`.

Conclude with `(GlobalTheory.CuspRep.CG.hasSat_mk p' w B).2 (GlobalTheory.CuspRep.CuspSub.Iso.hasSatGL (π := p) (π' := p') h ((GlobalTheory.CuspRep.CG.hasSat_mk p w B).1 hB))`. Consider the case `re p' => exact h.elim`. Consider the case `re p`. Consider the cases of `π' with`. Consider the case `cx p' => exact h.elim`.

Consider the case `re p' => exact UpperTheory.V.TR.CuspSub.Iso.hasSat (π := p) (π' := p') h hB`.
-/
theorem SIsoSat_holds : SIsoSat := by
  intro F _ _ n π π' h w B hB
  cases π with
  | cx p =>
    cases π' with
    | cx p' =>
      exact (GlobalTheory.CuspRep.CG.hasSat_mk p' w B).2
        (GlobalTheory.CuspRep.CuspSub.Iso.hasSatGL (π := p) (π' := p') h ((GlobalTheory.CuspRep.CG.hasSat_mk p w B).1 hB))
    | re p' => exact h.elim
  | re p =>
    cases π' with
    | cx p' => exact h.elim
    | re p' => exact UpperTheory.V.TR.CuspSub.Iso.hasSat (π := p) (π' := p') h hB

end UpperTheory.CBC

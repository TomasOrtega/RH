import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

/- English proof (translation)
Introduce `D hA i r hr w hw x`. Take `⟨ht, _, h1, h2, _, _, h5⟩` from `hA`. Take `⟨P, hP⟩` from `D.naut.pt_surj i x`. Take `⟨Pa, hPa⟩` from `h1 i P`. Take `⟨ρ, hc, hss, hwd, hl⟩` from `GlobalTheory.GalIsoBC.galRep_isobaric D ht h2 i P Pa hPa`.

Take `⟨Pm, hPm⟩` from `GlobalTheory.BaseChangeConj.rep_conj_of_baseChange D h5 i r hr x P Pa hP hPa ρ hc hss (fun w _ => hwd w)`. Use `⟨P, hP, ?_⟩` and prove the remaining obligations. Establish `hsp` using `D.nd.SQ_split i w hw`. Rewrite using `[← hPa.2.2.2.1 w hsp, ← hwd w]`. Establish `hok : SumRepresentations.At.WDok D.nd D.naut i ρ w`.

Distinguish the cases in `hwl : w ∈ placesOver D.host.E (D.nd.l i)`. Conclude with `Or.inr (hl w hwl).1`. Conclude with `Or.inl hwl`. Conclude with `((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w hok`.
-/
theorem GlobalTheory.StringRepresentationDecomposition.local_global_compat_of_adm : ∀ D : D7, SumRepresentations.AdmA D → LGC D := by
  intro D hA i r hr w hw x
  obtain ⟨ht, _, h1, h2, _, _, h5⟩ := hA
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hPa⟩ := h1 i P
  obtain ⟨ρ, hc, hss, hwd, hl⟩ := GlobalTheory.GalIsoBC.galRep_isobaric D ht h2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := GlobalTheory.BaseChangeConj.rep_conj_of_baseChange D h5 i r hr x P Pa hP hPa ρ hc hss
    (fun w _ => hwd w)
  refine ⟨P, hP, ?_⟩
  have hsp := D.nd.SQ_split i w hw
  rw [← hPa.2.2.2.1 w hsp, ← hwd w]
  have hok : SumRepresentations.At.WDok D.nd D.naut i ρ w := by
    by_cases hwl : w ∈ placesOver D.host.E (D.nd.l i)
    · exact Or.inr (hl w hwl).1
    · exact Or.inl hwl
  exact ((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w hok

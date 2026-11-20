import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChangeStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

/- English proof (translation)
Introduce `D ht h1 h2 h5 i r hr w _hwS hwg x`. Take `⟨P, hP⟩` from `D.naut.pt_surj i x`. Take `⟨Pa, hPa⟩` from `h1 i P`. Take `⟨ρ, hc, hss, hwd, hl⟩` from `GlobalTheory.T.exists_galois_rep_base_change D ht h2 i P Pa hPa`. Take `⟨Pm, hPm⟩` from `GlobalTheory.T.galois_rep_unique_base_change D h5 i r hr x P Pa hP hPa ρ hc hss (fun w _ => hwd w)`.

Use `⟨P, hP, ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hwg`. Establish `hsp : IsSplitPl D.host w` using `(GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1`. Rewrite using `[← hPa.2.2.2.1 w hsp, ← hwd w]`. Establish `hok : SumRepresentations.At.WDok D.nd D.naut i ρ w`.

Distinguish the cases in `hwl : w ∈ placesOver D.host.E (D.nd.l i)`. Conclude with `Or.inr (hl w hwl).1`. Conclude with `Or.inl hwl`. Conclude with `((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w hok`.
-/
theorem GlobalTheory.HubX.lgcG_of_adm : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → GlobalTheory.HubX.LgcG D := by
  intro D ht h1 h2 h5 i r hr w _hwS hwg x
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hPa⟩ := h1 i P
  obtain ⟨ρ, hc, hss, hwd, hl⟩ := GlobalTheory.T.exists_galois_rep_base_change D ht h2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := GlobalTheory.T.galois_rep_unique_base_change D h5 i r hr x P Pa hP hPa ρ hc hss (fun w _ => hwd w)
  refine ⟨P, hP, ?_⟩
  obtain ⟨k, hk⟩ := hwg
  have hsp : IsSplitPl D.host w :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1
  rw [← hPa.2.2.2.1 w hsp, ← hwd w]
  have hok : SumRepresentations.At.WDok D.nd D.naut i ρ w := by
    by_cases hwl : w ∈ placesOver D.host.E (D.nd.l i)
    · exact Or.inr (hl w hwl).1
    · exact Or.inl hwl
  exact ((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w hok

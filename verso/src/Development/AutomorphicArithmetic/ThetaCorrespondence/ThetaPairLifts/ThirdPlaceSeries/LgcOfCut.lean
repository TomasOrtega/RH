import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.NonCriticalLocalParamOfFullDim
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace UpperTheory.GalS
/- English proof (translation)
Introduce `i r hr w hw x`. Establish `ht` using `hA.1`. Establish `h1` using `hA.2.2.1`. Establish `h2` using `_root_.UpperTheory.GalS.weak' hA.2.2.2.1`. Establish `h5` using `hA.2.2.2.2.2.2`.

Take `⟨P, hP⟩` from `D.naut.pt_surj i x`. Take `⟨Pa, hPa⟩` from `h1 i P`. Take `⟨ρ, hc, hss, hwd, -⟩` from `isoRep D ht h2 i P Pa hPa`. Take `⟨Pm, hPm⟩` from `rep_conj D h5 i r hr x P Pa hP hPa ρ hc hss hwd`. Establish `hsp` using `D.nd.SQ_split i w hw`.

Establish `hwl` using `D.nd.SQ_l i w hw`. Establish `rel : RelW D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2))`. Rewrite using `[← hPa.2.2.2.1 w hsp, ((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w (Or.inl hwl)]`. Conclude with `hwd w hwl`. Use `⟨P, hP, rel, (nc_tw _ _).2 ?_⟩` and prove the remaining obligations.

Establish `hd : D.naut.lpDim (D.naut.locV i P w) = D.R.nV`. Rewrite using `[← D.naut.lpDim_tw _ ((1 - (D.R.nV : ℝ)) / 2), ← rel.dim, D.naut.wdOf_dim]`. Establish `hne : D.naut.ptV i P ≠ none` using `by rw [hP]; simp`. Break down `hw with hS | hQ` into its components or cases. Break down `((D.nd.S_def i w).1 hS).1 with h | h | h` into its components or cases.

Conclude with `hC i P hne 0 w h`. Conclude with `hC i P hne 1 w h`. Use `nonCritical_localParam_of_full_dim D hA.2.2.2.2.2.1 i P w (Or.inl hS) (Or.inr ⟨hS, ?_⟩) hd split_ifs at h with he` and prove the remaining obligations. Conclude with `Or.inr ⟨he, h⟩`. Conclude with `Or.inl h`.

Conclude with `nonCritical_localParam_of_full_dim D hA.2.2.2.2.2.1 i P w (Or.inr hQ) (Or.inl hQ) hd`.
-/
theorem lgc_of_cut'_alt (D : D7) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D) (hC : UpperTheory.GalC.CutRec D) : LGCN D := by
  intro i r hr w hw x
  have ht := hA.1
  have h1 := hA.2.2.1
  have h2 := _root_.UpperTheory.GalS.weak' hA.2.2.2.1
  have h5 := hA.2.2.2.2.2.2
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hPa⟩ := h1 i P
  obtain ⟨ρ, hc, hss, hwd, -⟩ := isoRep D ht h2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := rep_conj D h5 i r hr x P Pa hP hPa ρ hc hss hwd
  have hsp := D.nd.SQ_split i w hw
  have hwl := D.nd.SQ_l i w hw
  have rel : RelW D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)
      (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) := by
    rw [← hPa.2.2.2.1 w hsp, ((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w (Or.inl hwl)]
    exact hwd w hwl
  refine ⟨P, hP, rel, (nc_tw _ _).2 ?_⟩
  have hd : D.naut.lpDim (D.naut.locV i P w) = D.R.nV := by
    rw [← D.naut.lpDim_tw _ ((1 - (D.R.nV : ℝ)) / 2), ← rel.dim, D.naut.wdOf_dim]
  have hne : D.naut.ptV i P ≠ none := by rw [hP]; simp
  rcases hw with hS | hQ
  · rcases ((D.nd.S_def i w).1 hS).1 with h | h | h
    · exact hC i P hne 0 w h
    · exact hC i P hne 1 w h
    · refine nonCritical_localParam_of_full_dim D hA.2.2.2.2.2.1 i P w (Or.inl hS) (Or.inr ⟨hS, ?_⟩) hd
      split_ifs at h with he
      · exact Or.inr ⟨he, h⟩
      · exact Or.inl h
  · exact nonCritical_localParam_of_full_dim D hA.2.2.2.2.2.1 i P w (Or.inr hQ) (Or.inl hQ) hd
end UpperTheory.GalS
end
end

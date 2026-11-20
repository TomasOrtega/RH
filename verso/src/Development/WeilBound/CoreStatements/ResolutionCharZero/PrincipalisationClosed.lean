import Mathlib
import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroOfBoundary
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrincipalisationOfCharZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

/- English proof (translation)
Introduce `k _ _ d Y f hY hd hp I hI`. Establish `hsm : Smooth f` using `SmoothOfRelativeDimension.smooth d f`. Establish `hP : IsProper f` using `isProper_of_isProjOver hp`. Take `⟨X', s, E', hseq, hsm', hcart, hsnc, hiso⟩` from `principalisationCharZero_bot_closed k d Y f hd inferInstance inferInstance I (not_subset_of_ne_bot hI)`. Take `⟨y, hy⟩` from `GlobalTheory.Principalise.nonempty_compl_support hI`.

Establish `hne : Nonempty X'`. Take `⟨w, hw⟩` from `(s ∣_ I.support.compl).homeomorph.surjective ⟨y, hy⟩`. Conclude with `⟨(s ⁻¹ᵁ I.support.compl).ι w⟩`. Establish `hint : IsIntegral X'` using `isIntegral_of_seq hseq hY hne hsm'`. Establish `hproj : IsProjOver (s ≫ f)` using `(Resolution.IsBlowupSeq.of_smooth hseq.isSmoothBlowupSeq).isProjOver hp`.

Establish `hdense : Dense ((s ⁻¹ᵁ I.support.compl : X'.Opens) : Set X')`. Use `dense_compl_of_snc _ hsnc` as an intermediate fact. Rewrite `this` using `[Scheme.IdealSheafData.support_comap]`. Conclude with `this.mono fun x hx => hx`. Establish `hrel : SmoothOfRelativeDimension d (s ≫ f)` using `relDim_of_dense _ _ hdense (relDim_preimage s f _ (by`.

Establish `: SmoothOfRelativeDimension (0 + d) (Scheme.Opens.ι I.support.compl ≫ f)` using `inferInstance`. Simplify using `using this))`. Establish `hc` using `seq_of_iso hseq hY hp hne I.support.compl hiso`. Use `⟨X', s, hint, hrel, hproj, hc.mono ?_, hiso, hcart, hsnc⟩` and prove the remaining obligations. Introduce `x hx`.

Simplify using `using hx`.
-/
theorem principalisation_closed : GlobalTheory.Published.Principalisation := by
  intro k _ _ d Y f hY hd hp I hI
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth d f
  have hP : IsProper f := isProper_of_isProjOver hp
  obtain ⟨X', s, E', hseq, hsm', hcart, hsnc, hiso⟩ :=
    principalisationCharZero_bot_closed k d Y f hd inferInstance inferInstance I (not_subset_of_ne_bot hI)
  obtain ⟨y, hy⟩ := GlobalTheory.Principalise.nonempty_compl_support hI
  have hne : Nonempty X' := by
    obtain ⟨w, hw⟩ := (s ∣_ I.support.compl).homeomorph.surjective ⟨y, hy⟩
    exact ⟨(s ⁻¹ᵁ I.support.compl).ι w⟩
  have hint : IsIntegral X' := isIntegral_of_seq hseq hY hne hsm'
  have hproj : IsProjOver (s ≫ f) :=
    (Resolution.IsBlowupSeq.of_smooth hseq.isSmoothBlowupSeq).isProjOver hp
  have hdense : Dense ((s ⁻¹ᵁ I.support.compl : X'.Opens) : Set X') := by
    have := dense_compl_of_snc _ hsnc
    rw [Scheme.IdealSheafData.support_comap] at this
    exact this.mono fun x hx => hx
  have hrel : SmoothOfRelativeDimension d (s ≫ f) :=
    relDim_of_dense _ _ hdense (relDim_preimage s f _ (by
      have : SmoothOfRelativeDimension (0 + d) (Scheme.Opens.ι I.support.compl ≫ f) := inferInstance
      simpa using this))
  have hc := seq_of_iso hseq hY hp hne I.support.compl hiso
  refine ⟨X', s, hint, hrel, hproj, hc.mono ?_, hiso, hcart, hsnc⟩
  intro x hx
  simpa using hx

end PositivityTheory.ResPlug.WeightsCompactStabilizer

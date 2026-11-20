import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hAff hGlue Z S p _ hS`. Establish `h : ∃ w, IsNwt p w`. Use `hGlue p (fun s => ?_)` and prove the remaining obligations. Take `⟨U, hU, hs, hd, hi⟩` from `hS s`. Take `⟨A, w, ho, hr, hw⟩` from `hAff p U hU hd hi`.

Conclude with `⟨A, w, ho, by rw [hr]; exact hs, hw⟩`. Unfold `nwt`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtNormal_of :
    NormAff → NwtGlue → WtNormal := by
  intro hAff hGlue Z S p _ hS
  have h : ∃ w, IsNwt p w := by
    refine hGlue p (fun s => ?_)
    obtain ⟨U, hU, hs, hd, hi⟩ := hS s
    obtain ⟨A, w, ho, hr, hw⟩ := hAff p U hU hd hi
    exact ⟨A, w, ho, by rw [hr]; exact hs, hw⟩
  unfold nwt
  rw [dif_pos h]
  exact h.choose_spec

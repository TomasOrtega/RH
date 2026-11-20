import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hW hU hG Z S p _ _ _`. Establish `hm : IsNwt p (mult p)` using `⟨hW p, fun _ _ _ _ _ => rfl⟩`. Establish `hex : ∃ w, IsNwt p w` using `⟨mult p, hm⟩`. Establish `hspec : IsNwt p hex.choose` using `hex.choose_spec`. Establish `hval : nwt p = hex.choose`.

Unfold `nwt`. Rewrite using `[dif_pos hex]`. Rewrite using `[hval]`. Use `hU p _ _ hspec.1 hm.1 {s | GenPt s} (hG.1 S) ?_` and prove the remaining obligations. Introduce `Ω _ _ z hz`.

Conclude with `hspec.2 Ω z hz`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.nwtOfFlat_of :
    WtFlat → WtUnique → GenBasic → NwtOfFlat := by
  intro hW hU hG Z S p _ _ _
  have hm : IsNwt p (mult p) := ⟨hW p, fun _ _ _ _ _ => rfl⟩
  have hex : ∃ w, IsNwt p w := ⟨mult p, hm⟩
  have hspec : IsNwt p hex.choose := hex.choose_spec
  have hval : nwt p = hex.choose := by
    unfold nwt
    rw [dif_pos hex]
  rw [hval]
  refine hU p _ _ hspec.1 hm.1 {s | GenPt s} (hG.1 S) ?_
  intro Ω _ _ z hz
  exact hspec.2 Ω z hz

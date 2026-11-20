import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hP hL q _ n i Z S p _ w d hw hq hpush x`. Establish `h1` using `hP q n i p (𝟙 S) w (by simpa using hw) hq x`. Simplify using `only [Category.comp_id] at h1`. Rewrite using `[h1, hpush]`. Conclude with `(hL q n i).2.2 S d hq x`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.trDeg_of :
    TrPush → TrLin → TrDeg := by
  intro hP hL q _ n i Z S p _ w d hw hq hpush x
  have h1 := hP q n i p (𝟙 S) w (by simpa using hw) hq x
  simp only [Category.comp_id] at h1
  rw [h1, hpush]
  exact (hL q n i).2.2 S d hq x

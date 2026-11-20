import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

/- English proof (translation)
Introduce `h k _ _ _ _ n V _ _ π hs hi` and use `(h k).1 (Fin n) V π hs hi`.
-/
theorem GlobalTheory.FourClauses.adm : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun h k _ _ _ _ n V _ _ π hs hi => (h k).1 (Fin n) V π hs hi

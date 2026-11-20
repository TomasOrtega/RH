import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hPt Z S p w h A φ hφ`. Use `choose N c hN hu hc using h A φ hφ`. Use `⟨c, ?_, fun Ω _ _ x => (hc (pt x) Ω x (hu (pt x))).symm⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `u`.

Use `⟨N u, hN u, hu u, fun u' hu' => ?_⟩` and prove the remaining obligations. Take `⟨Ω, _, _, x, rfl⟩` from `hPt A.U u'`. Rewrite using `[← hc (pt x) Ω x (hu (pt x)), hc u Ω x hu']`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtCrit_of :
    PtEx → WtCrit := by
  intro hPt Z S p w h A φ hφ
  choose N c hN hu hc using h A φ hφ
  refine ⟨c, ?_, fun Ω _ _ x => (hc (pt x) Ω x (hu (pt x))).symm⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro u
  refine ⟨N u, hN u, hu u, fun u' hu' => ?_⟩
  obtain ⟨Ω, _, _, x, rfl⟩ := hPt A.U u'
  rw [← hc (pt x) Ω x (hu (pt x)), hc u Ω x hu']

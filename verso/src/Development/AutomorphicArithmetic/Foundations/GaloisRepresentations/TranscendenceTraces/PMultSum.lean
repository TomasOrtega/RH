import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hPt hBC Z S p _ _ Ω _ _ x`. Establish `hpb : IsPullback (pullback.fst p x) (pullback.snd p x) p x` using `IsPullback.of_hasPullback p x`. Establish `hfin` using `Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb (IsLocalRing.closedPoint Ω)`. Establish `h1` using `hPt Ω (pullback.snd p x)`. Rewrite `h1` using `[hBC _ _ _ _ hpb]`.

Rewrite using `[show pt x = x (IsLocalRing.closedPoint Ω) from rfl, ← hfin, ← h1]`. Simplify using `only [Wt.push, Wt.comap]`. Establish `hb` using `fib_bijOn hpb (Ω := Ω) (𝟙 _)`. Rewrite `hb` using `[Category.id_comp]`. Conclude with `(finsum_mem_eq_of_bijOn _ hb (fun _ _ => rfl)).symm`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.multSum_of :
    MultSumPt → MultBC → MultSum := by
  intro hPt hBC Z S p _ _ Ω _ _ x
  have hpb : IsPullback (pullback.fst p x) (pullback.snd p x) p x := IsPullback.of_hasPullback p x
  have hfin := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb (IsLocalRing.closedPoint Ω)
  have h1 := hPt Ω (pullback.snd p x)
  rw [hBC _ _ _ _ hpb] at h1
  rw [show pt x = x (IsLocalRing.closedPoint Ω) from rfl, ← hfin, ← h1]
  simp only [Wt.push, Wt.comap]
  have hb := fib_bijOn hpb (Ω := Ω) (𝟙 _)
  rw [Category.id_comp] at hb
  exact (finsum_mem_eq_of_bijOn _ hb (fun _ _ => rfl)).symm

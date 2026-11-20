import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hTr hFam hWt hRp hOp q _ n i Z Z' S h p _ _ w hw hq x`. Take `⟨σ, hσ, hσd⟩` from `hFam q i h p w (trFam (h ≫ p) w q i) (hTr q i (h ≫ p) w hw hq).2.1`. Establish `hw'` using `hWt h p w hw`. Establish `e2 : tr p (Wt.push h w) q n i = σ.op n`. Use extensionality with `y`.

Conclude with `(hTr q i p (Wt.push h w) hw' hq).2.2 σ hσ n ▸ rfl`. Rewrite using `[e2]`. Take `⟨a, ha⟩` from `(hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).1 x`. Establish `h1` using `hOp (ZMod q) (ZMod q) σ n x a ha`. Establish `h2` using `hOp (ZMod q) (ZMod q) (trFam (h ≫ p) w q i) n _ _ ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).2.2.2.1 Z h x a ha)`.

Conclude with `((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1 _ _ _ _ h2 h1).2.1 (hσd n a).symm`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.trPush_of :
    TrChar → FamPush → WtPush → RpBasic → RpOp → TrPush := by
  intro hTr hFam hWt hRp hOp q _ n i Z Z' S h p _ _ w hw hq x
  obtain ⟨σ, hσ, hσd⟩ := hFam q i h p w (trFam (h ≫ p) w q i) (hTr q i (h ≫ p) w hw hq).2.1
  have hw' := hWt h p w hw
  have e2 : tr p (Wt.push h w) q n i = σ.op n := by
    ext y
    exact (hTr q i p (Wt.push h w) hw' hq).2.2 σ hσ n ▸ rfl
  rw [e2]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).1 x
  have h1 := hOp (ZMod q) (ZMod q) σ n x a ha
  have h2 := hOp (ZMod q) (ZMod q) (trFam (h ≫ p) w q i) n _ _
    ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).2.2.2.1 Z h x a ha)
  exact ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1 _ _ _ _ h2 h1).2.1 (hσd n a).symm

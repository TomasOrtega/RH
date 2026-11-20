import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hFL hOp hTS hPI q _ i Z S p _ w hw hq`. Establish `hOver : (trFam p w q i).Over (tr0 p w q i)`. Unfold `trFam`. Conclude with `GlobalTheory.EtC.pick_spec (hFL q p (tw q i) (tw q i) (tr0 p w q i)).1`. Use `⟨hOver, ?_, ?_⟩` and prove the remaining obligations.

Introduce `A a`. Conclude with `⟨(tr0 p w q i).app A a, hOver A a, hTS q i p w hw hq A a⟩`. Introduce `τ hτ n`. Establish `hτo : τ.Over (tr0 p w q i)`. Introduce `A a`.

Take `⟨b, hb, hs⟩` from `hτ A a`. Establish `hbe : b = (tr0 p w q i).app A a`. Apply `hPI q i A.U` to reduce the goal to its premises. Introduce `Ω _ _ x`. Rewrite using `[hs Ω x, hTS q i p w hw hq A a Ω x]`.

Rewrite using `[hb, hbe]`. Conclude with `hOp q p (tw q i) (tw q i) (tr0 p w q i) (trFam p w q i) τ hOver hτo n`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.trChar_of :
    FL → OpEq → TrSum → PtInj → TrChar := by
  intro hFL hOp hTS hPI q _ i Z S p _ w hw hq
  have hOver : (trFam p w q i).Over (tr0 p w q i) := by
    unfold trFam
    exact GlobalTheory.EtC.pick_spec (hFL q p (tw q i) (tw q i) (tr0 p w q i)).1
  refine ⟨hOver, ?_, ?_⟩
  · intro A a
    exact ⟨(tr0 p w q i).app A a, hOver A a, hTS q i p w hw hq A a⟩
  · intro τ hτ n
    have hτo : τ.Over (tr0 p w q i) := by
      intro A a
      obtain ⟨b, hb, hs⟩ := hτ A a
      have hbe : b = (tr0 p w q i).app A a := by
        apply hPI q i A.U
        intro Ω _ _ x
        rw [hs Ω x, hTS q i p w hw hq A a Ω x]
      rw [hb, hbe]
    exact hOp q p (tw q i) (tw q i) (tr0 p w q i) (trFam p w q i) τ hOver hτo n

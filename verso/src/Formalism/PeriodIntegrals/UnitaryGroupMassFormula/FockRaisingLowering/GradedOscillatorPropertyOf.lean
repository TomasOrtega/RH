import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.SameSign

namespace FockRL

/- English proof (translation)
Introduce `p q r s`. Take `⟨e1, e2, k1, k2, o1, o2, c1, c2, a1, a2⟩` from `hM p q r s`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `Z hZ d P hP'`. Rewrite using `[e1]`.

Conclude with `hK p q r s _ (k1 Z hZ) d P hP'`. Introduce `Z hZ d P hP'`. Rewrite using `[e2]`. Conclude with `hK p q r s _ (k2 Z hZ) d P hP'`. Introduce `Z hZ P`.

Rewrite using `[e1]`. Conclude with `hP p q r s _ (o1 Z hZ) P`. Introduce `Z hZ P`. Rewrite using `[e2]`. Conclude with `hP p q r s _ (o2 Z hZ) P`.

Introduce `Z hZ P Q`. Rewrite using `[e1, e1]`. Conclude with `hA p q r s _ _ (o1 Z hZ) (o1 _ (c1 Z hZ)) (a1 Z) P Q`. Introduce `Z hZ P Q`. Rewrite using `[e2, e2]`.

Conclude with `hA p q r s _ _ (o2 Z hZ) (o2 _ (c2 Z hZ)) (a2 Z) P Q`.
-/
theorem gradedOscillatorProperty_of (hK : KCStep) (hP : PCStep) (hA : AdjStep) (hM : MatStep) : FockH1Action.H1 := by
  intro p q r s
  obtain ⟨e1, e2, k1, k2, o1, o2, c1, c2, a1, a2⟩ := hM p q r s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ d P hP'
    rw [e1]; exact hK p q r s _ (k1 Z hZ) d P hP'
  · intro Z hZ d P hP'
    rw [e2]; exact hK p q r s _ (k2 Z hZ) d P hP'
  · intro Z hZ P
    rw [e1]; exact hP p q r s _ (o1 Z hZ) P
  · intro Z hZ P
    rw [e2]; exact hP p q r s _ (o2 Z hZ) P
  · intro Z hZ P Q
    rw [e1, e1]; exact hA p q r s _ _ (o1 Z hZ) (o1 _ (c1 Z hZ)) (a1 Z) P Q
  · intro Z hZ P Q
    rw [e2, e2]; exact hA p q r s _ _ (o2 Z hZ) (o2 _ (c2 Z hZ)) (a2 Z) P Q

end FockRL

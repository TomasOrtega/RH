import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfOuter

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun l => by have := l.1.isLt; have := l.2; simp at *; omega⟩`.
-/
theorem cf_last_isEmpty (r : ℕ) : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} :=
  ⟨fun l => by have := l.1.isLt; have := l.2; simp at *; omega⟩

/- English proof (translation)
Use `haveI := cf_last_isEmpty r`. Establish `hvol : (volume : Measure (Cf r (Fin.last r))) = Measure.dirac (fun l => isEmptyElim l)`. Rewrite using `[volume_pi, Measure.pi_of_empty]`. Use `haveI : IsFiniteMeasure (volume : Measure (Cf r (Fin.last r))) := by rw [hvol]; infer_instance`. Establish `hf : f = fun _ => f (fun l => isEmptyElim l)`.

Use function extensionality and compare the values at `c'`. Use `congr 1`. Use function extensionality and compare the values at `l`. Conclude with `isEmptyElim l`. Rewrite using `[hf]`.

Conclude with `integrable_const _`.
-/
theorem integrable_cf_last {r : ℕ} (f : Cf r (Fin.last r) → ℂ) : Integrable f := by
  haveI := cf_last_isEmpty r
  have hvol : (volume : Measure (Cf r (Fin.last r))) = Measure.dirac (fun l => isEmptyElim l) := by
    rw [volume_pi, Measure.pi_of_empty]
  haveI : IsFiniteMeasure (volume : Measure (Cf r (Fin.last r))) := by rw [hvol]; infer_instance
  have hf : f = fun _ => f (fun l => isEmptyElim l) := by
    funext c'
    congr 1
    funext l
    exact isEmptyElim l
  rw [hf]
  exact integrable_const _

end Formalism.FourierDecayAlt.P5.HerC

import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverThm
import Formalism.SharpRestriction.LevelLetterCocycles.ThetaScalarFamilyOfEigenvalue

open Formalism.BasicNotions

namespace Formalism.L2

def LocsCoverTwF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocsCoverTw (Fm.D x i)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem linkEta_iff_tw {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.LinkEta Fm ↔ LocsCoverTwF Fm := by
  rw [Formalism.MainNotions.N.linkEta_iff]
  exact Iff.rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem locsCoverTwF_of {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      ∃ (M : MtFam (Fm.D x i)) (T : NormalizedLocalCompatibility (Fm.D x i) M), HeckeStdTw T.B) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨M, T, hT⟩ := hx0 x hx i
  exact locsCoverTw_of_tie T hT

end Formalism.L2

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.IsClosedComplexSubmanifoldIn
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ProjDegreeEqFinrankAdjoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Matrix

/- English proof (translation)
Unfold `GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement`. Use `forall_congr' fun n => forall_congr' fun d => forall_congr' fun J => imp_congr_right fun _ => imp_congr_right fun _ => ?_` and prove the remaining obligations. Use `and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨U, ⟨S, rfl⟩, ⟨A, hA⟩, hU⟩`.

Conclude with `⟨S, ⟨A, hA⟩, fun M hM => (Objects.isFiniteProjection_iff J M).mp (hU M hM)⟩`. Introduce and unpack `⟨S, ⟨A, hA⟩, hS⟩`. Conclude with `⟨{M | ∃ f ∈ S, eval (fun p : Fin d × Fin n => M p.1 p.2) f ≠ 0}, ⟨S, rfl⟩, ⟨A, hA⟩, fun M hM => (Objects.isFiniteProjection_iff J M).mpr (hS M hM)⟩`. Simplify using `only [Set.Nonempty, Set.mem_ofPred_eq, Objects.isFiniteProjection_iff]`. Simplify using `only [Objects.orthoRows_eq, Objects.isFiniteProjection_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h m F hF`. Take `⟨U, hU, hk⟩` from `h m fun k => ⟨(F k)ᴴ, by`. Simplify `Unitary.star_mem (hF k)⟩` using `[Matrix.star_eq_conjTranspose]`. Use `⟨Uᴴ, by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU, fun k s => ?_⟩` and prove the remaining obligations.

Rewrite using `[← Objects.isFiniteProjection_iff]`. Simplify `hk k s` using `[Matrix.conjTranspose_mul]`. Introduce `h m F`. Take `⟨U, hU, hk⟩` from `h m (fun k => (F k : Matrix (Fin n) (Fin n) ℂ)ᴴ) fun k => by`. Simplify `Unitary.star_mem (F k).2` using `[Matrix.star_eq_conjTranspose]`.

Use `⟨Uᴴ, by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU, fun k s => ?_⟩` and prove the remaining obligations. Rewrite using `[Objects.isFiniteProjection_iff]`. Simplify `hk k s` using `[Matrix.conjTranspose_mul]`.
-/
theorem GenericProjectionFinite.equiv :
    GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement := by
  unfold GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement
  refine forall_congr' fun n => forall_congr' fun d => forall_congr' fun J =>
    imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · rintro ⟨U, ⟨S, rfl⟩, ⟨A, hA⟩, hU⟩
      exact ⟨S, ⟨A, hA⟩, fun M hM => (Objects.isFiniteProjection_iff J M).mp (hU M hM)⟩
    · rintro ⟨S, ⟨A, hA⟩, hS⟩
      exact ⟨{M | ∃ f ∈ S, eval (fun p : Fin d × Fin n => M p.1 p.2) f ≠ 0}, ⟨S, rfl⟩, ⟨A, hA⟩,
        fun M hM => (Objects.isFiniteProjection_iff J M).mpr (hS M hM)⟩
  · simp only [Set.Nonempty, Set.mem_ofPred_eq, Objects.isFiniteProjection_iff]
  · simp only [Objects.orthoRows_eq, Objects.isFiniteProjection_iff]
  · constructor
    · intro h m F hF
      obtain ⟨U, hU, hk⟩ := h m fun k => ⟨(F k)ᴴ, by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem (hF k)⟩
      refine ⟨Uᴴ, by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU,
        fun k s => ?_⟩
      rw [← Objects.isFiniteProjection_iff]
      simpa [Matrix.conjTranspose_mul] using hk k s
    · intro h m F
      obtain ⟨U, hU, hk⟩ := h m (fun k => (F k : Matrix (Fin n) (Fin n) ℂ)ᴴ) fun k => by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem (F k).2
      refine ⟨Uᴴ, by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU,
        fun k s => ?_⟩
      rw [Objects.isFiniteProjection_iff]
      simpa [Matrix.conjTranspose_mul] using hk k s

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

/- English proof (translation)
Introduce `k r`. Take `⟨b, hbS, hspan, hli⟩` from `exists_linearIndependent ℝ (JfS.lieOf (Nset k r))`. Establish `hfin : b.Finite` using `hli.setFinite`. Establish `: Fintype b` using `hfin.fintype`. Set `Xs : Fin (Fintype.card b) → B.Mat k r` to `fun i => ((Fintype.equivFin b).symm i : B.Mat k r)`.

Establish `hrange : Set.range Xs = b`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `((Fintype.equivFin b).symm i).2`.

Introduce `hx`. Use `⟨Fintype.equivFin b ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Simplify using `[Xs]`. Use `⟨Fintype.card b, Xs, fun i => hbS ((Fintype.equivFin b).symm i).2, fun X hX => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `LieSplitPf.lieHpk_of (fun t => (hX t).1)`.

Establish `hmem : X ∈ Submodule.span ℝ (Set.range Xs)`. Rewrite using `[hrange, hspan]`. Conclude with `Submodule.subset_span hX`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ha]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use extensionality with `p q`. Simplify using `[Matrix.smul_apply, Complex.real_smul]`.
-/
theorem nilpotent_lie_finite_holds : LieNFin := by
  intro k r
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ (JfS.lieOf (Nset k r))
  have hfin : b.Finite := hli.setFinite
  have : Fintype b := hfin.fintype
  let Xs : Fin (Fintype.card b) → B.Mat k r := fun i => ((Fintype.equivFin b).symm i : B.Mat k r)
  have hrange : Set.range Xs = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin b).symm i).2
    · intro hx
      refine ⟨Fintype.equivFin b ⟨x, hx⟩, ?_⟩
      simp [Xs]
  refine ⟨Fintype.card b, Xs, fun i => hbS ((Fintype.equivFin b).symm i).2, fun X hX => ⟨?_, ?_⟩⟩
  · exact LieSplitPf.lieHpk_of (fun t => (hX t).1)
  · have hmem : X ∈ Submodule.span ℝ (Set.range Xs) := by
      rw [hrange, hspan]
      exact Submodule.subset_span hX
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    refine ⟨a, ?_⟩
    rw [← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext p q
    simp [Matrix.smul_apply, Complex.real_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

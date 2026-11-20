import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameBasePtFree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameImage
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGraphDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FirstPointNeSecondPoint
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace TopPullFS

variable {κ : Type} [Fintype κ] {D : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem linApply_projMat (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) (k : Fin (D + 1)) :
    linApply (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) z ⟨(), k⟩ = z (e k) := by
  classical
  simp only [linApply, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem isSmoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  refine hm.mono fun z hz => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 => hi (congrFun h0 _)

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem fs_linApply (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) :
    (HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))).h
        (linApply (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) z) =
      Real.sqrt (∑ k, ‖z (e k)‖ ^ 2) := by
  simp only [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_sigma, Fintype.sum_unique]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [linApply_projMat]

end TopPullFS

open TopPullFS in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem TopPullFS.proof (hCM : ChangeOfModelStatement) (hBP : ProjFrameBasePtFree.Statement)
    (hIm : ProjFrameImage.Statement) (hDeg : ProjFrameGraphDeg.Statement) : TopPullFS.Statement := by
  intro D Ω _ _ κ _ I x m e hI hP hm hfr hFS
  obtain ⟨G, J, hJ, hJe⟩ := hDeg D Ω κ x e hP hfr
  have himg := hIm D Ω κ x e hfr
  have key := hCM I hI Unit (GlobalTheory κ) (GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x) (D + 1) (projMat e) G J
    (fun _ => HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))) (fun _ => HermLine.ofCone m) hP
    (hBP D Ω κ x e hfr) (by rw [himg]; exact IndefiniteRowSideFullHecke.Inter.isArithVar_bot D) hJ
    (fun _ => IndefiniteRowSideFullHecke.HilbertSamuel.P1.isSmoothHerm_fs) (fun _ => isSmoothHerm_ofCone hm) (fun _ => rfl)
    (fun _ z hz => by
      rw [fs_linApply]
      exact hFS z ⟨fun h0 => by obtain ⟨i, hi⟩ := hz.1 (); exact hi (congrFun h0 _), hz.2⟩)
  rw [himg, hJe] at key
  simpa [top, hhOf] using key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

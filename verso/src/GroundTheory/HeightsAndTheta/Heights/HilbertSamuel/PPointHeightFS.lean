import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPointHeightFS
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PointHeightFSAux

abbrev fsOne : HermLine (GlobalTheory (Fin 1)) := HermLine.ofCone (fsMetric (Ix (Fin 1)))

abbrev x0 : MRing (GlobalTheory (Fin 1)) := X ⟨(), 0⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem isSmoothHerm_fsOne : IsSmoothHerm fsOne := by
  refine (ProjLine.isSmoothMetric_fs (J := Ix (Fin 1))).mono fun z hz h0 => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact hi (congrFun h0 _)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Substitute using the available equality.

A detailed English derivation is pending.
-/
theorem divisorSupport_coordinate_point : divSupp (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) x0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun W hW => ?_
  obtain ⟨i, hi⟩ := hW.2 ()
  have hle := hW.1.1.2
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst hi0
  exact hi (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem logNorm_coordinate_point : logNorm fsOne x0 = fun _ => 0 := by
  funext z
  have hρ : fsOne.h z = ‖z ⟨(), 0⟩‖ := by
    let _ : Unique (Ix (Fin 1)) :=
      ⟨⟨⟨(), 0⟩⟩, fun p => by rcases p with ⟨⟨⟩, i⟩; rw [Subsingleton.elim i 0]; rfl⟩
    show ‖WithLp.toLp 2 z‖ = _
    rw [EuclideanSpace.norm_eq, Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    rfl
  simp only [logNorm, hρ, map_X, eval_X]
  rcases eq_or_ne (z ⟨(), 0⟩) 0 with h | h
  · simp [h]
  · rw [div_self (norm_ne_zero_iff.mpr h), Real.log_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem ptsIntegral_zero {e : ℕ} (P : Ideal (MRing (GlobalTheory (Fin 1))))
    (φ : Fin e → (Ix (Fin 1) → ℂ) → ℝ) : ptsIntegral P φ (fun _ => 0) = 0 := by
  classical
  unfold ptsIntegral
  split_ifs
  · simp [ptsIntegralAt, sheetDensity]
  · rfl

end PointHeightFSAux

open PointHeightFSAux in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem PointHeightFS.proof : PointHeightFS.Statement := by
  intro I hI
  classical
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) (0 + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot 0
  have hs : IsMultiHomog x0 fun _ => 1 := IndefiniteRowSideFullHecke.Inter.isMultiHomog_Xb 1 0
  have hx0 : x0 ∉ (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) := by
    rw [Ideal.mem_bot]
    exact X_ne_zero _
  have hR := (hI Unit (GlobalTheory (Fin 1))).2.2 ⊥ 0 Fin.elim0 fsOne x0 (fun _ => 1) hP (fun j => j.elim0)
    isSmoothHerm_fsOne (fun _ => rfl) hs hx0
  have hL : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (GlobalTheory (Fin 1))) fsOne : Fin 1 → _) =
      fun _ => fsOne := by
    funext j
    fin_cases j
    rfl
  rw [hL] at hR
  unfold hhOf
  rw [hR, recR, divisorSupport_coordinate_point, finsum_mem_empty, zero_sub, arInt, logNorm_coordinate_point, ptsIntegral_zero, neg_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

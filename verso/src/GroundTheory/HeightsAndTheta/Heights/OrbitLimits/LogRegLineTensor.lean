import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAddFirst
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDeLeSemiPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.IsMultiHomogPlaneCoordinate
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LelongSectionLimit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

/- English proof (translation)
Establish `hh : 0 < A.h z` using `A.pos z hz`. Establish `hreg : Real.log ((regLine A s ε ha hs).h z) = regLog A s ε z` using `congrFun (log_regLine A s ε ha hs) z`. Establish `hpos : 0 < (regLine A s ε ha hs).h z` using `(regLine A s ε ha hs).pos z hz`. Use `show Real.log ((regLine A s ε ha hs).h z * A.h z) = _`. Rewrite using `[Real.log_mul hpos.ne' hh.ne', hreg]`.

Unfold `regLog normSq`. Use `set x := ‖eval z (map (Int.castRingHom ℂ) s)‖`. Establish `hx2 : 0 ≤ x ^ 2` using `sq_nonneg x`. Establish `hnum : 0 < x ^ 2 + ε * A.h z ^ 2` using `by positivity`. Establish `hq : (x / A.h z) ^ 2 + ε = (x ^ 2 + ε * A.h z ^ 2) / A.h z ^ 2`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hq, Real.log_div hnum.ne' (pow_pos hh 2).ne', Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_regLine_tensor {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι)
    (s : MRing ι) {ε : ℝ} (hε : 0 < ε) {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : IsMultiHomog s a)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((regLine A s ε ha hs).tensor A).h z) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2 := by
  have hh : 0 < A.h z := A.pos z hz
  have hreg : Real.log ((regLine A s ε ha hs).h z) = regLog A s ε z := congrFun (log_regLine A s ε ha hs) z
  have hpos : 0 < (regLine A s ε ha hs).h z := (regLine A s ε ha hs).pos z hz
  show Real.log ((regLine A s ε ha hs).h z * A.h z) = _
  rw [Real.log_mul hpos.ne' hh.ne', hreg]
  unfold regLog normSq
  set x := ‖eval z (map (Int.castRingHom ℂ) s)‖
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hnum : 0 < x ^ 2 + ε * A.h z ^ 2 := by positivity
  have hq : (x / A.h z) ^ 2 + ε = (x ^ 2 + ε * A.h z ^ 2) / A.h z ^ 2 := by
    field_simp
  rw [hq, Real.log_div hnum.ne' (pow_pos hh 2).ne', Real.log_pow]
  push_cast
  ring

/- English proof (translation)
Introduce `K _ ι _ P n L A B s hP hL hA hB hBa hs`. Take `⟨a, ha, hsa, -⟩` from `id hs`. Establish `hAdd` using `Inter.PtsAddFirst.proof hInt`. Establish `key : ∀ ε ∈ Set.Ioi (0 : ℝ), ptsIntegral P (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2) (pot L)) (fun z => Real.log (B.h z)) - ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z)) = ptsIntegral P …`. Introduce `ε hε`.

Establish `h1` using `Inter.ptsIntegral_add_first_log hAdd (Q := P) (e := n) (L := L) (M := regLine A s ε ha hsa) (N := A) (D := B) hP hL (isSmoothHerm_regLine hA hε ha hsa) hA hB hBa`. Rewrite `h1` using `[log_regLine]`. Establish `h2 : ptsIntegral P (Fin.cons (fun z => Real.log (((regLine A s ε ha hsa).tensor A).h z)) (pot L)) (fun z => Real.log (B.h z)) = ptsIntegral P (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2) (pot L)) (fun z => Real.log (B.h z))`. Use `Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations.

Introduce `z hz`. Simplify using `only [Fin.cons_zero]`. Conclude with `log_regLine_tensor A s hε ha hsa z hz.1`. Introduce `z _`. Simplify using `only [Fin.cons_succ]`.

Rewrite using `[← h2, h1]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `((hLel K ι P n L A B s hP hL hA hB hBa hs).sub_const _).congr' (eventually_nhdsWithin_of_forall key)`.
-/
theorem PoincareLelongLimit.proof (hInt : PtsIntegrableStatement) (hLel : LelongSectionLimit.Statement) :
    PoincareLelongLimit.Statement := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hAdd := Inter.PtsAddFirst.proof hInt
  have key : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) (fun z => Real.log (B.h z)) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) := by
    intro ε hε
    have h1 := Inter.ptsIntegral_add_first_log hAdd (Q := P) (e := n) (L := L)
      (M := regLine A s ε ha hsa) (N := A) (D := B) hP hL (isSmoothHerm_regLine hA hε ha hsa) hA hB hBa
    rw [log_regLine] at h1
    have h2 : ptsIntegral P (Fin.cons (fun z => Real.log (((regLine A s ε ha hsa).tensor A).h z)) (pot L))
          (fun z => Real.log (B.h z)) =
        ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) (fun z => Real.log (B.h z)) := by
      refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
      refine Fin.cases ?_ (fun i => ?_) j
      · intro z hz
        simp only [Fin.cons_zero]
        exact log_regLine_tensor A s hε ha hsa z hz.1
      · intro z _
        simp only [Fin.cons_succ]
    rw [← h2, h1]
    ring
  exact ((hLel K ι P n L A B s hP hL hA hB hBa hs).sub_const _).congr'
    (eventually_nhdsWithin_of_forall key)

end GroundTheory.Heights₂.Heights.Targets

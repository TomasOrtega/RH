import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCTheta

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

/- English proof (translation)
Unfold `ThetaC ThetaNF`. Rewrite using `[hTT]`. Use `congr 3`. Use function extensionality and compare the values at `ρ`. Rewrite using `[aC_eq]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaC_eq_thetaNF {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A)
    (hTT : d.L.TT = (P.TT : ℂ)) : ThetaC d = ThetaNF P d := by
  unfold ThetaC ThetaNF
  rw [hTT]
  congr 3
  funext ρ
  rw [aC_eq]
  push_cast
  ring

/- English proof (translation)
Introduce `P A _ _ _ d _ hk _ hRel hTT`. Take `⟨⟨a, ha⟩, -⟩` from `h P A d hRel hk hTT`. Establish `hk1 : P.k - 1 + 1 = P.k` using `by omega`. Use `⟨fun j => if j = P.k + 1 then 1 else if j = P.k then ThetaC d else if j < P.k then a j else 0, fun Y => ?_, 0, ?_⟩` and prove the remaining obligations. Establish `e` using `ha Y`.

Rewrite `e` using `[hk1]`. Simplify using `only at e ⊢`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ]`. Simplify using `only [show P.k ≠ P.k + 1 by omega, ↓reduceIte]`. Rewrite using `[Finset.sum_congr rfl (fun j hj => by`.

Rewrite using `[if_neg (by have := Finset.mem_range.1 hj; omega), if_neg (by have := Finset.mem_range.1 hj; omega), if_pos (Finset.mem_range.1 hj)]), ← e]`. Normalize the expressions using the abelian group laws. Simplify using `only [show P.k ≠ P.k + 1 by omega, if_false, if_true, Int.cast_zero, zero_smul, add_zero]`. Conclude with `thetaC_eq_thetaNF d hTT`.
-/
theorem gTRTopNF_of_curvPoly (h : GTCCurvPoly) : GTRTopNF := by
  intro P A _ _ _ d _ hk _ hRel hTT
  obtain ⟨⟨a, ha⟩, -⟩ := h P A d hRel hk hTT
  have hk1 : P.k - 1 + 1 = P.k := by omega
  refine ⟨fun j => if j = P.k + 1 then 1 else if j = P.k then ThetaC d else if j < P.k then a j else 0,
    fun Y => ?_, 0, ?_⟩
  · have e := ha Y
    rw [hk1] at e
    dsimp only at e ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [show P.k ≠ P.k + 1 by omega, ↓reduceIte]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [if_neg (by have := Finset.mem_range.1 hj; omega), if_neg (by have := Finset.mem_range.1 hj; omega),
        if_pos (Finset.mem_range.1 hj)]), ← e]
    abel
  · simp only [show P.k ≠ P.k + 1 by omega, if_false, if_true, Int.cast_zero, zero_smul, add_zero]
    exact thetaC_eq_thetaNF d hTT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D q hq`. Take `⟨hq1, hq2⟩` from `hq`. Establish `hsec` using `(D.sec.2 q.2 hq2).1`. Establish `hU : B2.embWb k r (D.μsec q.2) ∈ B2.UWb k r` using `TwoByOneBlock.emb_mem_UWb (k := k) (r := r) hsec`. Establish `hv` using `TwoByOneBlock.sec_vec D.z_mem D.z'_mem D.sec hq2`.

Use `⟨(q.1, B2.embWb k r (D.μsec q.2)), ?_, ?_⟩` and prove the remaining obligations. Use `⟨hq1, ⟨hU.1, fun a _ => hU.2 a⟩, ?_⟩ show 0 < Complex.normSq (zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2))) - Tz k r D.z * Tz k r D.z'` and prove the remaining obligations. Establish `hz : zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2)) = q.2`. Unfold `zetaL fvec`. Simplify using `using hv.2.2`.

Rewrite using `[hz]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨((∏ a : Fin r, if (a : ℕ) < ((Fin.last r : Fin (r + 1)) : ℕ) then ‖q.1 a‖ ^ (Mdim k r a - 1) else 1 : ℝ) : ℂ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.ofReal_ne_zero]`. Use `Finset.prod_ne_zero_iff.mpr fun a _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `pow_ne_zero _ (norm_ne_zero_iff.mpr (hq1 a))`. Conclude with `one_ne_zero`. Introduce `J _`. Establish `hcell : wCell k r (Fin.last r) q.1 * B2.embWb k r (D.μsec q.2) = B.gq D q`.

Rewrite using `[Rad.wCell_last_eq]`. Conclude with `((TwoByOneBlock.bigCellFactor k r q.1 (D.μsec q.2)).1).symm`. Unfold `resG`. Rewrite using `[hcell]`.
-/
theorem radial_group_residue : RDGqRes := by
  intro k r Wp Wq _ _ _ _ _ _ D q hq
  obtain ⟨hq1, hq2⟩ := hq
  have hsec := (D.sec.2 q.2 hq2).1
  have hU : B2.embWb k r (D.μsec q.2) ∈ B2.UWb k r :=
    TwoByOneBlock.emb_mem_UWb (k := k) (r := r) hsec
  have hv := TwoByOneBlock.sec_vec D.z_mem D.z'_mem D.sec hq2
  refine ⟨(q.1, B2.embWb k r (D.μsec q.2)), ?_, ?_⟩
  · refine ⟨hq1, ⟨hU.1, fun a _ => hU.2 a⟩, ?_⟩
    show 0 < Complex.normSq (zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2))) - Tz k r D.z * Tz k r D.z'
    have hz : zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2)) = q.2 := by
      unfold zetaL fvec
      simpa using hv.2.2
    rw [hz]
    linarith
  · refine ⟨((∏ a : Fin r, if (a : ℕ) < ((Fin.last r : Fin (r + 1)) : ℕ) then ‖q.1 a‖ ^ (Mdim k r a - 1) else 1 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Complex.ofReal_ne_zero]
      refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
      split_ifs
      · exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hq1 a))
      · exact one_ne_zero
    · intro J _
      have hcell : wCell k r (Fin.last r) q.1 * B2.embWb k r (D.μsec q.2) = B.gq D q := by
        rw [Rad.wCell_last_eq]
        exact ((TwoByOneBlock.bigCellFactor k r q.1 (D.μsec q.2)).1).symm
      unfold resG
      rw [hcell]

end Formalism.FourierDecayAlt.P.CutSE

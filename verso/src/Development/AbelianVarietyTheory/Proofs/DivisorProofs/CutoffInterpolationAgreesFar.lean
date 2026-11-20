import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.InterpCurv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Move the embeddings inside the algebraic operations.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem interp_cutWeight_eq_and_glue : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {χ : ℝ → ℝ}, IsCutoff χ → ∀ {κ t R : ℝ}, 2 ≤ R → ∀ {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {r : (ι → ℂ) → ℝ}, (∀ z ∈ U, Real.exp 1 ≤ r z) → IsPosFrame U (interp H₀ H fun x => t * cutWeight χ κ R r x) → (∀ z ∈ U, R ^ 3 ≤ r z → interp H₀ H (fun x => t * cutWeight χ κ R r x) z = H₀ z) ∧ ∀ V : Set (ι → ℂ), U ⊆ V → IsPosFrame V H₀ → (∀ z ∈ V \ U, Tendsto r (𝓝[U] z) atTop) → IsPosFrame V fun z => open Classical in if z ∈ U then interp H₀ H (fun x => t * cutWeight χ κ R r x) z else H₀ z := by
  intro ι n _ _ _ χ hχ κ t R hR U H₀ H r _hr hI
  have h1 : ∀ z ∈ U, R ^ 3 ≤ r z →
      interp H₀ H (fun x => t * cutWeight χ κ R r x) z = H₀ z := by
    intro z _ hz3
    have hlR : 0 < Real.log R := Real.log_pos (by linarith)
    have hR3 : 0 < R ^ 3 := by positivity
    have hlog : 3 ≤ Real.log (r z) / Real.log R := by
      rw [le_div_iff₀ hlR]
      have h := Real.log_le_log hR3 hz3
      rw [Real.log_pow] at h
      push_cast at h
      linarith
    have hw : cutWeight χ κ R r z = 0 := by
      simp [cutWeight, hχ.eq_zero _ hlog]
    simp [interp, hw]
  refine ⟨h1, fun V _ hV hlim => ?_⟩
  refine ⟨hV.isOpen, fun a b => ?_, fun z hz => ?_⟩
  · intro z hz
    apply ContDiffAt.contDiffWithinAt
    by_cases hzU : z ∈ U
    · have hc : ContDiffAt ℝ ∞
          (fun x => interp H₀ H (fun x => t * cutWeight χ κ R r x) x a b) z :=
        (hI.smooth a b).contDiffAt (hI.isOpen.mem_nhds hzU)
      refine hc.congr_of_eventuallyEq ?_
      filter_upwards [hI.isOpen.mem_nhds hzU] with x hx
      simp [hx]
    · have hc : ContDiffAt ℝ ∞ (fun x => H₀ x a b) z :=
        (hV.smooth a b).contDiffAt (hV.isOpen.mem_nhds hz)
      refine hc.congr_of_eventuallyEq ?_
      have hev := (hlim z ⟨hz, hzU⟩).eventually (eventually_ge_atTop (R ^ 3))
      rw [eventually_nhdsWithin_iff] at hev
      filter_upwards [hev] with x hx
      by_cases hxU : x ∈ U
      · simp [hxU, h1 x hxU (hx hxU)]
      · simp [hxU]
  · by_cases hzU : z ∈ U
    · simpa [hzU] using hI.posDef z hzU
    · simpa [hzU] using hV.posDef z hz

end GlobalTheory.InterpCurv

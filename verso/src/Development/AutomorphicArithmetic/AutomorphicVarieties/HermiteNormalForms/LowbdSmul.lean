import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
private theorem lowbd_cont (L : Type) [Field L] [NumberField L] (N : ℕ) :
    Continuous (fun p : HS L N × VR L N => qR p.1 p.2) := by
  unfold qR mat
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply]
  have hv : Continuous fun p : HS L N × VR L N => (p.1 : InfinitePlace L → Fin N → Fin N → ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : HS L N × VR L N => (p.2 : InfinitePlace L → Fin N → ℂ) := continuous_snd
  refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
  refine continuous_finset_sum _ fun i _ => ?_
  refine (continuous_star.comp ((continuous_apply i).comp ((continuous_apply w).comp hz))).mul ?_
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp hv))).mul
    ((continuous_apply j).comp ((continuous_apply w).comp hz))

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem lowbd_smul {L : Type} [Field L] [NumberField L] {N : ℕ} (k : HS L N) (r : ℝ)
    (z : VR L N) : qR k (r • z) = r ^ 2 * qR k z := by
  unfold qR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.smul_apply, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, smul_eq_mul]
  ring

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
private theorem lowbd_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  have hne : ∃ w, z w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz (funext hc)
  obtain ⟨w0, hw0⟩ := hne
  have hp : ∀ w, (mat h w).PosDef := hh
  unfold qR
  apply Finset.sum_pos'
  · intro w _
    by_cases hw : z w = 0
    · simp [hw]
    · exact le_of_lt (Complex.pos_iff.mp ((hp w).dotProduct_mulVec_pos hw)).1
  · exact ⟨w0, Finset.mem_univ _, (Complex.pos_iff.mp ((hp w0).dotProduct_mulVec_pos hw0)).1⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.KT.lowbd :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in nhds h, ∀ z : VR L N, c * ‖z‖ ^ 2 ≤ qR k z := by
  intro L _ _ N h hh
  have hK : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hcont := lowbd_cont L N
  have hsec : Continuous fun z : VR L N => (h, z) := by fun_prop
  obtain ⟨m, hm, hmle⟩ := hK.exists_forall_le' (f := fun z => qR h z)
    (hcont.comp hsec).continuousOn (a := 0)
    (fun z hz => lowbd_pos hh (by
      intro h0
      rw [h0] at hz
      simp at hz))
  refine ⟨m / 2, by positivity, ?_⟩
  have hev : ∀ᶠ k in nhds h, ∀ z ∈ Metric.sphere (0 : VR L N) 1, m / 2 < qR k z := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hlt : m / 2 < qR h z := by linarith [hmle z hz]
    exact (hcont.tendsto (h, z)).eventually (lt_mem_nhds hlt)
  filter_upwards [hev] with k hk z
  by_cases hz : z = 0
  · subst hz
    have h0 : qR k (0 : VR L N) = 0 := by simpa using lowbd_smul k 0 (0 : VR L N)
    simp [h0]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : VR L N) 1 := by
      simp [norm_smul, hn.ne']
    have hzu : ‖z‖ • (‖z‖⁻¹ • z) = z := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hlt := hk _ hu
    calc m / 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 * qR k (‖z‖⁻¹ • z) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hlt.le (by positivity)
      _ = qR k (‖z‖ • (‖z‖⁻¹ • z)) := (lowbd_smul k ‖z‖ _).symm
      _ = qR k z := by rw [hzu]

import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

namespace UpperTheory.V.Af.Rs

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
private theorem unf_meas_strip : MeasurableSet strip := by
  unfold strip
  exact (measurableSet_le measurable_const UpperHalfPlane.continuous_re.measurable).inter
    (measurableSet_lt UpperHalfPlane.continuous_re.measurable measurable_const)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem unf_meas_smul (γ : SL(2, ℤ)) : Measurable (fun z : ℍ => γ • z) := by
  refine Continuous.measurable ?_
  rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff]
  have h : (UpperHalfPlane.coe ∘ fun z : ℍ => γ • z) = fun z : ℍ =>
      (((algebraMap ℤ ℝ (γ 0 0) : ℂ) * z + (algebraMap ℤ ℝ (γ 0 1) : ℂ)) /
      ((algebraMap ℤ ℝ (γ 1 0) : ℂ) * z + (algebraMap ℤ ℝ (γ 1 1) : ℂ))) :=
    funext fun z => UpperHalfPlane.coe_specialLinearGroup_apply γ z
  rw [h]
  refine Continuous.div (by fun_prop) (by fun_prop) fun z => ?_
  have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
  simpa [UpperHalfPlane.denom] using this

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem unf_countable : Countable SL(2, ℤ) := @Subtype.countable (Matrix (Fin 2) (Fin 2) ℤ) (show Countable (Fin 2 → Fin 2 → ℤ) from inferInstance) _

end UpperTheory.V.Af.Rs

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem hasSum_integral_fd_smul_eq_two_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hU : UpperTheory.V.Af.Rs.UnfM) (f : ℍ → E) (hfm : StronglyMeasurable f)
    (hfi : Integrable f volume) :
    HasSum (fun γ : SL(2, ℤ) => ∫ z in ModularGroup.fd, f (γ • z)) ((2 : ℝ) • ∫ z, f z) := by
  have hsum : Integrable f (Measure.sum fun γ : SL(2, ℤ) =>
      Measure.map (fun z => γ • z) (volume.restrict ModularGroup.fd)) := by
    rw [hU, two_smul]
    exact hfi.add_measure hfi
  have h1 := hasSum_integral_measure hsum
  rw [hU, two_smul, integral_add_measure hfi hfi, ← two_smul ℝ] at h1
  convert h1 using 1
  funext γ
  rw [integral_map (UpperTheory.V.Af.Rs.unf_meas_smul γ).aemeasurable hfm.aestronglyMeasurable]

open UpperTheory.V.Af.Rs in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Rs.unfold :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.UnfM → UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.Unfold := by
  classical
  intro _ hU hR H Φ hH hHi hHΦ hΦ
  haveI := unf_countable
  have hstrip := unf_meas_strip
  set f : ℍ → ℂ := strip.indicator H with hf
  have hfm : StronglyMeasurable f := hH.stronglyMeasurable.indicator hstrip
  have hfi : Integrable f volume := (integrable_indicator_iff hstrip).mpr hHi
  have hA := hasSum_integral_fd_smul_eq_two_integral hU f hfm hfi
  have hB := hasSum_integral_fd_smul_eq_two_integral hU (fun z => ‖f z‖) hfm.norm hfi.norm
  have hval : (2 : ℝ) • ∫ z, f z = 2 * ∫ z in strip, H z := by
    rw [hf, integral_indicator hstrip]
    norm_num
  rw [hval] at hA
  have hfγ : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = if γ • z ∈ strip then Φ (row γ) z else 0 := by
    intro γ z
    rw [hf]
    split_ifs with h
    · rw [indicator_of_mem h, hHΦ]
    · rw [indicator_of_notMem h]
  let g : SL(2, ℤ) → Cop := fun γ => ⟨row γ, hR.1 γ⟩
  have hA' := (Equiv.sigmaFiberEquiv g).hasSum_iff.mpr hA
  refine HasSum.sigma hA' fun x => ?_
  have hint : ∀ c : {γ // g γ = x},
      Integrable (fun z => f (c.1 • z)) (volume.restrict ModularGroup.fd) := by
    intro c
    refine Integrable.mono (hΦ x)
      ((hfm.comp_measurable (unf_meas_smul c.1)).aestronglyMeasurable) (ae_of_all _ fun z => ?_)
    have hrow : row c.1 = x := congrArg Subtype.val c.2
    rw [hfγ]
    split_ifs
    · rw [hrow]
    · simp
  have hsumm : Summable fun c : {γ // g γ = x} => ∫ z in ModularGroup.fd, ‖f (c.1 • z)‖ :=
    hB.summable.comp_injective Subtype.val_injective
  have h := hasSum_integral_of_summable_integral_norm hint hsumm
  have heq : ∀ z, ∑' c : {γ // g γ = x}, f (c.1 • z) = Φ x z := by
    intro z
    obtain ⟨γ0, ⟨h0row, h0s⟩, huniq⟩ := hR.2 z x
    have hg0 : g γ0 = x := Subtype.ext h0row
    rw [tsum_eq_single ⟨γ0, hg0⟩]
    · rw [hfγ, if_pos h0s, h0row]
    · intro c hc
      rw [hfγ, if_neg]
      intro hs
      apply hc
      exact Subtype.ext (huniq c.1 ⟨congrArg Subtype.val c.2, hs⟩)
  simp only [heq] at h
  exact h

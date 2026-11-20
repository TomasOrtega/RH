import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem latTau_snd_ne (L : PeriodPair) : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Evaluate the numerical expressions.
-/
theorem latTau_im_ne (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have h2 := latTau_snd_ne L
  obtain ⟨r, hr⟩ : ∃ r : ℝ, L.ω₁ / L.ω₂ = (r : ℂ) :=
    ⟨(L.ω₁ / L.ω₂).re, Complex.ext (by simp) (by simp [h])⟩
  have h1 : L.ω₁ = (r : ℂ) * L.ω₂ := by rw [← hr, div_mul_cancel₀ _ h2]
  have h3 := (LinearIndependent.pair_iff.mp L.indep) 1 (-r)
    (by rw [Complex.real_smul, Complex.real_smul, h1]; push_cast; ring)
  norm_num at h3

/- English proof (translation)
Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem latTau (L : PeriodPair) : ∃ (c : ℂ) (τ : ℍ), IsTauOf L c τ := by
  have h2 := latTau_snd_ne L
  rcases lt_or_gt_of_ne (latTau_im_ne L) with hneg | hpos
  · refine ⟨L.ω₂, ⟨-(L.ω₁ / L.ω₂), by rw [Complex.neg_im]; linarith⟩, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice]
    try simp only [UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp; try ring⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨-u, v, by push_cast; field_simp; try ring⟩
  · refine ⟨L.ω₂, ⟨L.ω₁ / L.ω₂, hpos⟩, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice]
    try simp only [UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp; try ring⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨u, v, by field_simp; try ring⟩

end ReciprocityTheory.ChartRestriction.L1

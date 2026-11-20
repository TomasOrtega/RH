import Mathlib

open MeasureTheory Pointwise

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_zero_of_ae_fundamentalDomain_of_leftInvariant
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsHaarMeasure] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ)
    (hF : Continuous F) (hinv : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x)
    (hae : ∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) : ∀ x, F x = 0 := by
  set U : Set G := {x | F x ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hF continuous_const
  have hUinv : ∀ g : Γ, g • U = U := by
    intro g
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, hUdef, Set.mem_setOf_eq, Subgroup.smul_def,
      smul_eq_mul]
    rw [hinv _ (Γ.inv_mem g.2)]
  have hU𝓕 : μ (U ∩ 𝓕) = 0 := by
    rw [ae_iff, Measure.restrict_apply hUo.measurableSet] at hae
    simpa [hUdef] using hae
  have hU0 : μ U = 0 := h𝓕.measure_zero_of_invariant U hUinv hU𝓕
  have hUe : U = ∅ := by
    by_contra hne
    exact (hUo.measure_pos μ (Set.nonempty_iff_ne_empty.mpr hne)).ne' hU0
  intro x
  by_contra hx
  have : x ∈ U := hx
  rw [hUe] at this
  exact this

end GlobalTheory

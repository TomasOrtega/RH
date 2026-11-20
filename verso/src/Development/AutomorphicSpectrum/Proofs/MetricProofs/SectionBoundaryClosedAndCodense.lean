import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorusStatement
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Bdry

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem bdry_isClosed_dense_compl (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X)
    (hs : IsSection A L s) (hn : IsSNC A L s m W) : IsClosed (bdry s) ∧ Dense (bdry s)ᶜ := by
  have key := GlobalTheory.T.snc_boundary_coordinate_chart e X A L s nb m W hs hn
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨ψ, -, hyψ, S, hS⟩ := key y
    have hopen : IsOpen (ψ.source ∩ ψ ⁻¹' {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0}) := by
      apply ψ.continuousOn.isOpen_inter_preimage ψ.open_source
      have : {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0} = ⋂ i ∈ S, {z : Fin e → ℂ | z i ≠ 0} := by
        ext z; simp
      rw [this]
      exact isOpen_biInter_finset fun i _ =>
        isOpen_ne_fun (continuous_apply i) continuous_const
    have hmem : y ∈ ψ.source ∩ ψ ⁻¹' {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0} := by
      refine ⟨hyψ, fun i hi h0 => hy ((hS y hyψ).2 ⟨i, hi, h0⟩)⟩
    refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
    rintro y' ⟨h1, h2⟩ hb
    obtain ⟨i, hi, h0⟩ := (hS y' h1).1 hb
    exact h2 i hi h0
  · rw [dense_iff_inter_open]
    intro V hV ⟨x, hx⟩
    obtain ⟨ψ, -, hxψ, S, hS⟩ := key x
    have hsub : V ∩ ψ.source ⊆ ψ.source := Set.inter_subset_right
    have himg : IsOpen (ψ '' (V ∩ ψ.source)) :=
      ψ.isOpen_image_of_subset_source (hV.inter ψ.open_source) hsub
    have hne : (ψ '' (V ∩ ψ.source)).Nonempty := ⟨ψ x, x, ⟨hx, hxψ⟩, rfl⟩
    obtain ⟨z, hz, hz0⟩ := (GlobalTheory.T.dense_coordinate_torus e).inter_open_nonempty _ himg hne
    obtain ⟨y, ⟨hyV, hyψ⟩, rfl⟩ := hz
    refine ⟨y, hyV, fun hb => ?_⟩
    obtain ⟨i, -, h0⟩ := (hS y hyψ).1 hb
    exact hz0 i h0

end GlobalTheory.CompanionTheory.Ar.Bdry

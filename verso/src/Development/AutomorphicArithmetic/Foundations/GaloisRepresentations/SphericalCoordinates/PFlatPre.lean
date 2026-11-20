import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.W2.flatPre_of :
    UpperTheory.Gal.W2.FlatPre := by
  intro V _ _ V' _ _ Y B s hs φ φ' v₀ w hφ hB
  have key : ∀ (U : Y.Opens) (f : Γ(Y, U)), ⊤ ≤ s (φ v₀) ⁻¹ᵁ U →
      fderiv ℂ (fun v => valAt' (s (φ v)) U f) v₀ w =
        fderiv ℂ (fun b => valAt' (s b) U f) (φ v₀) (φ' w) := by
    intro U f hU
    obtain ⟨hopen, hdiff⟩ := hs U f
    have hmem : φ v₀ ∈ {b ∈ B | ⊤ ≤ s b ⁻¹ᵁ U} := ⟨hB, hU⟩
    have hd : DifferentiableAt ℂ (fun b => valAt' (s b) U f) (φ v₀) :=
      (hdiff _ hmem).differentiableAt (hopen.mem_nhds hmem)
    have hc := hd.hasFDerivAt.comp v₀ hφ
    have he : fderiv ℂ (fun v => valAt' (s (φ v)) U f) v₀ = _ := hc.fderiv
    rw [he]
    rfl
  constructor
  · intro h U f hU
    rw [← key U f hU]
    exact h U f hU
  · intro h U f hU
    rw [key U f hU]
    exact h U f hU

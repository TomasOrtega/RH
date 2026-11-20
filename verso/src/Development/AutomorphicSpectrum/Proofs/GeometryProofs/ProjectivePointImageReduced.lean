import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.SncRes

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Equip the data with the indicated structure. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isReduced_image_of_quasiCompact {X Y : Scheme.{0}} [IsReduced X] (f : X ⟶ Y) [QuasiCompact f] :
    IsReduced f.image := by
  have : ∀ x : f.image, _root_.IsReduced (f.image.presheaf.stalk x) := fun x => by
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := f.imageι x) trivial
    have hV : IsAffineOpen (f.imageι ⁻¹ᵁ U) := hU.preimage f.imageι
    have hx' : x ∈ f.imageι ⁻¹ᵁ U := hx
    have : _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ U) :=
      isReduced_of_injective (f.toImage.app (f.imageι ⁻¹ᵁ U)).hom
        (f.toImage_app_injective ⟨U, hU⟩)
    letI := f.image.presheaf.algebra_section_stalk (⟨x, hx'⟩ : f.imageι ⁻¹ᵁ U)
    have := hV.isLocalization_stalk ⟨x, hx'⟩
    exact isReduced_localizationPreserves (hV.primeIdealOf ⟨x, hx'⟩).asIdeal.primeCompl _ ‹_›
  exact isReduced_of_isReduced_stalk f.image

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem quasiCompact_point {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (hx : x ≠ 0) :
    QuasiCompact (point ℚ x hx) := by
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str ℚ N
  have h : QuasiCompact (point ℚ x hx ≫ PSpace.str ℚ N) := by
    rw [point_str]
    infer_instance
  exact .of_comp _ (PSpace.str ℚ N)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem closure_reduced_dominant : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (hx : x ≠ 0),
    IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage := by
  intro Ω _ _ N x hx
  have := quasiCompact_point x hx
  exact ⟨isReduced_image_of_quasiCompact _, inferInstance⟩

end GlobalTheory.CompanionTheory.Ar.SncRes

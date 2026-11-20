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
Establish `: ∀ x : f.image, _root_.IsReduced (f.image.presheaf.stalk x)` using `fun x => by`. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := f.imageι x) trivial`. Establish `hV : IsAffineOpen (f.imageι ⁻¹ᵁ U)` using `hU.preimage f.imageι`. Establish `hx' : x ∈ f.imageι ⁻¹ᵁ U` using `hx`. Establish `: _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ U)` using `isReduced_of_injective (f.toImage.app (f.imageι ⁻¹ᵁ U)).hom (f.toImage_app_injective ⟨U, hU⟩)`.

Use `letI := f.image.presheaf.algebra_section_stalk (⟨x, hx'⟩ : f.imageι ⁻¹ᵁ U)`. Use `hV.isLocalization_stalk ⟨x, hx'⟩` as an intermediate fact. Conclude with `isReduced_localizationPreserves (hV.primeIdealOf ⟨x, hx'⟩).asIdeal.primeCompl _ ‹_›`. Conclude with `isReduced_of_isReduced_stalk f.image`.
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
Use `ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str ℚ N` as an intermediate fact. Establish `h : QuasiCompact (point ℚ x hx ≫ PSpace.str ℚ N)`. Rewrite using `[point_str]`. Use `infer_instance`. Conclude with `.of_comp _ (PSpace.str ℚ N)`.
-/
theorem quasiCompact_point {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (hx : x ≠ 0) :
    QuasiCompact (point ℚ x hx) := by
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str ℚ N
  have h : QuasiCompact (point ℚ x hx ≫ PSpace.str ℚ N) := by
    rw [point_str]
    infer_instance
  exact .of_comp _ (PSpace.str ℚ N)

/- English proof (translation)
Introduce `Ω _ _ N x hx`. Use `quasiCompact_point x hx` as an intermediate fact. Conclude with `⟨isReduced_image_of_quasiCompact _, inferInstance⟩`.
-/
theorem closure_reduced_dominant : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (hx : x ≠ 0),
    IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage := by
  intro Ω _ _ N x hx
  have := quasiCompact_point x hx
  exact ⟨isReduced_image_of_quasiCompact _, inferInstance⟩

end GlobalTheory.CompanionTheory.Ar.SncRes

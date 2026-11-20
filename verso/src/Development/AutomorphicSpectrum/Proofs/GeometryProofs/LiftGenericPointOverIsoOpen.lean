import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.Coords

/- English proof (translation)
Establish `hr : Set.range ξ ⊆ Set.range U.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hU (show x ∈ (⊤ : (Sp Ω).Opens) from trivial)`. Set `ζ₀ : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme` to `IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U)`.

Establish `hζ₀ : ζ₀ ≫ (f ∣_ U ≫ U.ι) = ξ`. Simplify using `only [ζ₀, Category.assoc, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]`. Establish `hT : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f` using `morphismRestrict_ι f U`. Establish `hfac : (ζ₀ ≫ (f ⁻¹ᵁ U).ι) ≫ f = ξ`. Rewrite using `[Category.assoc, ← hT, hζ₀]`.

Use `⟨ζ₀ ≫ (f ⁻¹ᵁ U).ι, hfac, ⟨?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[DenseRange, dense_iff_inter_open]`. Introduce `W hW hne`. Take `⟨v, hvW, hvU⟩` from `hd.inter_open_nonempty W hW hne`. Set `T : (f ⁻¹ᵁ U).toScheme ⟶ X` to `f ∣_ U ≫ U.ι`.

Establish `hTo : IsOpenImmersion T` using `inferInstance`. Set `W' : Set (f ⁻¹ᵁ U).toScheme` to `(f ⁻¹ᵁ U).ι ⁻¹' W`. Establish `hW' : IsOpen W'` using `hW.preimage (f ⁻¹ᵁ U).ι.continuous`. Establish `himg : IsOpen (T '' W')` using `T.isOpenEmbedding.isOpenMap _ hW'`. Establish `hne' : (T '' W').Nonempty` using `⟨T ⟨v, hvU⟩, ⟨v, hvU⟩, by`.

Express the relevant statement in the definitionally equal form `(f ⁻¹ᵁ U).ι ⟨v, hvU⟩ ∈ W`. Conclude with `hvW, rfl⟩`. Take `⟨y, hyT, p, rfl⟩` from `(ξ.denseRange).inter_open_nonempty _ himg hne'`. Take `⟨w, hwW, hw⟩` from `hyT`. Establish `hp : T (ζ₀ p) = ξ p`.

Rewrite using `[← hζ₀]`. Simplify using `[T]`. Establish `hwp : w = ζ₀ p` using `T.isOpenEmbedding.injective (hw.trans hp.symm)`. Use `⟨(ζ₀ ≫ (f ⁻¹ᵁ U).ι) p, ?_, p, rfl⟩` and prove the remaining obligations. Substitute `hwp` using the available equality.

Simplify `hwW` using `[W']`. Introduce `x _`. Establish `hx : ξ x ∈ U` using `hU (show x ∈ (⊤ : (Sp Ω).Opens) from trivial)`. Rewrite `hx` using `[← hfac]`. Conclude with `hx`.
-/
theorem dense_point_lift (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    [IsDominant ξ] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)]
    (hd : Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X')) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) :
    ∃ ζ : Sp Ω ⟶ X', ζ ≫ f = ξ ∧ IsDominant ζ ∧ ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hU (show x ∈ (⊤ : (Sp Ω).Opens) from trivial)

  let ζ₀ : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U)
  have hζ₀ : ζ₀ ≫ (f ∣_ U ≫ U.ι) = ξ := by
    simp only [ζ₀, Category.assoc, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]
  have hT : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := morphismRestrict_ι f U
  have hfac : (ζ₀ ≫ (f ⁻¹ᵁ U).ι) ≫ f = ξ := by
    rw [Category.assoc, ← hT, hζ₀]
  refine ⟨ζ₀ ≫ (f ⁻¹ᵁ U).ι, hfac, ⟨?_⟩, ?_⟩
  ·
    rw [DenseRange, dense_iff_inter_open]
    intro W hW hne
    obtain ⟨v, hvW, hvU⟩ := hd.inter_open_nonempty W hW hne
    let T : (f ⁻¹ᵁ U).toScheme ⟶ X := f ∣_ U ≫ U.ι
    have hTo : IsOpenImmersion T := inferInstance
    let W' : Set (f ⁻¹ᵁ U).toScheme := (f ⁻¹ᵁ U).ι ⁻¹' W
    have hW' : IsOpen W' := hW.preimage (f ⁻¹ᵁ U).ι.continuous
    have himg : IsOpen (T '' W') := T.isOpenEmbedding.isOpenMap _ hW'
    have hne' : (T '' W').Nonempty :=
      ⟨T ⟨v, hvU⟩, ⟨v, hvU⟩, by
        change (f ⁻¹ᵁ U).ι ⟨v, hvU⟩ ∈ W
        exact hvW, rfl⟩
    obtain ⟨y, hyT, p, rfl⟩ := (ξ.denseRange).inter_open_nonempty _ himg hne'
    obtain ⟨w, hwW, hw⟩ := hyT
    have hp : T (ζ₀ p) = ξ p := by
      rw [← hζ₀]; simp [T]
    have hwp : w = ζ₀ p := T.isOpenEmbedding.injective (hw.trans hp.symm)
    refine ⟨(ζ₀ ≫ (f ⁻¹ᵁ U).ι) p, ?_, p, rfl⟩
    subst hwp
    simpa [W'] using hwW
  · intro x _
    have hx : ξ x ∈ U := hU (show x ∈ (⊤ : (Sp Ω).Opens) from trivial)
    rw [← hfac] at hx
    exact hx

end GlobalTheory.CompanionTheory.Ar.Coords

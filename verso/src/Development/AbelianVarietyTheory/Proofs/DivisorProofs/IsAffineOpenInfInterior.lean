import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffOff

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y h U`. Establish `hs` using `snc_gen_iff.1 h`. Unfold `boundary at hs`. Use `set V := interior Y with hVdef`. Establish `key : ∀ y : Y.X, ∃ W : Y.X.Opens, y ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen (V.ι ⁻¹ᵁ W)`.

Introduce `y`. Take `⟨-, W, hy, n, f, J, -, hI⟩` from `hs y`. Establish `e : W.1 ⊓ V = Y.X.basicOpen (∏ i ∈ J, f i)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hW, hV⟩`. Assume the negation of the conclusion as `hz`. Establish `: z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support`. Rewrite using `[Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]`. Conclude with `hz`.

Rewrite `this` using `[← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Conclude with `this hV`. Introduce `hz`. Establish `hW : z ∈ W.1` using `Y.X.basicOpen_le _ hz`. Use `⟨hW, by_contra fun hV ↦ ?_⟩` and prove the remaining obligations.

Establish `: z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support`. Rewrite using `[← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Conclude with `hV`. Rewrite `this` using `[Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]`. Conclude with `this hz`.

Use `⟨W.1, hy, W.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm, e]`. Conclude with `W.2.basicOpen _`. Establish `: IsAffineHom V.ι` using `isAffineHom_of_forall_exists_isAffineOpen _ key`. Establish `h2` using `U.2.preimage V.ι`.

Rewrite `h2` using `[← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]`. Rewrite using `[inf_comm]` and apply the resulting hypothesis.
-/
theorem isAffineOpen_inf_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ U : Y.X.affineOpens, IsAffineOpen (U.1 ⊓ interior Y) := by
  intro E _ _ _ H Dw l Xo c Y h U
  have hs := snc_gen_iff.1 h
  unfold boundary at hs
  set V := interior Y with hVdef
  have key : ∀ y : Y.X, ∃ W : Y.X.Opens, y ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen (V.ι ⁻¹ᵁ W) := by
    intro y
    obtain ⟨-, W, hy, n, f, J, -, hI⟩ := hs y
    have e : W.1 ⊓ V = Y.X.basicOpen (∏ i ∈ J, f i) := by
      ext z
      constructor
      · rintro ⟨hW, hV⟩
        by_contra hz
        have : z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
          rw [Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
          exact hz
        rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
        exact this hV
      · intro hz
        have hW : z ∈ W.1 := Y.X.basicOpen_le _ hz
        refine ⟨hW, by_contra fun hV ↦ ?_⟩
        have : z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
          rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
          exact hV
        rw [Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span,
          Scheme.zeroLocus_singleton] at this
        exact this hz
    refine ⟨W.1, hy, W.2, ?_⟩
    rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_comm, e]
    exact W.2.basicOpen _
  have : IsAffineHom V.ι := isAffineHom_of_forall_exists_isAffineOpen _ key
  have h2 := U.2.preimage V.ι
  rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι] at h2
  rwa [inf_comm]

end GlobalTheory.AffOff

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseChangeCompatibleGlobalOneFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleGlobalOneFormsFiniteProjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

/- English proof (translation)
Establish `h : SmoothOfRelativeDimension g (x ≫ s)`. Use `smoothOfRelativeDimension_comp 0 g x s` as an intermediate fact. Simplify using `using this`. Rewrite `h` using `[hx]`. Prove the components needed by the constructor for the conclusion.

Conclude with `(HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).1 h`. Establish `h2 : Smooth (spMap (algebraMap R B))` using `SmoothOfRelativeDimension.smooth g _`. Conclude with `RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h2)`.
-/
theorem smooth_of_openImm {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (g : ℕ) (hs : SmoothOfRelativeDimension g s) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B))
    [IsOpenImmersion x] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R B) ∧ Algebra.Smooth R B := by
  have h : SmoothOfRelativeDimension g (x ≫ s) := by
    have := smoothOfRelativeDimension_comp 0 g x s
    simpa using this
  rw [hx] at h
  constructor
  · exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).1 h
  · have h2 : Smooth (spMap (algebraMap R B)) := SmoothOfRelativeDimension.smooth g _
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h2)

/- English proof (translation)
Take `⟨s, hs, H⟩` from `h`. Take `⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p.asIdeal` from `by by_contra! hc`. Conclude with `p.2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))`. Set `Bt` to `Localization.Away t`. Establish `hstd : Algebra.IsStandardSmoothOfRelativeDimension g R Bt` using `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).1 (by rw [IsScalarTower.algebraMap_eq R B Bt]; exact H t ht)`.

Establish `: Algebra.FormallyEtale B Bt` using `.of_isLocalization (Submonoid.powers t)`. Set `e` to `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B Bt`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ q : PrimeSpectrum Bt, PrimeSpectrum.comap (algebraMap B Bt) q = p := by`. Establish `: p ∈ Set.range (PrimeSpectrum.comap (algebraMap B Bt))`. Rewrite using `[PrimeSpectrum.localization_away_comap_range Bt t]`.

Conclude with `htp`. Conclude with `this`. Establish `: Nontrivial Bt` using `PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩`. Establish `: Algebra.IsStandardSmooth R Bt` using `hstd.isStandardSmooth`. Establish `: Module.Free Bt Ω[Bt⁄R]` using `Algebra.IsStandardSmooth.free_kaehlerDifferential`.

Establish `h1` using `Module.rankAtStalk_baseChange (R := B) (S := Bt) (M := Ω[B⁄R]) q`. Rewrite `h1` using `[hq]`. Rewrite using `[← h1, Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_eq_finrank_of_free]`. Establish `hf : Module.finrank Bt Ω[Bt⁄R] = g`. Rewrite using `[Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := Bt) g]`.

Simplify using the standard rewrite rules. Simplify using `[hf]`.
-/
theorem rankAtStalk_kaehler_of_locally {R B : Type} [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (g : ℕ) (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R B))
    (p : PrimeSpectrum B) : Module.rankAtStalk Ω[B⁄R] p = g := by
  obtain ⟨s, hs, H⟩ := h
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p.asIdeal := by
    by_contra! hc
    exact p.2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  let Bt := Localization.Away t
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension g R Bt :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).1
      (by rw [IsScalarTower.algebraMap_eq R B Bt]; exact H t ht)
  have : Algebra.FormallyEtale B Bt := .of_isLocalization (Submonoid.powers t)
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B Bt
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum Bt, PrimeSpectrum.comap (algebraMap B Bt) q = p := by
    have : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B Bt)) := by
      rw [PrimeSpectrum.localization_away_comap_range Bt t]
      exact htp
    exact this
  have : Nontrivial Bt := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  have : Algebra.IsStandardSmooth R Bt := hstd.isStandardSmooth
  have : Module.Free Bt Ω[Bt⁄R] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have h1 := Module.rankAtStalk_baseChange (R := B) (S := Bt) (M := Ω[B⁄R]) q
  rw [hq] at h1
  rw [← h1, Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_eq_finrank_of_free]
  have hf : Module.finrank Bt Ω[Bt⁄R] = g := by
    rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := Bt) g]
    simp
  simp [hf]

/- English proof (translation)
Introduce `R _ A _ g hA hg`. Take `⟨hF, h0, -⟩` from `GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg`. Take `⟨hfin, hproj⟩` from `GlobalTheory.T.glob1_finite_and_projective R _ (OAff A.hom) hF h0`. Use `⟨hfin, hproj, fun p ↦ ?_⟩` and prove the remaining obligations. Establish `hη : (η[A]).left ≫ A.hom = 𝟙 _` using `by simpa using Over.w η[A]`.

Set `x : A.left` to `(η[A]).left.base p`. Establish `hxp : A.hom.base x = p`. Express the relevant statement in the definitionally equal form `((η[A]).left ≫ A.hom).base p = p`. Rewrite using `[hη]`. Both sides reduce to the same expression.

Choose the witnesses or unpack the hypotheses as in `⟨U, hU⟩ : ∃ U : A.left.affineOpens, x ∈ U.1 := by`. Take `⟨_, ⟨V, hV, rfl⟩, hxV, -⟩` from `A.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Conclude with `⟨⟨V, hV⟩, hxV⟩`. Set `T : AffOp A.left` to `Opposite.op U`. Set `B` to `(OAff A.hom).obj T`.

Establish `hUa : IsAffineOpen U.1` using `U.2`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ q : Sp (Sec A.hom U.1), (affPt A.hom U).base q = x := by`. Establish `: x ∈ Set.range hUa.fromSpec.base`. Rewrite using `[hUa.range_fromSpec]`. Conclude with `hU`.

Take `⟨q, hq⟩` from `this`. Conclude with `⟨q, hq⟩`. Establish `hqp : PrimeSpectrum.comap (algebraMap R (Sec A.hom U.1)) q = p`. Use `congrArg (fun f ↦ f.base q) (affPt_w A.hom U)` as an intermediate fact. Express the relevant statement in the definitionally equal form `A.hom.base ((affPt A.hom U).base q) = _ at this`.

Rewrite `this` using `[hq, hxp]`. Conclude with `this.symm`. Use `haveI : IsOpenImmersion (affPt A.hom U) := IsAffineOpen.isOpenImmersion_fromSpec hUa`. Take `⟨hloc, hsm⟩` from `smooth_of_openImm A.hom g hg (affPt A.hom U) (affPt_w A.hom U)`. Establish `hrk` using `rankAtStalk_kaehler_of_locally g hloc q`.

Set `e : Glob1 (OAff A.hom) →ₗ[R] Ω[B⁄R]` to `(LinearMap.proj T).comp (Glob1 (OAff A.hom)).subtype`. Establish `he : IsBaseChange B e` using `GlobalTheory.T.isBaseChange_compatibleGlobalOneForms R _ (OAff A.hom) hF h0 T e (fun _ ↦ rfl)`. Establish `h1` using `Module.rankAtStalk_baseChange (R := R) (M := Glob1 (OAff A.hom)) (S := B) q`. Rewrite `h1` using `[Module.rankAtStalk_eq_of_equiv he.equiv]`. Rewrite using `[← hqp]`.

Conclude with `h1.symm.trans hrk`.
-/
theorem globForm_FP : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → FP R (GlobForm A.hom) g := by
  intro R _ A _ g hA hg
  obtain ⟨hF, h0, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.glob1_finite_and_projective R _ (OAff A.hom) hF h0
  refine ⟨hfin, hproj, fun p ↦ ?_⟩

  have hη : (η[A]).left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  let x : A.left := (η[A]).left.base p
  have hxp : A.hom.base x = p := by
    change ((η[A]).left ≫ A.hom).base p = p
    rw [hη]; rfl
  obtain ⟨U, hU⟩ : ∃ U : A.left.affineOpens, x ∈ U.1 := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      isOpen_univ
    exact ⟨⟨V, hV⟩, hxV⟩
  let T : AffOp A.left := Opposite.op U
  let B := (OAff A.hom).obj T
  have hUa : IsAffineOpen U.1 := U.2
  obtain ⟨q, hq⟩ : ∃ q : Sp (Sec A.hom U.1), (affPt A.hom U).base q = x := by
    have : x ∈ Set.range hUa.fromSpec.base := by
      rw [hUa.range_fromSpec]; exact hU
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq⟩
  have hqp : PrimeSpectrum.comap (algebraMap R (Sec A.hom U.1)) q = p := by
    have := congrArg (fun f ↦ f.base q) (affPt_w A.hom U)
    change A.hom.base ((affPt A.hom U).base q) = _ at this
    rw [hq, hxp] at this
    exact this.symm
  haveI : IsOpenImmersion (affPt A.hom U) := IsAffineOpen.isOpenImmersion_fromSpec hUa
  obtain ⟨hloc, hsm⟩ := smooth_of_openImm A.hom g hg (affPt A.hom U) (affPt_w A.hom U)
  have hrk := rankAtStalk_kaehler_of_locally g hloc q
  let e : Glob1 (OAff A.hom) →ₗ[R] Ω[B⁄R] := (LinearMap.proj T).comp (Glob1 (OAff A.hom)).subtype
  have he : IsBaseChange B e := GlobalTheory.T.isBaseChange_compatibleGlobalOneForms R _ (OAff A.hom) hF h0 T e (fun _ ↦ rfl)
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := Glob1 (OAff A.hom)) (S := B) q
  rw [Module.rankAtStalk_eq_of_equiv he.equiv] at h1
  rw [← hqp]
  exact h1.symm.trans hrk

end GlobalTheory.AbCoh

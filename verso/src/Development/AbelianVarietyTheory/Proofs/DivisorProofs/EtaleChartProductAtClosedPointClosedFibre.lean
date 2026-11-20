import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDescendAlongProperMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFibreOfGeometricLiftingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLiftImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateMapEtaleNearProperFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleRestrictOfUniversallyClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackMorphismRestrictImageOfRestrictRestricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtChart

/- English proof (translation)
Set `P₀ : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty` to `{ __ := Algebra.Generators.mvPolynomial R (Fin n) relation := Empty.elim span_range_relation_eq_ker := by`. Rewrite using `[Algebra.Generators.ker_mvPolynomial]`. Simplify using `}`. Set `P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty` to `{ __ := P₀ map := Empty.elim map_inj := fun a => a.elim }`. Set `P₂ : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty` to `{ __ := P₁ jacobian_isUnit := by`.

Rewrite using `[Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]`. Simplify using `}`. Conclude with `P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])`.
-/
theorem mvPolynomial_stdSmooth (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  let P₀ : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := Algebra.Generators.mvPolynomial R (Fin n)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `: SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S)`. Use `smoothOfRelativeDimension_isStableUnderBaseChange.{0} n` as an intermediate fact. Use `MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ ?_` and prove the remaining obligations. Use `isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)` as an intermediate fact. Rewrite using `[← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)), MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension n), HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]`.

Use `RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_` and prove the remaining obligations. Conclude with `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2 (mvPolynomial_stdSmooth (ULift ℤ) n)`. Conclude with `SmoothOfRelativeDimension.smooth n _`.
-/
theorem affineSpace_smooth (S : Scheme.{0}) (n : ℕ) : Smooth (𝔸(Fin n; S) ↘ S) := by
  have : SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
    refine MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ ?_
    have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
      MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension n),
      HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2
      (mvPolynomial_stdSmooth (ULift ℤ) n)
  exact SmoothOfRelativeDimension.smooth n _

end GlobalTheory.Mum.EtChart

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ hR M G' _ _ hG E P' b X a hbsep hblft ha hsec hab hπΓ hπs x hx hx0 hinj hlift`. Use `haveI := hbsep`. Use `haveI := hblft`. Use `haveI := ha`. Use `haveI : IsProper M.π := M.proper`.

Use `haveI : IsProper (PSpace.str R E.N) := isProper_str R E.N`. Establish `key : a ≫ b ≫ PSpace.str R E.N = X.ι ≫ E.H.ι ≫ G'.hom ≫ M.π`. Rewrite using `[reassoc_of% hab, E.f_over]`. Take `⟨z, hz⟩` from `GlobalTheory.T.exists_mem_fiber_of_geometric_lifting R M.S P' X.toScheme M.π (b ≫ PSpace.str R E.N) a (X.ι ≫ E.H.ι ≫ G'.hom) hπs x hx0 hlift`. Establish `hz0 : M.π (G'.hom (E.H.ι (X.ι z))) = closedPoint R`.

Establish `h1` using `congrArg (fun f : X.toScheme ⟶ Sp R => f z) key`. Simplify using `only [Scheme.Hom.comp_apply] at h1`. Rewrite using `[← h1, hz]`. Simplify `hx0` using `[Scheme.Hom.comp_apply]`. Take `⟨y, hy⟩` from `(GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R M.S M.π G' E).1 (X.ι z) hz0`.

Establish `hyb : E.j y = b x`. Rewrite using `[← hy, ← hz]`. Establish `h1` using `congrArg (fun f : X.toScheme ⟶ PSpace R E.N => f z) hab`. Simplify `h1.symm` using `[Scheme.Hom.comp_apply]`. Take `⟨W0, g, τ0, O, e, hyO, hOW, hτ0, he, he2, he3⟩` from `GlobalTheory.T.exists_etale_coordinates_through_immersion R E.N E.Y E.smooth E.j E.imm E.j_over y`.

Establish `hxW1 : x ∈ b ⁻¹ᵁ W0` using `by show b x ∈ W0`. Rewrite using `[← hyb]`. Conclude with `hOW hyO`. Set `τ1 : (b ⁻¹ᵁ W0).toScheme ⟶ 𝔸(Fin g; Sp R)` to `(b ∣_ W0) ≫ τ0`. Establish `hτ1 : τ1 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = (b ⁻¹ᵁ W0).ι ≫ b ≫ PSpace.str R E.N`.

Simplify using `only [τ1, Category.assoc, hτ0, morphismRestrict_ι_assoc]`. Set `c1 : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π` to `pullback.lift ((a ∣_ (b ⁻¹ᵁ W0)) ≫ τ1) ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (by`. Rewrite using `[Category.assoc, hτ1, morphismRestrict_ι_assoc, key]`. Simplify using `only [Category.assoc])`. Establish `hF` using `GlobalTheory.T.coordinateMap_etale_near_properFibre R hR M G' hG E P' b X a hab x y hyb hx0 W0 g τ0 O e hyO hOW hτ0 he he2 he3 c1 (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)`.

Take `⟨W, hWW1, hxW, hWet⟩` from `GlobalTheory.T.exists_open_etale_restrict_of_universallyClosed' X.toScheme P' _ a (b ⁻¹ᵁ W0) c1 x inferInstance hxW1 hF`. Establish `hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ (b ⁻¹ᵁ W0)` using `fun _ hp => hWW1 hp`. Set `c` to `X.toScheme.homOfLE hle ≫ c1`. Set `τ` to `P'.homOfLE hWW1 ≫ τ1`. Set `U : Over (Sp R)` to `Over.mk (W.ι ≫ b ≫ PSpace.str R E.N)`.

Establish `hsq : X.toScheme.homOfLE hle ≫ (a ∣_ (b ⁻¹ᵁ W0)) = (a ∣_ W) ≫ P'.homOfLE hWW1`. Rewrite using `[← cancel_mono (b ⁻¹ᵁ W0).ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]`. Take `⟨x', hx'⟩ : x ∈ Set.range W.ι` from `by rw [Scheme.Opens.range_ι]; exact hxW`. Establish `hLFT : LocallyOfFiniteType U.hom` using `by show LocallyOfFiniteType (W.ι ≫ b ≫ PSpace.str R E.N); infer_instance`. Establish `hSep : IsSeparated U.hom` using `by show IsSeparated (W.ι ≫ b ≫ PSpace.str R E.N); infer_instance`.

Establish `hPr : IsProper (a ∣_ W)` using `inferInstance`. Establish `hSec : ∀ V : U.left.Opens, Function.Bijective ((a ∣_ W).app V).hom`. Introduce `V`. Rewrite using `[morphismRestrict_app]`. Conclude with `(ConcreteCategory.bijective_of_isIso (X.toScheme.presheaf.map (eqToHom (image_morphismRestrict_preimage a W V)).op)).comp (hsec (W.ι ''ᵁ V))`.

Establish `hτ : τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom`. Simplify using `only [τ, Category.assoc, hτ1]`. Rewrite using `[Scheme.homOfLE_ι_assoc]`. Both sides reduce to the same expression. Establish `hc1 : c ≫ pullback.fst _ _ = (a ∣_ W) ≫ τ`.

Simplify using `only [c, τ, c1, Category.assoc, pullback.lift_fst]`. Rewrite using `[← Category.assoc, hsq, Category.assoc]`. Establish `hc2 : c ≫ pullback.snd _ _ = (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom`. Simplify using `only [c, c1, Category.assoc, pullback.lift_snd]`. Rewrite using `[Scheme.homOfLE_ι_assoc]`.

Establish `hcl : IsClosed ({x'} : Set U.left)`. Establish `: ({x'} : Set U.left) = W.ι ⁻¹' {x}`. Use extensionality with `p`. Simplify using `only [Set.mem_singleton_iff, Set.mem_preimage]`. Conclude with `⟨fun h => h ▸ hx', fun h => W.ι.isOpenEmbedding.injective (h.trans hx'.symm)⟩`.

Rewrite using `[this]`. Conclude with `hx.preimage W.ι.continuous`. Establish `hx'0 : U.hom x' = closedPoint R` using `by show (W.ι ≫ b ≫ PSpace.str R E.N) x' = closedPoint R`. Simplify `hx0` using `[Scheme.Hom.comp_apply, hx']`. Establish `hrange : ∀ (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ U.left), Set.range ξ = {x'} → Set.range (ξ ≫ W.ι) = {x}`.

Introduce `Ω _ ξ hr`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]`. Use `erw [hr]`. Rewrite using `[Set.image_singleton, hx']`. Establish `hinj' : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ (a ⁻¹ᵁ W).toScheme), Set.range (p ≫ (a ∣_ W)) = {x'} → p ≫ (a ∣_ W) = p' ≫ (a ∣_ W) → p ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom → p = p'`.

Introduce `Ω _ p p' hr he hb`. Establish `hr' : Set.range ((p ≫ (a ⁻¹ᵁ W).ι) ≫ a) = {x}`. Rewrite using `[Category.assoc, ← morphismRestrict_ι, ← Category.assoc]`. Conclude with `hrange Ω _ hr`. Establish `h2 : (p ≫ (a ⁻¹ᵁ W).ι) ≫ a = (p' ≫ (a ⁻¹ᵁ W).ι) ≫ a`.

Simplify using `only [Category.assoc, ← morphismRestrict_ι]`. Rewrite using `[reassoc_of% he]`. Use `hinj Ω (p ≫ (a ⁻¹ᵁ W).ι) (p' ≫ (a ⁻¹ᵁ W).ι) hr' h2 (by simpa only [Category.assoc] using hb)` as an intermediate fact. Conclude with `(cancel_mono _).1 this`. Establish `hlift' : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ M.S), Set.range ξ = {x'} → ξ ≫ U.hom = s ≫ M.π → ∃ p : Sp Ω ⟶ (a ⁻¹ᵁ W).toScheme, p ≫ (a ∣_ W) = ξ ∧ p ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom = s`.

Introduce `Ω _ _ ξ s hr hs`. Take `⟨p, hp1, hp2⟩` from `hlift Ω (ξ ≫ W.ι) s (hrange Ω ξ hr) (by rw [Category.assoc]; exact hs)`. Establish `hsub : Set.range p.base ⊆ Set.range (a ⁻¹ᵁ W).ι.base`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨t, rfl⟩`.

Use `show a (p t) ∈ W`. Establish `h3 : a (p t) = W.ι (ξ t)`. Establish `h4` using `congrArg (fun f : Sp Ω ⟶ P' => f t) hp1`. Simplify `h4` using `[Scheme.Hom.comp_apply]`. Rewrite using `[h3]`.

Establish `h5` using `Set.mem_range_self (f := W.ι) (ξ t)`. Rewrite `h5` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis. Use `⟨IsOpenImmersion.lift (a ⁻¹ᵁ W).ι p hsub, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc, hp1]`. Rewrite using `[IsOpenImmersion.lift_fac_assoc]`.

Conclude with `hp2`. Take `⟨V, hxV, hVet, hVpb⟩` from `GlobalTheory.T.etaleCoordinates_descend_along_proper_map R hR M.S (a ⁻¹ᵁ W).toScheme M.π U (a ∣_ W) ((a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) g τ c M.proper hπs hπΓ hLFT hSep hPr hSec hτ hc1 hc2 (hWet hle) x' hcl hx'0 hinj' hlift'`. Use `⟨W.ι ''ᵁ V, ⟨x', hxV, hx'⟩, ?_, ?_⟩` and prove the remaining obligations. Use `haveI : Etale (V.ι ≫ τ) := hVet haveI : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := GlobalTheory.Mum.EtChart.affineSpace_smooth (Sp R) g`. Establish `e1 : (W.ι ''ᵁ V).ι ≫ b ≫ PSpace.str R E.N = (W.ι.isoImage V).inv ≫ (V.ι ≫ τ) ≫ (𝔸(Fin g; Sp R) ↘ Sp R)`.

Rewrite using `[Category.assoc, hτ, Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Use `infer_instance`. Conclude with `GlobalTheory.T.isPullback_restrict_image_of_restrict_restrict P' X.toScheme M.S (Sp R) a W V (X.ι ≫ E.H.ι ≫ G'.hom) (b ≫ PSpace.str R E.N) M.π hVpb`.
-/
theorem etale_chart_at_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), IsSeparated b → LocallyOfFiniteType b → IsProper a → (∀ V : P'.Opens, Function.Bijective (a.app V).hom) → a ≫ b = X.ι ≫ E.f → Function.Bijective M.π.appTop.hom → Surjective M.π → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X.toScheme), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ X.ι ≫ E.H.ι ≫ G'.hom → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s) → ∃ V : P'.Opens, x ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π := by
  intro R _ _ _ hR M G' _ _ hG E P' b X a hbsep hblft ha hsec hab hπΓ hπs x hx hx0 hinj hlift
  haveI := hbsep
  haveI := hblft
  haveI := ha
  haveI : IsProper M.π := M.proper
  haveI : IsProper (PSpace.str R E.N) := isProper_str R E.N
  have key : a ≫ b ≫ PSpace.str R E.N = X.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by
    rw [reassoc_of% hab, E.f_over]
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_mem_fiber_of_geometric_lifting R M.S P' X.toScheme M.π (b ≫ PSpace.str R E.N) a (X.ι ≫ E.H.ι ≫ G'.hom) hπs x hx0 hlift
  have hz0 : M.π (G'.hom (E.H.ι (X.ι z))) = closedPoint R := by
    have h1 := congrArg (fun f : X.toScheme ⟶ Sp R => f z) key
    simp only [Scheme.Hom.comp_apply] at h1
    rw [← h1, hz]
    simpa [Scheme.Hom.comp_apply] using hx0
  obtain ⟨y, hy⟩ := (GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R M.S M.π G' E).1 (X.ι z) hz0
  have hyb : E.j y = b x := by
    rw [← hy, ← hz]
    have h1 := congrArg (fun f : X.toScheme ⟶ PSpace R E.N => f z) hab
    simpa [Scheme.Hom.comp_apply] using h1.symm
  obtain ⟨W0, g, τ0, O, e, hyO, hOW, hτ0, he, he2, he3⟩ := GlobalTheory.T.exists_etale_coordinates_through_immersion R E.N E.Y E.smooth E.j E.imm E.j_over y
  have hxW1 : x ∈ b ⁻¹ᵁ W0 := by
    show b x ∈ W0
    rw [← hyb]; exact hOW hyO
  let τ1 : (b ⁻¹ᵁ W0).toScheme ⟶ 𝔸(Fin g; Sp R) := (b ∣_ W0) ≫ τ0
  have hτ1 : τ1 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = (b ⁻¹ᵁ W0).ι ≫ b ≫ PSpace.str R E.N := by
    simp only [τ1, Category.assoc, hτ0, morphismRestrict_ι_assoc]
  let c1 : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π :=
    pullback.lift ((a ∣_ (b ⁻¹ᵁ W0)) ≫ τ1) ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (by
      rw [Category.assoc, hτ1, morphismRestrict_ι_assoc, key]
      simp only [Category.assoc])
  have hF := GlobalTheory.T.coordinateMap_etale_near_properFibre R hR M G' hG E P' b X a hab x y hyb hx0 W0 g τ0 O e hyO hOW hτ0 he he2 he3 c1
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨W, hWW1, hxW, hWet⟩ := GlobalTheory.T.exists_open_etale_restrict_of_universallyClosed' X.toScheme P' _ a (b ⁻¹ᵁ W0) c1 x inferInstance hxW1 hF
  have hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ (b ⁻¹ᵁ W0) := fun _ hp => hWW1 hp
  let c := X.toScheme.homOfLE hle ≫ c1
  let τ := P'.homOfLE hWW1 ≫ τ1
  let U : Over (Sp R) := Over.mk (W.ι ≫ b ≫ PSpace.str R E.N)
  have hsq : X.toScheme.homOfLE hle ≫ (a ∣_ (b ⁻¹ᵁ W0)) = (a ∣_ W) ≫ P'.homOfLE hWW1 := by
    rw [← cancel_mono (b ⁻¹ᵁ W0).ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
      Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
  obtain ⟨x', hx'⟩ : x ∈ Set.range W.ι := by rw [Scheme.Opens.range_ι]; exact hxW
  have hLFT : LocallyOfFiniteType U.hom := by
    show LocallyOfFiniteType (W.ι ≫ b ≫ PSpace.str R E.N); infer_instance
  have hSep : IsSeparated U.hom := by
    show IsSeparated (W.ι ≫ b ≫ PSpace.str R E.N); infer_instance
  have hPr : IsProper (a ∣_ W) := inferInstance
  have hSec : ∀ V : U.left.Opens, Function.Bijective ((a ∣_ W).app V).hom := by
    intro V
    rw [morphismRestrict_app]
    exact (ConcreteCategory.bijective_of_isIso (X.toScheme.presheaf.map (eqToHom (image_morphismRestrict_preimage a W V)).op)).comp (hsec (W.ι ''ᵁ V))
  have hτ : τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom := by
    simp only [τ, Category.assoc, hτ1]
    rw [Scheme.homOfLE_ι_assoc]
    rfl
  have hc1 : c ≫ pullback.fst _ _ = (a ∣_ W) ≫ τ := by
    simp only [c, τ, c1, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, hsq, Category.assoc]
  have hc2 : c ≫ pullback.snd _ _ = (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom := by
    simp only [c, c1, Category.assoc, pullback.lift_snd]
    rw [Scheme.homOfLE_ι_assoc]
  have hcl : IsClosed ({x'} : Set U.left) := by
    have : ({x'} : Set U.left) = W.ι ⁻¹' {x} := by
      ext p
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hx', fun h => W.ι.isOpenEmbedding.injective (h.trans hx'.symm)⟩
    rw [this]
    exact hx.preimage W.ι.continuous
  have hx'0 : U.hom x' = closedPoint R := by
    show (W.ι ≫ b ≫ PSpace.str R E.N) x' = closedPoint R
    simpa [Scheme.Hom.comp_apply, hx'] using hx0
  have hrange : ∀ (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ U.left), Set.range ξ = {x'} → Set.range (ξ ≫ W.ι) = {x} := by
    intro Ω _ ξ hr
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    erw [hr]
    rw [Set.image_singleton, hx']
  have hinj' : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ (a ⁻¹ᵁ W).toScheme), Set.range (p ≫ (a ∣_ W)) = {x'} →
      p ≫ (a ∣_ W) = p' ≫ (a ∣_ W) → p ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom →
      p = p' := by
    intro Ω _ p p' hr he hb
    have hr' : Set.range ((p ≫ (a ⁻¹ᵁ W).ι) ≫ a) = {x} := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc]
      exact hrange Ω _ hr
    have h2 : (p ≫ (a ⁻¹ᵁ W).ι) ≫ a = (p' ≫ (a ⁻¹ᵁ W).ι) ≫ a := by
      simp only [Category.assoc, ← morphismRestrict_ι]
      rw [reassoc_of% he]
    have := hinj Ω (p ≫ (a ⁻¹ᵁ W).ι) (p' ≫ (a ⁻¹ᵁ W).ι) hr' h2 (by simpa only [Category.assoc] using hb)
    exact (cancel_mono _).1 this
  have hlift' : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ M.S), Set.range ξ = {x'} →
      ξ ≫ U.hom = s ≫ M.π → ∃ p : Sp Ω ⟶ (a ⁻¹ᵁ W).toScheme, p ≫ (a ∣_ W) = ξ ∧ p ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
    intro Ω _ _ ξ s hr hs
    obtain ⟨p, hp1, hp2⟩ := hlift Ω (ξ ≫ W.ι) s (hrange Ω ξ hr) (by rw [Category.assoc]; exact hs)
    have hsub : Set.range p.base ⊆ Set.range (a ⁻¹ᵁ W).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      show a (p t) ∈ W
      have h3 : a (p t) = W.ι (ξ t) := by
        have h4 := congrArg (fun f : Sp Ω ⟶ P' => f t) hp1
        simpa [Scheme.Hom.comp_apply] using h4
      rw [h3]
      have h5 := Set.mem_range_self (f := W.ι) (ξ t)
      rwa [Scheme.Opens.range_ι] at h5
    refine ⟨IsOpenImmersion.lift (a ⁻¹ᵁ W).ι p hsub, ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc, hp1]
    · rw [IsOpenImmersion.lift_fac_assoc]; exact hp2
  obtain ⟨V, hxV, hVet, hVpb⟩ := GlobalTheory.T.etaleCoordinates_descend_along_proper_map R hR M.S (a ⁻¹ᵁ W).toScheme M.π U (a ∣_ W)
    ((a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) g τ c M.proper hπs hπΓ hLFT hSep hPr hSec hτ hc1 hc2 (hWet hle)
    x' hcl hx'0 hinj' hlift'
  refine ⟨W.ι ''ᵁ V, ⟨x', hxV, hx'⟩, ?_, ?_⟩
  · haveI : Etale (V.ι ≫ τ) := hVet
    haveI : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := GlobalTheory.Mum.EtChart.affineSpace_smooth (Sp R) g
    have e1 : (W.ι ''ᵁ V).ι ≫ b ≫ PSpace.str R E.N =
        (W.ι.isoImage V).inv ≫ (V.ι ≫ τ) ≫ (𝔸(Fin g; Sp R) ↘ Sp R) := by
      rw [Category.assoc, hτ, Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc]
      rfl
    rw [e1]
    infer_instance
  · exact GlobalTheory.T.isPullback_restrict_image_of_restrict_restrict P' X.toScheme M.S (Sp R) a W V (X.ι ≫ E.H.ι ≫ G'.hom) (b ≫ PSpace.str R E.N) M.π hVpb

end GlobalTheory.Mum

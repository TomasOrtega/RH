import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DomBy
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NotIsGenericFlagSelf
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Set `φ : X.presheaf.stalk q.1 →+* W` to `(i.comp (genMap ξ q)).codRestrict W.toSubring (fun a => h1 _ ⟨a, rfl⟩)`. Establish `hφ : ∀ a, ((φ a : W) : Ω') = i (genMap ξ q a)` using `fun _ => rfl`. Establish `hloc : IsLocalHom φ`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations.

Establish `hne : genMap ξ q a ≠ 0`. Introduce `h0`. Establish `: φ a = 0` using `Subtype.ext (by rw [hφ, h0, map_zero]; rfl)`. Rewrite `ha` using `[this]`. Conclude with `not_isUnit_zero ha`.

Establish `hinv : (i (genMap ξ q a))⁻¹ ∈ W.toSubring`. Take `⟨b, hb⟩` from `ha.exists_right_inv`. Establish `hb' : i (genMap ξ q a) * (b : Ω') = 1`. Use `congrArg (fun x : W => (x : Ω')) hb` as an intermediate fact. Simplify `this` using `[hφ]`.

Rewrite using `[inv_eq_of_mul_eq_one_right hb']`. Conclude with `b.2`. Take `⟨b, hb⟩` from `h2 _ ⟨a, rfl⟩ hne hinv`. Use `IsUnit.of_mul_eq_one b (hinj ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hb, map_one, mul_inv_cancel₀ hne]`.

Set `z : Sp W ⟶ X` to `Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk q.1`. Use `⟨z, ?_, ?_⟩` and prove the remaining obligations. Establish `e : CommRingCat.ofHom φ ≫ CommRingCat.ofHom W.subtype = X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i`. Use extensionality with `a`. Both sides reduce to the same expression.

Establish `e2 : spMap W.subtype ≫ Spec.map (CommRingCat.ofHom φ) = spMap i ≫ Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2)`. Simplify using `only [spMap, ← Spec.map_comp]`. Rewrite using `[e]`. Both sides reduce to the same expression. Use `show spMap W.subtype ≫ Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk q.1 = _`.

Rewrite using `[← Category.assoc, e2]`. Simplify using `only [Category.assoc]`. Establish `e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ)` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2`. Establish `e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ`. Establish `e5 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = ξ` using `(congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4`.

Conclude with `congrArg (spMap i ≫ ·) e5`. Establish `: IsLocalHom (CommRingCat.ofHom φ).hom` using `hloc`. Express the relevant statement in the definitionally equal form `X.fromSpecStalk q.1 (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint W)) = q.1`. Rewrite using `[Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]`.
-/
theorem exists_valPoint {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X)
    (W : ValuationSubring Ω') (i : Ω →+* Ω') (q : Cpt ξ) (hinj : Function.Injective (genMap ξ q))
    (h : DomBy W.toSubring i ξ q) :
    ∃ z : Sp W ⟶ X, spMap W.subtype ≫ z = spMap i ≫ ξ ∧ z (IsLocalRing.closedPoint W) = q.1 := by
  obtain ⟨h1, h2⟩ := h
  let φ : X.presheaf.stalk q.1 →+* W :=
    (i.comp (genMap ξ q)).codRestrict W.toSubring (fun a => h1 _ ⟨a, rfl⟩)
  have hφ : ∀ a, ((φ a : W) : Ω') = i (genMap ξ q a) := fun _ => rfl
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    have hne : genMap ξ q a ≠ 0 := by
      intro h0
      have : φ a = 0 := Subtype.ext (by rw [hφ, h0, map_zero]; rfl)
      rw [this] at ha
      exact not_isUnit_zero ha
    have hinv : (i (genMap ξ q a))⁻¹ ∈ W.toSubring := by
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hb' : i (genMap ξ q a) * (b : Ω') = 1 := by
        have := congrArg (fun x : W => (x : Ω')) hb
        simpa [hφ] using this
      rw [inv_eq_of_mul_eq_one_right hb']
      exact b.2
    obtain ⟨b, hb⟩ := h2 _ ⟨a, rfl⟩ hne hinv
    refine IsUnit.of_mul_eq_one b (hinj ?_)
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  let z : Sp W ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk q.1
  refine ⟨z, ?_, ?_⟩
  · have e : CommRingCat.ofHom φ ≫ CommRingCat.ofHom W.subtype =
        X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
      ext a
      rfl
    have e2 : spMap W.subtype ≫ Spec.map (CommRingCat.ofHom φ) =
        spMap i ≫ Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) := by
      simp only [spMap, ← Spec.map_comp]
      rw [e]
      rfl
    show spMap W.subtype ≫ Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk q.1 = _
    rw [← Category.assoc, e2]
    simp only [Category.assoc]
    have e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2
    have e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have e5 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) ≫
        X.fromSpecStalk q.1 = ξ :=
      (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4
    exact congrArg (spMap i ≫ ·) e5
  · have : IsLocalHom (CommRingCat.ofHom φ).hom := hloc
    change X.fromSpecStalk q.1 (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint W)) = q.1
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/- English proof (translation)
Take `⟨N, i, hi, rfl⟩` from `h`. Establish `: IsSeparated (PSpace.str R N)`. Unfold `PSpace.str`. Use `infer_instance`. Use `infer_instance`.
-/
theorem isSeparated_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsSeparated (PSpace.str R N) := by
    unfold PSpace.str
    infer_instance
  infer_instance

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i hξ W q q₀ hq hq₀`. Take `⟨z, hz, hzc⟩` from `exists_valPoint 𝔐.ξ W (RingHom.id Ω) q (𝔐.tie.gen.inj q) hq`. Take `⟨z₀, hz₀, hzc₀⟩` from `exists_valPoint 𝔐₀.ξ W i q₀ (𝔐₀.tie.gen.inj q₀) hq₀`. Establish `hsep : IsSeparated Y.s` using `isSeparated_of_isProjOver' Y.proj`. Establish `hinj : Function.Injective W.subtype` using `Subtype.val_injective`.

Establish `hdom : IsDominant (spMap W.subtype)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]`. Conclude with `bot_le)⟩`. Establish `hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐₀.f`. Rewrite using `[← Category.assoc, hz, ← Category.assoc, hz₀]`.

Establish `: spMap (RingHom.id Ω) = 𝟙 _` using `by simp [spMap]`. Rewrite using `[this, Category.id_comp, hξ]`. Simplify using `only [Category.assoc]`. Establish `hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐₀.f) ≫ Y.s`. Establish `hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F)))` using `inferInstance`.

Use `ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F))) (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_` and prove the remaining obligations. Simplify using `only [← Category.assoc] at hgen ⊢`. Rewrite using `[hgen]`. Establish `heq : z ≫ 𝔐.f = z₀ ≫ 𝔐₀.f` using `ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen`. Use `congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq` as an intermediate fact.

Express the relevant statement in the definitionally equal form `𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐₀.f (z₀ (IsLocalRing.closedPoint W)) at this`. Rewrite `this` using `[hzc, hzc₀]`. Then use the resulting hypothesis.
-/
theorem image_eq_of_domBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∀ (W : ValuationSubring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), DomBy W.toSubring (RingHom.id Ω) 𝔐.ξ q → DomBy W.toSubring i 𝔐₀.ξ q₀ → 𝔐.f q.1 = 𝔐₀.f q₀.1 := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i hξ W q q₀ hq hq₀
  obtain ⟨z, hz, hzc⟩ := exists_valPoint 𝔐.ξ W (RingHom.id Ω) q (𝔐.tie.gen.inj q) hq
  obtain ⟨z₀, hz₀, hzc₀⟩ := exists_valPoint 𝔐₀.ξ W i q₀ (𝔐₀.tie.gen.inj q₀) hq₀
  have hsep : IsSeparated Y.s := isSeparated_of_isProjOver' Y.proj
  have hinj : Function.Injective W.subtype := Subtype.val_injective
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]; exact bot_le)⟩
  have hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐₀.f := by
    rw [← Category.assoc, hz, ← Category.assoc, hz₀]
    have : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
    rw [this, Category.id_comp, hξ]
    simp only [Category.assoc]
  have hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐₀.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have heq : z ≫ 𝔐.f = z₀ ≫ 𝔐₀.f :=
    ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen
  have := congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq
  change 𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐₀.f (z₀ (IsLocalRing.closedPoint W)) at this
  rwa [hzc, hzc₀] at this

end GlobalTheory.CompanionTheory.Ar.OrVert

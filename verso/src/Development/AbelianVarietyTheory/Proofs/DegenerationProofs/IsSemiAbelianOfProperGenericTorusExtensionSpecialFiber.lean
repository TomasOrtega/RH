import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

/- English proof (translation)
Use `IsPullback.of_bot (h₃₁ := f) (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) ?_ ?_ (IsPullback.of_hasPullback Y.hom f)` and prove the remaining obligations. Establish `h₁ : ((Over.pullback f).map q).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f` using `Over.w ((Over.pullback f).map q)`. Establish `h₂ : q.left ≫ Y.hom = X.hom` using `Over.w q`. Rewrite using `[h₁, h₂]`. Conclude with `IsPullback.of_hasPullback X.hom f`.

Conclude with `(pullback.lift_fst _ _ _).symm`.
-/
theorem isPullback_overPullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (q : X ⟶ Y) :
    IsPullback (pullback.fst X.hom f) ((Over.pullback f).map q).left q.left (pullback.fst Y.hom f) := by
  refine IsPullback.of_bot (h₃₁ := f) (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) ?_ ?_
    (IsPullback.of_hasPullback Y.hom f)
  · have h₁ : ((Over.pullback f).map q).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f :=
      Over.w ((Over.pullback f).map q)
    have h₂ : q.left ≫ Y.hom = X.hom := Over.w q
    rw [h₁, h₂]
    exact IsPullback.of_hasPullback X.hom f
  · exact (pullback.lift_fst _ _ _).symm

/- English proof (translation)
Take `⟨T⟩` from `h`. Use `letI := T.grpB`. Use `letI := T.addCommGroup`. Use `haveI := T.q_hom`. Use `haveI := T.i_hom`.

Take `⟨e, he, -⟩` from `GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X`. Establish `hq` using `isPullback_overPullback_map_left f T.q`. Use `⟨{ X := T.X addCommGroup := T.addCommGroup free := T.free finite := T.finite B := (Over.pullback f).obj T.B grpB := inferInstance isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian q := (Over.pullback f).map T.q q_hom := inferInstance q_flat := MorphismPrope …` and prove the remaining obligations. Establish `hk` using `T.isKernel.map (Over.pullback f)`. Use `IsPullback.of_iso hk e.symm (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Conclude with `toUnit_unique _ _`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem nonempty_torusExtension_pullback {k Ω : Type} [Field k] [Field Ω] (f : Sp Ω ⟶ Sp k)
    (G : Over (Sp k)) [GrpObj G] (h : Nonempty (TorusExtension G)) :
    Nonempty (TorusExtension ((Over.pullback f).obj G)) := by
  obtain ⟨T⟩ := h
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X
  have hq := isPullback_overPullback_map_left f T.q
  refine ⟨{ X := T.X
            addCommGroup := T.addCommGroup
            free := T.free
            finite := T.finite
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.hom ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }⟩
  have hk := T.isKernel.map (Over.pullback f)
  refine IsPullback.of_iso hk e.symm (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact toUnit_unique _ _
  · simp
  · simp

/- English proof (translation)
Set `ρ' : IsLocalRing.ResidueField W →+* k` to `Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) ρ fun a ha => (RingHom.mem_ker).1 (hρ ▸ ha)`. Set `φ' : IsLocalRing.ResidueField W →+* Ω` to `Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ fun a ha => (RingHom.mem_ker).1 (hφ ▸ ha)`. Use `letI := ρ'.toAlgebra`. Use `letI := φ'.toAlgebra`. Establish `hi' : ρ'.IsIntegral` using `RingHom.IsIntegral.tower_top (IsLocalRing.residue W) ρ' hi`.

Use `haveI : Algebra.IsIntegral (IsLocalRing.ResidueField W) k := ⟨hi'⟩`. Set `ψ : k →ₐ[IsLocalRing.ResidueField W] Ω` to `IsAlgClosed.lift`. Use `⟨ψ.toRingHom, RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Conclude with `ψ.commutes (IsLocalRing.residue W x)`.
-/
theorem exists_ringHom_comp_eq_of_isIntegral {W k Ω : Type} [CommRing W] [IsLocalRing W] [Field k] [Field Ω]
    [IsAlgClosed Ω] (ρ : W →+* k) (hρ : RingHom.ker ρ = IsLocalRing.maximalIdeal W) (hi : ρ.IsIntegral)
    (φ : W →+* Ω) (hφ : RingHom.ker φ = IsLocalRing.maximalIdeal W) : ∃ ψ : k →+* Ω, ψ.comp ρ = φ := by
  let ρ' : IsLocalRing.ResidueField W →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) ρ fun a ha => (RingHom.mem_ker).1 (hρ ▸ ha)
  let φ' : IsLocalRing.ResidueField W →+* Ω :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ fun a ha => (RingHom.mem_ker).1 (hφ ▸ ha)
  letI := ρ'.toAlgebra
  letI := φ'.toAlgebra
  have hi' : ρ'.IsIntegral := RingHom.IsIntegral.tower_top (IsLocalRing.residue W) ρ' hi
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField W) k := ⟨hi'⟩
  let ψ : k →ₐ[IsLocalRing.ResidueField W] Ω := IsAlgClosed.lift
  refine ⟨ψ.toRingHom, RingHom.ext fun x => ?_⟩
  exact ψ.commutes (IsLocalRing.residue W x)

/- English proof (translation)
Introduce `W L _ _ _ _ _ _ G _ hG hp k _ ρ hρ hi hT`. Take `⟨hc, hs, hsep, hqc, hgc⟩` from `hG`. Establish `key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω), Nonempty (TorusExtension ((Over.pullback (spMap a)).obj G)) → Nonempty (TorusExtension ((Over.pullback (spMap (ψ.comp a))).obj G))`. Introduce `Ω F _ _ a ψ h`. Take `⟨E⟩` from `nonempty_torusExtension_pullback (spMap ψ) _ h`.

Establish `e : spMap (ψ.comp a) = spMap ψ ≫ spMap a`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Rewrite using `[e]`. Establish `: IsMonHom (pullCompIso (spMap ψ) (spMap a) G).symm.hom` using `inferInstanceAs (IsMonHom (pullCompIso (spMap ψ) (spMap a) G).inv)`. Conclude with `⟨torusExtOfIso (pullCompIso (spMap ψ) (spMap a) G).symm E⟩`.

Establish `hA : IsAbelianScheme ((Over.pullback (spMap (algebraMap W L))).obj G)` using `{ comm := inferInstance smooth := by change Smooth (pullback.snd G.hom _); infer_instance proper := hp geomConnected := by change GeometricallyConnected (pullback.snd G.hom _); infer_instance }`. Use `⟨hc, hs, hsep, hqc, hgc, fun Ω _ _ q => ?_⟩` and prove the remaining obligations. Take `⟨φ, rfl⟩` from `Spec.map_surjective q`. Express the relevant statement in the definitionally equal form `Nonempty (TorusExtension ((Over.pullback (spMap φ.hom)).obj G))`. Distinguish the cases in `h : RingHom.ker φ.hom = ⊥`.

Establish `hinj` using `(RingHom.injective_iff_ker_eq_bot _).2 h`. Establish `e : (IsFractionRing.lift (K` using `L) hinj).comp (algebraMap W L) = φ.hom := RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x`. Rewrite using `[← e]`. Conclude with `key Ω L _ _ ⟨GlobalTheory.torusExtensionOfAbelian _ hA⟩`. Establish `hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W` using `IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)`.

Take `⟨ψ, e⟩` from `exists_ringHom_comp_eq_of_isIntegral ρ hρ hi φ.hom hm`. Rewrite using `[← e]`. Conclude with `key Ω k _ _ hT`.
-/
theorem isSemiAbelian_of_proper_generic_of_torusExtension : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ (k : Type) [Field k] (ρ : W →+* k), RingHom.ker ρ = IsLocalRing.maximalIdeal W → ρ.IsIntegral → Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj G)) → IsSemiAbelian G := by
  intro W L _ _ _ _ _ _ G _ hG hp k _ ρ hρ hi hT
  obtain ⟨hc, hs, hsep, hqc, hgc⟩ := hG
  have key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω),
      Nonempty (TorusExtension ((Over.pullback (spMap a)).obj G)) →
      Nonempty (TorusExtension ((Over.pullback (spMap (ψ.comp a))).obj G)) := by
    intro Ω F _ _ a ψ h
    obtain ⟨E⟩ := nonempty_torusExtension_pullback (spMap ψ) _ h
    have e : spMap (ψ.comp a) = spMap ψ ≫ spMap a := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e]
    have : IsMonHom (pullCompIso (spMap ψ) (spMap a) G).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso (spMap ψ) (spMap a) G).inv)
    exact ⟨torusExtOfIso (pullCompIso (spMap ψ) (spMap a) G).symm E⟩
  have hA : IsAbelianScheme ((Over.pullback (spMap (algebraMap W L))).obj G) :=
    { comm := inferInstance
      smooth := by change Smooth (pullback.snd G.hom _); infer_instance
      proper := hp
      geomConnected := by change GeometricallyConnected (pullback.snd G.hom _); infer_instance }
  refine ⟨hc, hs, hsep, hqc, hgc, fun Ω _ _ q => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  change Nonempty (TorusExtension ((Over.pullback (spMap φ.hom)).obj G))
  by_cases h : RingHom.ker φ.hom = ⊥
  · have hinj := (RingHom.injective_iff_ker_eq_bot _).2 h
    have e : (IsFractionRing.lift (K := L) hinj).comp (algebraMap W L) = φ.hom :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    rw [← e]
    exact key Ω L _ _ ⟨GlobalTheory.torusExtensionOfAbelian _ hA⟩
  · have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)
    obtain ⟨ψ, e⟩ := exists_ringHom_comp_eq_of_isIntegral ρ hρ hi φ.hom hm
    rw [← e]
    exact key Ω k _ _ hT

end GlobalTheory.SS

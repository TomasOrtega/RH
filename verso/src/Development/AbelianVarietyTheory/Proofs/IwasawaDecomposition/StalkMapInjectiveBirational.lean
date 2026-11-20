import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericStalkPointInInteriorStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ChartBir

/- English proof (translation)
Establish `hb : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F))` using `IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 c.F)) (S := c.F) (nonZeroDivisors (𝓞 c.F))`. Establish `hbf : Flat (spMap (algebraMap (𝓞 c.F) c.F))`. Rewrite using `[Flat.SpecMap_iff]`. Conclude with `RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F)))`. Establish `h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)))` using `MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb`.

Establish `h2 : Flat (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)))` using `MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip hbf`. Use `haveI := Y.jQ_open`. Establish `i1 : IsIso ((pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).stalkMap (Y.jQ u))` using `GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ _`. Establish `i2 : IsIso (Y.jQ.stalkMap u)` using `(IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 u`. Use `show IsIso ((Y.jQ ≫ pullback.fst _ _).stalkMap u)`.

Rewrite using `[Scheme.Hom.stalkMap_comp]`. Conclude with `@IsIso.comp_isIso _ _ _ _ _ _ _ i1 i2`.
-/
theorem isIso_stalkMap_j {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : GMod Xo c) (u : Xo.XF c) : IsIso (Y.j.stalkMap u) := by
  have hb : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 c.F)) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  have hbf : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F)))
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have h2 : Flat (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip hbf
  haveI := Y.jQ_open
  have i1 : IsIso ((pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).stalkMap (Y.jQ u)) :=
    GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ _
  have i2 : IsIso (Y.jQ.stalkMap u) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 u
  show IsIso ((Y.jQ ≫ pullback.fst _ _).stalkMap u)
  rw [Scheme.Hom.stalkMap_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ i1 i2

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c X Z π hj _ z`. Take `⟨hBd, -⟩` from `Z.normal z`. Take `⟨hAd, -⟩` from `X.normal (π z)`. Set `p0 : PrimeSpectrum (Z.X.presheaf.stalk z)` to `⟨⊥, Ideal.bot_prime⟩`. Take `⟨w, hw⟩` from `GlobalTheory.T.generic_stalk_point_in_interior E H D l Xo c Z z p0 rfl`.

Establish `hy : Z.j w ⤳ z`. Establish `hm : Z.X.fromSpecStalk z p0 ∈ Set.range (Z.X.fromSpecStalk z)` using `⟨p0, rfl⟩`. Rewrite `hm` using `[Scheme.range_fromSpecStalk]`. Rewrite using `[hw]`. Conclude with `hm`.

Establish `hg : IsIso (π.stalkMap (Z.j w))`. Establish `h1 : IsIso ((Z.j ≫ π).stalkMap w)` using `by rw [hj]; exact isIso_stalkMap_j X w`. Rewrite `h1` using `[Scheme.Hom.stalkMap_comp]`. Conclude with `@IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (isIso_stalkMap_j Z w) h1`. Establish `hgb` using `(ConcreteCategory.isIso_iff_bijective (π.stalkMap (Z.j w))).1 hg`.

Establish `hπy : π (Z.j w) ⤳ π z` using `hy.map π.continuous`. Establish `sq : ∀ a : X.X.presheaf.stalk (π z), (Z.X.presheaf.stalkSpecializes hy).hom ((π.stalkMap z).hom a) = (π.stalkMap (Z.j w)).hom ((X.X.presheaf.stalkSpecializes hπy).hom a)` using `fun a => (Scheme.Hom.stalkSpecializes_stalkMap_apply π (Z.j w) z hy a).symm`. Establish `hσ` using `GlobalTheory.PushInv.stalkSpecializes_injective (X := Z.X) hy`. Establish `hτ` using `GlobalTheory.PushInv.stalkSpecializes_injective (X := X.X) hπy`. Establish `hinj : Function.Injective (π.stalkMap z).hom`.

Use `(injective_iff_map_eq_zero _).2 fun a ha => hτ ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Apply `hgb.1` to reduce the goal to its premises. Rewrite using `[← sq, ha, map_zero, map_zero]`. Use `⟨hinj, fun b => ?_⟩` and prove the remaining obligations.

Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X.X) (U := ⊤) (x := π z) trivial`. Establish `hyU : π (Z.j w) ∈ U` using `hπy.mem_open U.2 hxU`. Take `⟨κ, hκ⟩` from `hgb.2 ((Z.X.presheaf.stalkSpecializes hy).hom b)`. Take `⟨r, t, ht, e⟩` from `GlobalTheory.PushInv.exists_frac hU hyU κ`. Establish `er` using `GlobalTheory.PushInv.gs_specializes (𝟙 X.X) hπy U hxU r`.

Establish `et` using `GlobalTheory.PushInv.gs_specializes (𝟙 X.X) hπy U hxU t`. Use `⟨gs (𝟙 X.X) (π z) U r, gs (𝟙 X.X) (π z) U t, fun h0 => ?_, hσ ?_⟩` and prove the remaining obligations. Establish `h0'` using `hinj (h0.trans (map_zero _).symm)`. Rewrite `et` using `[h0', map_zero]`. Rewrite `ht` using `[← et]`.

Conclude with `not_isUnit_zero ht`. Rewrite using `[map_mul, sq, sq, et, er, ← e, map_mul, hκ, mul_comm]`.
-/
theorem stalkMap_birational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s →
    ∀ z : Z.X, Function.Injective (π.stalkMap z).hom ∧ ∀ b : Z.X.presheaf.stalk z, ∃ a s : X.X.presheaf.stalk (π z),
      (π.stalkMap z).hom s ≠ 0 ∧ (π.stalkMap z).hom s * b = (π.stalkMap z).hom a := by
  intro E _ _ _ H D l Xo c X Z π hj _ z
  obtain ⟨hBd, -⟩ := Z.normal z
  obtain ⟨hAd, -⟩ := X.normal (π z)
  let p0 : PrimeSpectrum (Z.X.presheaf.stalk z) := ⟨⊥, Ideal.bot_prime⟩
  obtain ⟨w, hw⟩ := GlobalTheory.T.generic_stalk_point_in_interior E H D l Xo c Z z p0 rfl
  have hy : Z.j w ⤳ z := by
    have hm : Z.X.fromSpecStalk z p0 ∈ Set.range (Z.X.fromSpecStalk z) := ⟨p0, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hm
    rw [hw]; exact hm

  have hg : IsIso (π.stalkMap (Z.j w)) := by
    have h1 : IsIso ((Z.j ≫ π).stalkMap w) := by rw [hj]; exact isIso_stalkMap_j X w
    rw [Scheme.Hom.stalkMap_comp] at h1
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (isIso_stalkMap_j Z w) h1
  have hgb := (ConcreteCategory.isIso_iff_bijective (π.stalkMap (Z.j w))).1 hg
  have hπy : π (Z.j w) ⤳ π z := hy.map π.continuous

  have sq : ∀ a : X.X.presheaf.stalk (π z), (Z.X.presheaf.stalkSpecializes hy).hom ((π.stalkMap z).hom a) =
      (π.stalkMap (Z.j w)).hom ((X.X.presheaf.stalkSpecializes hπy).hom a) := fun a =>
    (Scheme.Hom.stalkSpecializes_stalkMap_apply π (Z.j w) z hy a).symm
  have hσ := GlobalTheory.PushInv.stalkSpecializes_injective (X := Z.X) hy
  have hτ := GlobalTheory.PushInv.stalkSpecializes_injective (X := X.X) hπy
  have hinj : Function.Injective (π.stalkMap z).hom := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => hτ ?_
    rw [map_zero]
    apply hgb.1
    rw [← sq, ha, map_zero, map_zero]
  refine ⟨hinj, fun b => ?_⟩
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X.X) (U := ⊤) (x := π z) trivial
  have hyU : π (Z.j w) ∈ U := hπy.mem_open U.2 hxU
  obtain ⟨κ, hκ⟩ := hgb.2 ((Z.X.presheaf.stalkSpecializes hy).hom b)
  obtain ⟨r, t, ht, e⟩ := GlobalTheory.PushInv.exists_frac hU hyU κ
  have er := GlobalTheory.PushInv.gs_specializes (𝟙 X.X) hπy U hxU r
  have et := GlobalTheory.PushInv.gs_specializes (𝟙 X.X) hπy U hxU t
  refine ⟨gs (𝟙 X.X) (π z) U r, gs (𝟙 X.X) (π z) U t, fun h0 => ?_, hσ ?_⟩
  · have h0' := hinj (h0.trans (map_zero _).symm)
    rw [h0', map_zero] at et
    rw [← et] at ht
    exact not_isUnit_zero ht
  · rw [map_mul, sq, sq, et, er, ← e, map_mul, hκ, mul_comm]

end GlobalTheory.ChartBir

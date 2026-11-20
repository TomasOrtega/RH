import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace GlobalTheory.CompanionTheory.Ar.HT

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O C)` using `hv.hom_inj`. Use `haveI : IsDomain O := hinj.isDomain`. Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Set `f : L →ₗ[O] (V ⧸ U)` to `(U.mkQ.restrictScalars O).comp L.subtype`. Use `haveI : Module.Finite O L := Module.Finite.iff_fg.2 hL`.

Use `haveI : Module.Finite O (LinearMap.range f) := inferInstance`. Use `haveI : Module.Flat O (LinearMap.range f) := by`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce and unpack `⟨x, hx⟩ ⟨⟨a, ha⟩, h⟩`. Establish `h1 : a • x = 0` using `congrArg Subtype.val h`.

Establish `ha0 : algebraMap O C a ≠ 0`. Introduce `h0`. Conclude with `nonZeroDivisors.ne_zero ha (hinj (by simpa using h0))`. Rewrite `h1` using `[← algebraMap_smul C a x]`. Establish `: x = 0` using `(smul_eq_zero.1 h1).resolve_left ha0`.

Simplify using `[this]`. Use `haveI : Module.Free O (LinearMap.range f) := Module.free_of_flat_of_isLocalRing`. Take `⟨s, hs⟩` from `Module.projective_lifting_property f.rangeRestrict LinearMap.id f.surjective_rangeRestrict`. Set `p : L →ₗ[O] V` to `L.subtype.comp (LinearMap.id - s.comp f.rangeRestrict)`. Establish `key : L ⊓ U.restrictScalars O = LinearMap.range p`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨hxL, hxU⟩`. Use `⟨⟨x, hxL⟩, ?_⟩` and prove the remaining obligations. Establish `: f.rangeRestrict ⟨x, hxL⟩ = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `U.mkQ x = 0`. Conclude with `(Submodule.Quotient.mk_eq_zero U).2 hxU`. Simplify using `[p, this]`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `⟨(y - s (f.rangeRestrict y)).2, ?_⟩` and prove the remaining obligations.

Establish `h2 : f.rangeRestrict (s (f.rangeRestrict y)) = f.rangeRestrict y` using `LinearMap.congr_fun hs _`. Establish `h3 : f (y - s (f.rangeRestrict y)) = 0`. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `(congrArg Subtype.val h2).symm`. Conclude with `(Submodule.Quotient.mk_eq_zero U).1 h3`.

Rewrite using `[key]`. Conclude with `Module.Finite.iff_fg.1 inferInstance`.
-/
theorem fg_inf_restrictScalars_of_integers (C : Type) [Field C] (v : Valuation C NNReal) (O : Type)
    [CommRing O] [Algebra O C] (hv : v.Integers O) (V : Type) [AddCommGroup V] [Module C V]
    [Module O V] [IsScalarTower O C V] (L : Submodule O V) (U : Submodule C V) (hL : L.FG) :
    (L ⊓ U.restrictScalars O).FG := by
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := hinj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  let f : L →ₗ[O] (V ⧸ U) := (U.mkQ.restrictScalars O).comp L.subtype
  haveI : Module.Finite O L := Module.Finite.iff_fg.2 hL
  haveI : Module.Finite O (LinearMap.range f) := inferInstance
  haveI : Module.Flat O (LinearMap.range f) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hx⟩ ⟨⟨a, ha⟩, h⟩
    have h1 : a • x = 0 := congrArg Subtype.val h
    have ha0 : algebraMap O C a ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero ha (hinj (by simpa using h0))
    rw [← algebraMap_smul C a x] at h1
    have : x = 0 := (smul_eq_zero.1 h1).resolve_left ha0
    simp [this]
  haveI : Module.Free O (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  let p : L →ₗ[O] V := L.subtype.comp (LinearMap.id - s.comp f.rangeRestrict)
  have key : L ⊓ U.restrictScalars O = LinearMap.range p := by
    apply le_antisymm
    · rintro x ⟨hxL, hxU⟩
      refine ⟨⟨x, hxL⟩, ?_⟩
      have : f.rangeRestrict ⟨x, hxL⟩ = 0 := by
        apply Subtype.ext
        change U.mkQ x = 0
        exact (Submodule.Quotient.mk_eq_zero U).2 hxU
      simp [p, this]
    · rintro _ ⟨y, rfl⟩
      refine ⟨(y - s (f.rangeRestrict y)).2, ?_⟩
      have h2 : f.rangeRestrict (s (f.rangeRestrict y)) = f.rangeRestrict y :=
        LinearMap.congr_fun hs _
      have h3 : f (y - s (f.rangeRestrict y)) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact (congrArg Subtype.val h2).symm
      exact (Submodule.Quotient.mk_eq_zero U).1 h3
  rw [key]
  exact Module.Finite.iff_fg.1 inferInstance

end GlobalTheory.CompanionTheory.Ar.HT

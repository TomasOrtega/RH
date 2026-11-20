import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

/- English proof (translation)
Rewrite using `[Scheme.ker_of_isAffine, baseIdeal]`. Use `congr 1`. Establish `h1` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))`. Establish `h1' : ∀ y, (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom y) = Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y)` using `fun y => by`. Rewrite using `[← CommRingCat.comp_apply, h1, CommRingCat.comp_apply]`.

Both sides reduce to the same expression. Establish `hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom` using `(ConcreteCategory.bijective_of_isIso _).1`. Establish `hc : ∀ r : R, cst (𝟙 (Spec (CommRingCat.of R))) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r`. Introduce `r`. Simplify using `[cst, rs]`.

Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, ← map_eq_zero_iff _ hinj, h1']`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hm` using `Ideal.mem_map_of_mem (cst (𝟙 (Spec (CommRingCat.of R))) ⊤) (Ideal.Quotient.eq_zero_iff_mem.1 hx)`.

Rewrite `hm` using `[hc, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]`. Then use the resulting hypothesis. Introduce `hx`. Establish `hle : J.map (cst (𝟙 (Spec (CommRingCat.of R))) ⊤) ≤ RingHom.ker ((Ideal.Quotient.mk J).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom)`. Use `Ideal.map_le_iff_le_comap.2 fun j hj => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hc, RingHom.comp_apply, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hj`. Conclude with `hle hx`.
-/
theorem ker_specMap_quotientMk (R : Type) [CommRing R] (J : Ideal R) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker =
      baseIdeal (𝟙 (Spec (CommRingCat.of R))) J := by
  rw [Scheme.ker_of_isAffine, baseIdeal]
  congr 1
  have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have h1' : ∀ y, (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom y) =
        Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := fun y => by
    rw [← CommRingCat.comp_apply, h1, CommRingCat.comp_apply]
    rfl
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hc : ∀ r : R, cst (𝟙 (Spec (CommRingCat.of R))) ⊤ r =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    intro r
    simp [cst, rs]
  ext x
  rw [RingHom.mem_ker, ← map_eq_zero_iff _ hinj, h1']
  constructor
  · intro hx
    have hm := Ideal.mem_map_of_mem (cst (𝟙 (Spec (CommRingCat.of R))) ⊤)
      (Ideal.Quotient.eq_zero_iff_mem.1 hx)
    rwa [hc, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at hm
  · intro hx
    have hle : J.map (cst (𝟙 (Spec (CommRingCat.of R))) ⊤) ≤
        RingHom.ker ((Ideal.Quotient.mk J).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom) := by
      refine Ideal.map_le_iff_le_comap.2 fun j hj => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hc, RingHom.comp_apply, ← CommRingCat.comp_apply,
        Iso.inv_hom_id, CommRingCat.id_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hj
    exact hle hx

/- English proof (translation)
Introduce `R _ J W Y f b q h`. Use `haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `e : h.isoPullback.hom ≫ pullback.fst _ _ = b` using `h.isoPullback_hom_fst`. Use `haveI hb : IsClosedImmersion b := by`. Rewrite using `[← e]`.

Use `infer_instance`. Establish `hk : b.ker = baseIdeal f J`. Rewrite using `[← e, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ker_specMap_quotientMk, (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1, Category.comp_id]`. Use `⟨hb, hk, fun V hV => ⟨b.app_surjective V hV, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.ker_apply b ⟨V, hV⟩, hk, baseIdeal_ideal]`.
-/
theorem baseChange_quotient : ∀ (R : Type) [CommRing R] (J : Ideal R) (W Y : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))),
    IsPullback b q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) →
      IsClosedImmersion b ∧ b.ker = baseIdeal f J ∧ ∀ V : W.Opens, IsAffineOpen V →
        Function.Surjective (b.app V).hom ∧ RingHom.ker (b.app V).hom = J.map (cst f V) := by
  intro R _ J W Y f b q h
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have e : h.isoPullback.hom ≫ pullback.fst _ _ = b := h.isoPullback_hom_fst
  haveI hb : IsClosedImmersion b := by
    rw [← e]
    infer_instance
  have hk : b.ker = baseIdeal f J := by
    rw [← e, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ker_specMap_quotientMk, (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1, Category.comp_id]
  refine ⟨hb, hk, fun V hV => ⟨b.app_surjective V hV, ?_⟩⟩
  rw [← Scheme.Hom.ker_apply b ⟨V, hV⟩, hk, baseIdeal_ideal]

end GlobalTheory.FormalAlg

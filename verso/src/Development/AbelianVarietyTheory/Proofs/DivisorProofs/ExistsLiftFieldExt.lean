import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Take `⟨⟨p, φ⟩, hy⟩` from `(Scheme.SpecToEquivOfField K X).symm.surjective y`. Establish `hp : p = j ξ`. Rewrite using `[← h, ← hy]`. Conclude with `(X.fromSpecResidueField_apply p _).symm`. Substitute `hp` using the available equality.

Establish `: IsIso (j.residueFieldMap ξ)`. Use `(ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `X'.residue_surjective ξ a`. Take `⟨b, rfl⟩` from `j.stalkMap_surjective ξ a`. Conclude with `⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩`.

Use `⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id_assoc]`.
-/
theorem fieldPoint_lift_of_isPreimmersion {X' X : Scheme.{0}} (j : X' ⟶ X) [IsPreimmersion j] {K : Type} [Field K]
    (y : Sp K ⟶ X) (ξ : X') (h : y (IsLocalRing.closedPoint K) = j ξ) : ∃ z : Sp K ⟶ X', z ≫ j = y := by
  obtain ⟨⟨p, φ⟩, hy⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  have hp : p = j ξ := by
    rw [← h, ← hy]
    exact (X.fromSpecResidueField_apply p _).symm
  subst hp
  have : IsIso (j.residueFieldMap ξ) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := X'.residue_surjective ξ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective ξ a
    exact ⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩
  refine ⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩
  rw [← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc]

/- English proof (translation)
Take `⟨g, hg, w, hw⟩` from `hg`. Take `⟨y, hy⟩` from `(Emb.range_closed R S π G' E).1 g hg`. Establish `hsub : ∀ a b : Sp Ω, a = b` using `fun a b => Subsingleton.elim (α := PrimeSpectrum Ω) a b`. Establish `hx : ∀ v, (s ≫ π) v = closedPoint R`. Introduce `v`.

Rewrite using `[hsub v w, ← hν, Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, E.f_over]`. Simplify `hg` using `only [Scheme.Hom.comp_apply]`. Take `⟨κ, hκ⟩` from `spMap_factor_residueField_of_closedPoint R Ω (s ≫ π) hx`. Use `E.imm` as an intermediate fact. Take `⟨y₀, hy₀⟩` from `fieldPoint_lift_of_isPreimmersion E.j ν y (by rw [hsub (closedPoint Ω) w, hw, hy])`.

Establish `hcl : IsClosedImmersion (spMap (residue R))` using `IsClosedImmersion.spec_of_surjective _ (residue_surjective (R := R))`. Establish `hY : y₀ ≫ E.Y.hom = spMap κ`. Rewrite using `[← cancel_mono (spMap (residue R)), Category.assoc, ← E.j_over, ← Category.assoc, hy₀, hν, hκ, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨Ω', _, io, e, l, -, hl1, hl2⟩` from `E.fib Ω s κ hκ`.

Set `t : Sp Ω' ⟶ pullback E.Y.hom (spMap (io.comp κ))` to `pullback.lift (spMap io ≫ y₀) (𝟙 _) (by rw [Category.assoc, hY, Category.id_comp, ← Spec.map_comp]; rfl)`. Establish `h1 : t ≫ pullback.fst _ _ = spMap io ≫ y₀` using `pullback.lift_fst _ _ _`. Establish `h2 : t ≫ pullback.snd _ _ = 𝟙 _` using `pullback.lift_snd _ _ _`. Establish `he : e.inv.left ≫ e.hom.left = 𝟙 _` using `by rw [← Over.comp_left, e.inv_hom_id]; rfl`. Establish `hw' : e.inv.left ≫ pullback.snd G'.hom (spMap io ≫ s) = pullback.snd E.Y.hom (spMap (io.comp κ))` using `Over.w e.inv`.

Use `⟨Ω', inferInstance, io, t ≫ e.inv.left ≫ l, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hl2, ← Category.assoc e.inv.left, he, ← hy₀, ← Category.assoc (spMap io), ← h1]`. Simplify using the standard rewrite rules. Rewrite using `[Category.assoc, Category.assoc, ← Category.assoc l, hl1] erw [pullback.condition, ← Category.assoc e.inv.left, hw', ← Category.assoc, h2, Category.id_comp]`.
-/
theorem Emb.exists_lift_fieldExt (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (E : Emb π G') (Ω : Type) [Field Ω] (ν : Sp Ω ⟶ PSpace R E.N) (s : Sp Ω ⟶ S)
    (hν : ν ≫ PSpace.str R E.N = s ≫ π)
    (hg : ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (q : Sp Ω' ⟶ E.H.toScheme),
      q ≫ E.f = spMap io ≫ ν ∧ q ≫ E.H.ι ≫ G'.hom = spMap io ≫ s := by
  obtain ⟨g, hg, w, hw⟩ := hg
  obtain ⟨y, hy⟩ := (Emb.range_closed R S π G' E).1 g hg
  have hsub : ∀ a b : Sp Ω, a = b := fun a b => Subsingleton.elim (α := PrimeSpectrum Ω) a b
  have hx : ∀ v, (s ≫ π) v = closedPoint R := by
    intro v
    rw [hsub v w, ← hν, Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, E.f_over]
    simpa only [Scheme.Hom.comp_apply] using hg
  obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (s ≫ π) hx
  have := E.imm
  obtain ⟨y₀, hy₀⟩ := fieldPoint_lift_of_isPreimmersion E.j ν y (by rw [hsub (closedPoint Ω) w, hw, hy])
  have hcl : IsClosedImmersion (spMap (residue R)) :=
    IsClosedImmersion.spec_of_surjective _ (residue_surjective (R := R))
  have hY : y₀ ≫ E.Y.hom = spMap κ := by
    rw [← cancel_mono (spMap (residue R)), Category.assoc, ← E.j_over, ← Category.assoc, hy₀, hν, hκ,
      ← Spec.map_comp]
    rfl
  obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω s κ hκ
  let t : Sp Ω' ⟶ pullback E.Y.hom (spMap (io.comp κ)) :=
    pullback.lift (spMap io ≫ y₀) (𝟙 _) (by rw [Category.assoc, hY, Category.id_comp, ← Spec.map_comp]; rfl)
  have h1 : t ≫ pullback.fst _ _ = spMap io ≫ y₀ := pullback.lift_fst _ _ _
  have h2 : t ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have he : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id]; rfl
  have hw' : e.inv.left ≫ pullback.snd G'.hom (spMap io ≫ s) = pullback.snd E.Y.hom (spMap (io.comp κ)) :=
    Over.w e.inv
  refine ⟨Ω', inferInstance, io, t ≫ e.inv.left ≫ l, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hl2, ← Category.assoc e.inv.left, he, ← hy₀, ← Category.assoc (spMap io), ← h1]
    simp
  · rw [Category.assoc, Category.assoc, ← Category.assoc l, hl1]
    erw [pullback.condition, ← Category.assoc e.inv.left, hw', ← Category.assoc, h2, Category.id_comp]

end GlobalTheory.Mum

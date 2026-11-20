import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorDown

/- English proof (translation)
Introduce `Z R R' _ _ _ _ _ gam hgam x a' hx`. Take `⟨U, hU, hz, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens) (show a' (IsLocalRing.closedPoint R') ∈ (⊤ : Z.Opens) from trivial)`. Establish `hU' : IsAffineOpen U` using `hU`. Establish `hra : Set.range a' ⊆ Set.range hU'.fromSpec`. Rewrite using `[hU'.range_fromSpec]`.

Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `((IsLocalRing.specializes_closedPoint p).map a'.continuous).mem_open U.isOpen hz`. Establish `hrx : Set.range x ⊆ Set.range hU'.fromSpec`. Introduce and unpack `_ ⟨t, rfl⟩`. Take `⟨t'⟩ : Nonempty (Sp (FractionRing R'))` from `inferInstance`.

Establish `e1 : (spMap gam) t' = t` using `Subsingleton.elim _ _`. Establish `e2` using `congrArg (fun h : Sp (FractionRing R') ⟶ Z => h t') hx`. Simplify using `only [Scheme.Hom.comp_apply] at e2`. Rewrite using `[← e1, ← e2]`. Conclude with `hra ⟨_, rfl⟩`.

Establish `ha₁` using `IsOpenImmersion.lift_fac hU'.fromSpec a' hra`. Establish `hx₁` using `IsOpenImmersion.lift_fac hU'.fromSpec x hrx`. Rewrite `ha₁` using `[← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec a' hra)]`. Rewrite `hx₁` using `[← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)]`. Use `set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec a' hra) with hψ`.

Use `set χ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hχ`. Establish `key : ψ ≫ CommRingCat.ofHom (algebraMap R' (FractionRing R')) = χ ≫ CommRingCat.ofHom gam`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, ha₁, hx₁]`. Conclude with `hx`.

Establish `hmem : ∀ b : Γ(Z, U), χ.hom b ∈ (algebraMap R (FractionRing R)).range`. Introduce `b`. Establish `e` using `congrArg (fun h => h.hom b) key`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e`. Take `⟨r, hr⟩` from `hgam (χ.hom b) (ψ.hom b) e`.

Conclude with `⟨r, hr⟩`. Establish `hinj : Function.Injective (algebraMap R (FractionRing R)).rangeRestrict` using `fun a b h => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)`. Set `eR` to `RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict ⟨hinj, RingHom.rangeRestrict_surjective _⟩`. Set `θ : Γ(Z, U) →+* R` to `eR.symm.toRingHom.comp (χ.hom.codRestrict _ hmem)`. Establish `hθ : ∀ b, algebraMap R (FractionRing R) (θ b) = χ.hom b`.

Introduce `b`. Use `eR.apply_symm_apply (χ.hom.codRestrict _ hmem b)` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Use `⟨Spec.map (CommRingCat.ofHom θ : Γ(Z, U) ⟶ CommRingCat.of R) ≫ hU'.fromSpec, ?_⟩` and prove the remaining obligations. Rewrite using `[← hx₁, ← Category.assoc]`.

Use `congr 1`. Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Use extensionality with `b`. Conclude with `hθ b`.
-/
theorem ext_of_fraction_meet : ∀ (Z : Scheme.{0}) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (gam : FractionRing R →+* FractionRing R'), (∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x) → ∀ (x : Sp (FractionRing R) ⟶ Z) (a' : Sp R' ⟶ Z), jK R' ≫ a' = spMap gam ≫ x → ∃ a : Sp R ⟶ Z, jK R ≫ a = x := by
  intro Z R R' _ _ _ _ _ gam hgam x a' hx
  obtain ⟨U, hU, hz, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens)
    (show a' (IsLocalRing.closedPoint R') ∈ (⊤ : Z.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hra : Set.range a' ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map a'.continuous).mem_open U.isOpen hz
  have hrx : Set.range x ⊆ Set.range hU'.fromSpec := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t'⟩ : Nonempty (Sp (FractionRing R')) := inferInstance
    have e1 : (spMap gam) t' = t := Subsingleton.elim _ _
    have e2 := congrArg (fun h : Sp (FractionRing R') ⟶ Z => h t') hx
    simp only [Scheme.Hom.comp_apply] at e2
    rw [← e1, ← e2]
    exact hra ⟨_, rfl⟩
  have ha₁ := IsOpenImmersion.lift_fac hU'.fromSpec a' hra
  have hx₁ := IsOpenImmersion.lift_fac hU'.fromSpec x hrx
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec a' hra)] at ha₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)] at hx₁
  set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec a' hra) with hψ
  set χ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hχ
  have key : ψ ≫ CommRingCat.ofHom (algebraMap R' (FractionRing R')) = χ ≫ CommRingCat.ofHom gam := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ha₁, hx₁]
    exact hx
  have hmem : ∀ b : Γ(Z, U), χ.hom b ∈ (algebraMap R (FractionRing R)).range := by
    intro b
    have e := congrArg (fun h => h.hom b) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    obtain ⟨r, hr⟩ := hgam (χ.hom b) (ψ.hom b) e
    exact ⟨r, hr⟩
  have hinj : Function.Injective (algebraMap R (FractionRing R)).rangeRestrict := fun a b h =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)
  let eR := RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
    ⟨hinj, RingHom.rangeRestrict_surjective _⟩
  let θ : Γ(Z, U) →+* R := eR.symm.toRingHom.comp (χ.hom.codRestrict _ hmem)
  have hθ : ∀ b, algebraMap R (FractionRing R) (θ b) = χ.hom b := by
    intro b
    have := eR.apply_symm_apply (χ.hom.codRestrict _ hmem b)
    exact congrArg Subtype.val this
  refine ⟨Spec.map (CommRingCat.ofHom θ : Γ(Z, U) ⟶ CommRingCat.of R) ≫ hU'.fromSpec, ?_⟩
  rw [← hx₁, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext b
  exact hθ b

end GlobalTheory.TorDown

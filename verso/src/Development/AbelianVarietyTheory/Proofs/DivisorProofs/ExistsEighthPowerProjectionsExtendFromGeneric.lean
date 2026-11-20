import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PowExtend

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Fan.IsLimit.hom_ext hl _ _ fun a => ?_` and prove the remaining obligations. Use `hp a` as an intermediate fact. Use `he a` as an intermediate fact. Express the relevant statement in the definitionally equal form `(_ ≫ e) ≫ p a = _ ≫ p a`.

Rewrite using `[Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]`. Use `Fan.IsLimit.hom_ext hl _ _ fun a => ?_` and prove the remaining obligations. Use `hp a` as an intermediate fact. Use `he a` as an intermediate fact. Express the relevant statement in the definitionally equal form `(_ ≫ e) ≫ p a = (_ ≫ _) ≫ p a`.

Rewrite using `[Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]`.
-/
theorem isMonHom_of_components {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {ι : Type}
    {A B C : 𝒞} [MonObj A] [MonObj B] [MonObj C] (p : ι → (B ⟶ C)) (hp : ∀ a, IsMonHom (p a))
    (hl : IsLimit (Fan.mk B p)) (e : A ⟶ B) (he : ∀ a, IsMonHom (e ≫ p a)) : IsMonHom e := by
  refine ⟨?_, ?_⟩
  · refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    have := hp a
    have := he a
    change (_ ≫ e) ≫ p a = _ ≫ p a
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    have := hp a
    have := he a
    change (_ ≫ e) ≫ p a = (_ ≫ _) ≫ p a
    rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      tensorHom_comp_tensorHom]

/- English proof (translation)
Establish `hA : IsLimit (Fan.mk A q)` using `mkFanLimit _ (fun s => (hq s.pt s.proj).exists.choose) (fun s a => (hq s.pt s.proj).exists.choose_spec a) (fun s m hm => (hq s.pt s.proj).unique hm (hq s.pt s.proj).exists.choose_spec)`. Conclude with `⟨hA.conePointUniqueUpToIso hl, fun a => hA.conePointUniqueUpToIso_hom_comp hl ⟨a⟩⟩`.
-/
theorem exists_iso_of_universal {𝒞 : Type*} [Category 𝒞] {ι : Type} {A B C : 𝒞} (p : ι → (B ⟶ C))
    (hl : IsLimit (Fan.mk B p)) (q : ι → (A ⟶ C))
    (hq : ∀ (T : 𝒞) (y : ι → (T ⟶ C)), ∃! x : T ⟶ A, ∀ a, x ≫ q a = y a) :
    ∃ e : A ≅ B, ∀ a, e.hom ≫ p a = q a := by
  have hA : IsLimit (Fan.mk A q) :=
    mkFanLimit _ (fun s => (hq s.pt s.proj).exists.choose)
      (fun s a => (hq s.pt s.proj).exists.choose_spec a)
      (fun s m hm => (hq s.pt s.proj).unique hm (hq s.pt s.proj).exists.choose_spec)
  exact ⟨hA.conePointUniqueUpToIso hl, fun a => hA.conePointUniqueUpToIso_hom_comp hl ⟨a⟩⟩

/- English proof (translation)
Use `⟨hl.lift (Fan.mk T y) ≫ E.inv, fun a => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, E.inv_hom_id_assoc]`. Conclude with `hl.fac (Fan.mk T y) ⟨a⟩`. Rewrite using `[Iso.eq_comp_inv]`. Use `Fan.IsLimit.hom_ext hl _ _ fun a => ?_` and prove the remaining obligations.

Conclude with `((Category.assoc _ _ _).trans (hx a)).trans (hl.fac (Fan.mk T y) ⟨a⟩).symm`.
-/
theorem universal_of_iso {𝒞 : Type*} [Category 𝒞] {ι : Type} {A B C : 𝒞} (p : ι → (B ⟶ C))
    (hl : IsLimit (Fan.mk B p)) (E : A ≅ B) (T : 𝒞) (y : ι → (T ⟶ C)) :
    ∃! x : T ⟶ A, ∀ a, x ≫ (E.hom ≫ p a) = y a := by
  refine ⟨hl.lift (Fan.mk T y) ≫ E.inv, fun a => ?_, fun x hx => ?_⟩
  · rw [Category.assoc, E.inv_hom_id_assoc]
    exact hl.fac (Fan.mk T y) ⟨a⟩
  · rw [Iso.eq_comp_inv]
    refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    exact ((Category.assoc _ _ _).trans (hx a)).trans (hl.fac (Fan.mk T y) ⟨a⟩).symm

/- English proof (translation)
Introduce `R _ _ _ _ G C _ _ _ _ hG hC pr' hm hu`. Establish `hH : IsSemiAbelian (powObj C 8)` using `GlobalTheory.SemiPow.isSemiAbelian_of_isPowGrp _ C (powObj C 8) 8 (powIsPowGrp C 8) (GlobalTheory.isSemiAbelian_of_isAbelianScheme C hC)`. Set `prK : Fin 8 → ((Over.pullback (jK R)).obj (powObj C 8) ⟶ (Over.pullback (jK R)).obj C)` to `fun i => (Over.pullback (jK R)).map (powPr C i)`. Establish `hlim : IsLimit (Fan.mk ((Over.pullback (jK R)).obj (powObj C 8)) prK)` using `isLimitFanMkObjOfIsLimit (Over.pullback (jK R)) (fun _ : Fin 8 => C) (powPr C) (powIsLimit C 8)`. Establish `hprKm : ∀ i, IsMonHom (prK i)` using `fun i => inferInstanceAs (IsMonHom ((Over.pullback (jK R)).map (powPr C i)))`.

Take `⟨e, he⟩` from `exists_iso_of_universal prK hlim pr' hu`. Establish `hem : IsMonHom e.hom` using `isMonHom_of_components prK hprKm hlim e.hom fun a => by`. Rewrite using `[he a]`. Conclude with `hm a`. Take `⟨E, ⟨hE, hEe⟩, -⟩` from `@GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic R _ _ _ _ (FractionRing R) _ _ _ G (powObj C 8) _ _ hG hH e hem`.

Use `⟨fun a => E.hom ≫ powPr C a, fun a => inferInstance, fun a => ?_, universal_of_iso (powPr C) (powIsLimit C 8) E⟩` and prove the remaining obligations. Rewrite using `[Functor.map_comp, ← he a]`. Conclude with `congrArg (· ≫ prK a) hEe`.
-/
theorem exists_pow_projections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G C : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj C] [IsCommMonObj C], IsSemiAbelian G → IsAbelianScheme C → ∀ pr' : Fin 8 → ((Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj C), (∀ a, IsMonHom (pr' a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ (Over.pullback (jK R)).obj C)), ∃! x : T' ⟶ (Over.pullback (jK R)).obj G, ∀ a, x ≫ pr' a = y a) → ∃ prO : Fin 8 → (G ⟶ C), (∀ a, IsMonHom (prO a)) ∧ (∀ a, (Over.pullback (jK R)).map (prO a) = pr' a) ∧ ∀ (T' : Over (Sp R)) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ G, ∀ a, x ≫ prO a = y a := by
  intro R _ _ _ _ G C _ _ _ _ hG hC pr' hm hu
  have hH : IsSemiAbelian (powObj C 8) :=
    GlobalTheory.SemiPow.isSemiAbelian_of_isPowGrp _ C (powObj C 8) 8 (powIsPowGrp C 8)
      (GlobalTheory.isSemiAbelian_of_isAbelianScheme C hC)
  let prK : Fin 8 → ((Over.pullback (jK R)).obj (powObj C 8) ⟶ (Over.pullback (jK R)).obj C) :=
    fun i => (Over.pullback (jK R)).map (powPr C i)
  have hlim : IsLimit (Fan.mk ((Over.pullback (jK R)).obj (powObj C 8)) prK) :=
    isLimitFanMkObjOfIsLimit (Over.pullback (jK R)) (fun _ : Fin 8 => C) (powPr C) (powIsLimit C 8)
  have hprKm : ∀ i, IsMonHom (prK i) := fun i =>
    inferInstanceAs (IsMonHom ((Over.pullback (jK R)).map (powPr C i)))
  obtain ⟨e, he⟩ := exists_iso_of_universal prK hlim pr' hu
  have hem : IsMonHom e.hom := isMonHom_of_components prK hprKm hlim e.hom fun a => by
    rw [he a]; exact hm a
  obtain ⟨E, ⟨hE, hEe⟩, -⟩ := @GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic R _ _ _ _
    (FractionRing R) _ _ _ G (powObj C 8) _ _ hG hH e hem
  refine ⟨fun a => E.hom ≫ powPr C a, fun a => inferInstance, fun a => ?_,
    universal_of_iso (powPr C) (powIsLimit C 8) E⟩
  rw [Functor.map_comp, ← he a]
  exact congrArg (· ≫ prK a) hEe

end GlobalTheory.PowExtend

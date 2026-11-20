import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.SplitField

/- English proof (translation)
Take `⟨t, ht⟩` from `Module.Finite.fg_top (R := E) (M := A)`. Take `⟨p, hp⟩ : ∃ p : Polynomial E, p = ∏ a ∈ t, minpoly E a` from `⟨_, rfl⟩`. Use `⟨p, fun Ω _ _ _ _ φ => ?_⟩` and prove the remaining obligations. Establish `hp0 : p ≠ 0` using `hp ▸ Finset.prod_ne_zero_iff.2 fun a _ => minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)`. Set `j : p.SplittingField →ₐ[E] Ω` to `IsScalarTower.toAlgHom E p.SplittingField Ω`.

Establish `hj : Function.Injective j` using `j.toRingHom.injective`. Establish `hgen : ∀ a ∈ t, φ a ∈ j.range` using `fun a ha => by`. Establish `h0 : Polynomial.aeval (φ a) p = 0`. Rewrite using `[Polynomial.aeval_algHom_apply, hp, map_prod, Finset.prod_eq_zero ha (minpoly.aeval E a), map_zero]`. Establish `hs` using `Polynomial.SplittingField.splits p`.

Establish `hr : φ a ∈ ((p.map (algebraMap E p.SplittingField)).map (algebraMap p.SplittingField Ω)).roots`. Rewrite using `[Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.mem_roots (Polynomial.map_ne_zero hp0), Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]`. Conclude with `h0`. Rewrite `hr` using `[hs.roots_map]`. Take `⟨b, -, hb⟩` from `Multiset.mem_map.1 hr`.

Conclude with `⟨b, hb⟩`. Establish `hall : ∀ a, φ a ∈ j.range` using `fun a => by`. Establish `ha : a ∈ Submodule.span E (t : Set A)` using `ht ▸ trivial`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx => exact hgen x hx`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`.

Conclude with `Subalgebra.smul_mem _ hx c`. Use `⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (φ.codRestrict j.range hall), fun a => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨φ a, hall a⟩)).symm`.
-/
theorem exists_algHom_factor (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] :
    ∃ p : Polynomial E, ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra p.SplittingField Ω]
      [IsScalarTower E p.SplittingField Ω] (φ : A →ₐ[E] Ω),
      ∃ φ₀ : A →ₐ[E] p.SplittingField, ∀ a, φ a = algebraMap p.SplittingField Ω (φ₀ a) := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := E) (M := A)
  obtain ⟨p, hp⟩ : ∃ p : Polynomial E, p = ∏ a ∈ t, minpoly E a := ⟨_, rfl⟩
  refine ⟨p, fun Ω _ _ _ _ φ => ?_⟩
  have hp0 : p ≠ 0 := hp ▸ Finset.prod_ne_zero_iff.2 fun a _ => minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)
  let j : p.SplittingField →ₐ[E] Ω := IsScalarTower.toAlgHom E p.SplittingField Ω
  have hj : Function.Injective j := j.toRingHom.injective
  have hgen : ∀ a ∈ t, φ a ∈ j.range := fun a ha => by
    have h0 : Polynomial.aeval (φ a) p = 0 := by
      rw [Polynomial.aeval_algHom_apply, hp, map_prod, Finset.prod_eq_zero ha (minpoly.aeval E a), map_zero]
    have hs := Polynomial.SplittingField.splits p
    have hr : φ a ∈ ((p.map (algebraMap E p.SplittingField)).map (algebraMap p.SplittingField Ω)).roots := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.mem_roots (Polynomial.map_ne_zero hp0),
        Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      exact h0
    rw [hs.roots_map] at hr
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 hr
    exact ⟨b, hb⟩
  have hall : ∀ a, φ a ∈ j.range := fun a => by
    have ha : a ∈ Submodule.span E (t : Set A) := ht ▸ trivial
    induction ha using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Subalgebra.smul_mem _ hx c
  refine ⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (φ.codRestrict j.range hall), fun a => ?_⟩
  exact (congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨φ a, hall a⟩)).symm

/- English proof (translation)
Establish `: IsAffine Z` using `isAffine_of_isAffineHom f`. Take `⟨g, hg⟩` from `Spec.map_surjective (R := CommRingCat.of E) (Z.isoSpec.inv ≫ f)`. Establish `hfin : g.hom.Finite` using `(IsFinite.SpecMap_iff g).1 (hg ▸ inferInstance)`. Use `letI : Algebra E Γ(Z, ⊤) := g.hom.toAlgebra`. Establish `: Module.Finite E Γ(Z, ⊤)` using `hfin`.

Take `⟨p, hp⟩` from `exists_algHom_factor E Γ(Z, ⊤)`. Use `⟨p, fun Ω _ _ _ _ z hz => ?_⟩` and prove the remaining obligations. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (S := CommRingCat.of Ω) (z ≫ Z.isoSpec.hom)`. Establish `hc : g ≫ ψ = CommRingCat.ofHom (algebraMap E Ω)` using `Spec.map_injective (by`. Rewrite using `[Spec.map_comp, hg, hψ, Category.assoc, Iso.hom_inv_id_assoc, hz])`.

Take `⟨φ₀, h₀⟩` from `hp Ω { ψ.hom with commutes' := fun a => congrArg (fun q => q.hom a) hc }`. Use `⟨Spec.map (CommRingCat.ofHom φ₀.toRingHom) ≫ Z.isoSpec.inv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hg, ← Spec.map_comp]`. Conclude with `congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => φ₀.commutes a))`. Rewrite using `[← Category.assoc, Iso.eq_comp_inv, ← hψ, ← Spec.map_comp]`.

Conclude with `congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => h₀ a))`.
-/
theorem exists_point_factor (E : Type) [Field E] {Z : Scheme.{0}} (f : Z ⟶ Sp E) [IsFinite f] :
    ∃ p : Polynomial E, ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra p.SplittingField Ω]
      [IsScalarTower E p.SplittingField Ω] (z : Sp Ω ⟶ Z), z ≫ f = spMap (algebraMap E Ω) →
      ∃ z₀ : Sp p.SplittingField ⟶ Z, z₀ ≫ f = spMap (algebraMap E p.SplittingField) ∧
        z = spMap (algebraMap p.SplittingField Ω) ≫ z₀ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨g, hg⟩ := Spec.map_surjective (R := CommRingCat.of E) (Z.isoSpec.inv ≫ f)
  have hfin : g.hom.Finite := (IsFinite.SpecMap_iff g).1 (hg ▸ inferInstance)
  letI : Algebra E Γ(Z, ⊤) := g.hom.toAlgebra
  have : Module.Finite E Γ(Z, ⊤) := hfin
  obtain ⟨p, hp⟩ := exists_algHom_factor E Γ(Z, ⊤)
  refine ⟨p, fun Ω _ _ _ _ z hz => ?_⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (S := CommRingCat.of Ω) (z ≫ Z.isoSpec.hom)
  have hc : g ≫ ψ = CommRingCat.ofHom (algebraMap E Ω) := Spec.map_injective (by
    rw [Spec.map_comp, hg, hψ, Category.assoc, Iso.hom_inv_id_assoc, hz])
  obtain ⟨φ₀, h₀⟩ := hp Ω { ψ.hom with commutes' := fun a => congrArg (fun q => q.hom a) hc }
  refine ⟨Spec.map (CommRingCat.ofHom φ₀.toRingHom) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => φ₀.commutes a))
  · rw [← Category.assoc, Iso.eq_comp_inv, ← hψ, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => h₀ a))

/- English proof (translation)
Use `(S.mem_subPts_cut_baseChange_iff E s x).trans (Iff.trans ?_ (S.mem_subPts_cut_baseChange_iff E' (fun i k => algebraMap E E' (s i k)) x').symm)` and prove the remaining obligations. Rewrite using `[h]`. Simplify using `only [← IsScalarTower.algebraMap_apply]`.
-/
theorem mem_subPts_iff_of_toBase_eq {F : Type} [Field F] (S : LinSys F) (E E' : Type) [Field E] [Field E'] [Algebra F E]
    [Algebra F E'] [Algebra E E'] {ι : Type} (s : ι → Fin S.N → E)
    {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra E' Ω] [Algebra F Ω] [IsScalarTower F E Ω] [IsScalarTower F E' Ω]
    [IsScalarTower E E' Ω] (x : (S.baseChange E).Pt Ω) (x' : (S.baseChange E').Pt Ω)
    (h : LinSys.toBase x = LinSys.toBase x') :
    x ∈ (S.baseChange E).subPts ((S.baseChange E).cut s) Ω ↔
      x' ∈ (S.baseChange E').subPts ((S.baseChange E').cut fun i k => algebraMap E E' (s i k)) Ω := by
  refine (S.mem_subPts_cut_baseChange_iff E s x).trans
    (Iff.trans ?_ (S.mem_subPts_cut_baseChange_iff E' (fun i k => algebraMap E E' (s i k)) x').symm)
  rw [h]
  simp only [← IsScalarTower.algebraMap_apply]

end GlobalTheory.HSCore.SplitField

namespace GlobalTheory.HSCore

open SplitField in

/- English proof (translation)
Introduce `F _ _ T E _ _ _ s hs`. Establish `hfin : IsFinite ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)` using `hs.finiteEtale.finite`. Take `⟨p, hp⟩` from `exists_point_factor E ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)`. Use `⟨p.SplittingField, inferInstance, NumberField.of_module_finite E _, inferInstance, inferInstance, inferInstance, fun x hx => ?_⟩` and prove the remaining obligations. Set `x' : (T.toLinSys.baseChange p.SplittingField).Pt (AlgebraicClosure p.SplittingField)` to `⟨x ≫ Scheme.IdealSheafData.subschemeι _, (Category.assoc _ _ _).trans hx⟩`.

Take `⟨y, hy⟩` from `(T.toLinSys.toBase_bijective E (AlgebraicClosure p.SplittingField)).2 (LinSys.toBase x')`. Take `⟨z, hz⟩` from `(mem_subPts_iff_of_toBase_eq T.toLinSys E p.SplittingField s y x' hy).2 ⟨x, rfl⟩`. Take `⟨z₀, h₀, h₁⟩` from `hp (AlgebraicClosure p.SplittingField) z (by`. Rewrite using `[← Category.assoc]`. Conclude with `(congrArg (· ≫ _) hz).trans y.2)`.

Set `y₀ : (T.toLinSys.baseChange E).Pt p.SplittingField` to `⟨z₀ ≫ Scheme.IdealSheafData.subschemeι _, (Category.assoc _ _ _).trans h₀⟩`. Take `⟨x₁, hx₁⟩` from `(T.toLinSys.toBase_bijective p.SplittingField p.SplittingField).2 (LinSys.toBase y₀)`. Take `⟨x₀, hx₀⟩` from `(mem_subPts_iff_of_toBase_eq T.toLinSys E p.SplittingField s y₀ x₁ hx₁.symm).1 ⟨z₀, rfl⟩`. Use `⟨x₀, ?_⟩` and prove the remaining obligations. Use `(cancel_mono (Scheme.IdealSheafData.subschemeι _)).1 ?_` and prove the remaining obligations.

Use `Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hx₀)).symm` and prove the remaining obligations. Use `(T.toLinSys.isPullback_baseChange p.SplittingField).hom_ext ?_ ?_` and prove the remaining obligations. Establish `e₁ : x₁.1 ≫ T.toLinSys.bcFst _ = y₀.1 ≫ T.toLinSys.bcFst _` using `congrArg Subtype.val hx₁`. Establish `e₂ : y.1 ≫ T.toLinSys.bcFst _ = x'.1 ≫ T.toLinSys.bcFst _` using `congrArg Subtype.val hy`. Use `e₂.symm.trans ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, e₁, ← hz, h₁, Category.assoc, Category.assoc]`. Both sides reduce to the same expression. Use `x'.2.trans ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, x₁.2, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem exists_split : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin T.D → Fin T.N → E), T.IsGoodSection E s → ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : Algebra F E') (_ : Algebra E E') (_ : IsScalarTower F E E'), Split T E' fun i k => algebraMap E E' (s i k) := by
  intro F _ _ T E _ _ _ s hs
  have hfin : IsFinite ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str) := hs.finiteEtale.finite
  obtain ⟨p, hp⟩ := exists_point_factor E ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
  refine ⟨p.SplittingField, inferInstance, NumberField.of_module_finite E _, inferInstance, inferInstance,
    inferInstance, fun x hx => ?_⟩
  let x' : (T.toLinSys.baseChange p.SplittingField).Pt (AlgebraicClosure p.SplittingField) :=
    ⟨x ≫ Scheme.IdealSheafData.subschemeι _, (Category.assoc _ _ _).trans hx⟩
  obtain ⟨y, hy⟩ := (T.toLinSys.toBase_bijective E (AlgebraicClosure p.SplittingField)).2 (LinSys.toBase x')
  obtain ⟨z, hz⟩ := (mem_subPts_iff_of_toBase_eq T.toLinSys E p.SplittingField s y x' hy).2 ⟨x, rfl⟩
  obtain ⟨z₀, h₀, h₁⟩ := hp (AlgebraicClosure p.SplittingField) z (by
    rw [← Category.assoc]; exact (congrArg (· ≫ _) hz).trans y.2)
  let y₀ : (T.toLinSys.baseChange E).Pt p.SplittingField :=
    ⟨z₀ ≫ Scheme.IdealSheafData.subschemeι _, (Category.assoc _ _ _).trans h₀⟩
  obtain ⟨x₁, hx₁⟩ := (T.toLinSys.toBase_bijective p.SplittingField p.SplittingField).2 (LinSys.toBase y₀)
  obtain ⟨x₀, hx₀⟩ := (mem_subPts_iff_of_toBase_eq T.toLinSys E p.SplittingField s y₀ x₁ hx₁.symm).1 ⟨z₀, rfl⟩
  refine ⟨x₀, ?_⟩
  refine (cancel_mono (Scheme.IdealSheafData.subschemeι _)).1 ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hx₀)).symm
  refine (T.toLinSys.isPullback_baseChange p.SplittingField).hom_ext ?_ ?_
  · have e₁ : x₁.1 ≫ T.toLinSys.bcFst _ = y₀.1 ≫ T.toLinSys.bcFst _ := congrArg Subtype.val hx₁
    have e₂ : y.1 ≫ T.toLinSys.bcFst _ = x'.1 ≫ T.toLinSys.bcFst _ := congrArg Subtype.val hy
    refine e₂.symm.trans ?_
    rw [Category.assoc, e₁, ← hz, h₁, Category.assoc, Category.assoc]
    rfl
  · refine x'.2.trans ?_
    rw [Category.assoc, x₁.2, ← Spec.map_comp]
    rfl

end GlobalTheory.HSCore

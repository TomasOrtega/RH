import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.RootUnitGeom

/- English proof (translation)
Establish `hw : IsNilpotent (∑ i ∈ Finset.range k, (v ^ i - 1))`. Use `isNilpotent_sum fun i _ => ?_` and prove the remaining obligations. Establish `: v ^ i - 1 = (∑ j ∈ Finset.range i, v ^ j) * (v - 1)` using `(geom_sum_mul v i).symm`. Rewrite using `[this]`. Conclude with `mem_nilradical.1 (Ideal.mul_mem_left _ _ (mem_nilradical.2 hn))`.

Establish `hs : ∑ i ∈ Finset.range k, v ^ i = (k : A) + ∑ i ∈ Finset.range k, (v ^ i - 1)`. Simplify using `[Finset.sum_sub_distrib]`. Establish `hu : IsUnit (∑ i ∈ Finset.range k, v ^ i)`. Rewrite using `[hs]`. Conclude with `hw.isUnit_add_left_of_commute hk (Commute.all _ _)`.

Establish `h0 : (∑ i ∈ Finset.range k, v ^ i) * (v - 1) = 0`. Rewrite using `[geom_sum_mul, hv, sub_self]`. Establish `: v - 1 = 0` using `(hu.mul_right_eq_zero).1 h0`. Conclude with `sub_eq_zero.1 this`.
-/
theorem eq_one_of_pow_eq_one_of_isNilpotent {A : Type*} [CommRing A] {v : A} {k : ℕ}
    (hk : IsUnit (k : A)) (hv : v ^ k = 1) (hn : IsNilpotent (v - 1)) : v = 1 := by
  have hw : IsNilpotent (∑ i ∈ Finset.range k, (v ^ i - 1)) := by
    refine isNilpotent_sum fun i _ => ?_
    have : v ^ i - 1 = (∑ j ∈ Finset.range i, v ^ j) * (v - 1) := (geom_sum_mul v i).symm
    rw [this]
    exact mem_nilradical.1 (Ideal.mul_mem_left _ _ (mem_nilradical.2 hn))
  have hs : ∑ i ∈ Finset.range k, v ^ i = (k : A) + ∑ i ∈ Finset.range k, (v ^ i - 1) := by
    simp [Finset.sum_sub_distrib]
  have hu : IsUnit (∑ i ∈ Finset.range k, v ^ i) := by
    rw [hs]
    exact hw.isUnit_add_left_of_commute hk (Commute.all _ _)
  have h0 : (∑ i ∈ Finset.range k, v ^ i) * (v - 1) = 0 := by
    rw [geom_sum_mul, hv, sub_self]
  have : v - 1 = 0 := (hu.mul_right_eq_zero).1 h0
  exact sub_eq_zero.1 this

end GlobalTheory.RootUnitGeom

namespace GlobalTheory.RootUnitGeom

/- English proof (translation)
Rewrite using `[Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]`. Simplify using `only [Category.assoc, Scheme.ΓSpecIso_naturality]`. Establish `e : (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)) = 𝟙 _` using `rfl`. Rewrite using `[e, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]`. Both sides reduce to the same expression.
-/
theorem fromSpecResidueField_appTop_comp (S : Scheme.{0}) (x : S) :
    (S.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ x trivial := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality]
  have e : (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)) = 𝟙 _ := rfl
  rw [e, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
  rfl

/- English proof (translation)
Set `K` to `AlgebraicClosure (S.residueField q)`. Set `f : S.residueField q ⟶ CommRingCat.of K` to `CommRingCat.ofHom (algebraMap (S.residueField q) K)`. Set `x : Sp K ⟶ S` to `Spec.map f ≫ S.fromSpecResidueField q`. Establish `hx : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom`. Simplify using `[spMap]`.

Establish `h1` using `h K x _ hx`. Establish `h2 : x.appTop (u : Γ(S, ⊤)) = 1`. Use `congrArg Units.val h1` as an intermediate fact. Simplify using `using this`. Establish `e : x.appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ q trivial ≫ f`.

Simplify using `only [x, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]`. Rewrite using `[← Category.assoc, fromSpecResidueField_appTop_comp]`. Establish `h3` using `congrArg (fun g => g (u : Γ(S, ⊤))) (congrArg (fun g => (CategoryTheory.ConcreteCategory.hom g : _ → _)) e)`. Simplify using `only [CategoryTheory.comp_apply, h2, map_one] at h3`. Apply `(algebraMap (S.residueField q) K).injective` to reduce the goal to its premises.

Rewrite using `[map_one]`. Conclude with `h3.symm`.
-/
theorem evaluation_eq_one (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R)
    (u : Γ(S, ⊤)ˣ)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β →
      Units.map x.appTop.hom.toMonoidHom u = 1) (q : S) :
    S.evaluation ⊤ q trivial (u : Γ(S, ⊤)) = 1 := by
  let K := AlgebraicClosure (S.residueField q)
  let f : S.residueField q ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap (S.residueField q) K)
  let x : Sp K ⟶ S := Spec.map f ≫ S.fromSpecResidueField q
  have hx : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
    simp [spMap]
  have h1 := h K x _ hx
  have h2 : x.appTop (u : Γ(S, ⊤)) = 1 := by
    have := congrArg Units.val h1
    simpa using this
  have e : x.appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ q trivial ≫ f := by
    simp only [x, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    rw [← Category.assoc, fromSpecResidueField_appTop_comp]
  have h3 := congrArg (fun g => g (u : Γ(S, ⊤))) (congrArg (fun g => (CategoryTheory.ConcreteCategory.hom g : _ → _)) e)
  simp only [CategoryTheory.comp_apply, h2, map_one] at h3
  apply (algebraMap (S.residueField q) K).injective
  rw [map_one]
  exact h3.symm

end GlobalTheory.RootUnitGeom

namespace GlobalTheory.RootUnitGeom

/- English proof (translation)
Take `⟨U, hU, hqU, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) (show q ∈ (⊤ : S.Opens) from trivial)`. Establish `hb : S.basicOpen (S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ε) = ⊥`. Rewrite using `[Scheme.basicOpen_res, hε, inf_bot_eq]`. Establish `hn` using `(Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact (IsAffineOpen.isCompact hU) _).2 hb`. Use `hn.map (S.presheaf.germ U q hqU).hom` as an intermediate fact.

Rewrite `this` using `[TopCat.Presheaf.germ_res_apply]`. Then use the resulting hypothesis.
-/
theorem germ_isNilpotent (S : Scheme.{0}) (ε : Γ(S, ⊤)) (hε : S.basicOpen ε = ⊥) (q : S) :
    IsNilpotent (S.presheaf.germ ⊤ q trivial ε) := by
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
    (show q ∈ (⊤ : S.Opens) from trivial)
  have hb : S.basicOpen (S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ε) = ⊥ := by
    rw [Scheme.basicOpen_res, hε, inf_bot_eq]
  have hn := (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact
    (IsAffineOpen.isCompact hU) _).2 hb
  have := hn.map (S.presheaf.germ U q hqU).hom
  rwa [TopCat.Presheaf.germ_res_apply] at this

end GlobalTheory.RootUnitGeom

open GlobalTheory.RootUnitGeom in

/- English proof (translation)
Introduce `R _ S s k u hk hu h`. Establish `hε : S.basicOpen ((u : Γ(S, ⊤)) - 1) = ⊥`. Rewrite using `[Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero]`. Introduce `x`. Rewrite using `[map_sub, map_one, evaluation_eq_one R S s u h x.1, sub_self]`.

Use `ext1`. Apply `TopCat.Presheaf.section_ext S.sheaf ⊤` to reduce the goal to its premises. Introduce `q hq`. Set `φ : R →+* S.presheaf.stalk q` to `(S.presheaf.germ ⊤ q trivial).hom.comp (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)`. Establish `hk' : IsUnit (k : S.presheaf.stalk q)`.

Simplify `hk.map φ` using `[map_natCast]`. Establish `hv : (S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤))) ^ k = 1`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]`. Establish `hn : IsNilpotent (S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤)) - 1)`. Use `germ_isNilpotent S _ hε q` as an intermediate fact.

Rewrite `this` using `[map_sub, map_one]`. Then use the resulting hypothesis. Use `eq_one_of_pow_eq_one_of_isNilpotent hk' hv hn` as an intermediate fact. Express the relevant statement in the definitionally equal form `S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤)) = S.presheaf.germ ⊤ q trivial ((1 : Γ(S, ⊤)ˣ) : Γ(S, ⊤))`. Rewrite using `[this, Units.val_one, map_one]`.
-/
theorem GlobalTheory.rootOfUnity_eq_one_of_geom : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R) (k : ℕ)
    (u : Γ(S, ⊤)ˣ), IsUnit (k : R) → u ^ k = 1 →
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β →
      Units.map x.appTop.hom.toMonoidHom u = 1) → u = 1 := by
  intro R _ S s k u hk hu h
  have hε : S.basicOpen ((u : Γ(S, ⊤)) - 1) = ⊥ := by
    rw [Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero]
    intro x
    rw [map_sub, map_one, evaluation_eq_one R S s u h x.1, sub_self]
  ext1
  apply TopCat.Presheaf.section_ext S.sheaf ⊤
  intro q hq
  let φ : R →+* S.presheaf.stalk q :=
    (S.presheaf.germ ⊤ q trivial).hom.comp (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hk' : IsUnit (k : S.presheaf.stalk q) := by
    simpa [map_natCast] using hk.map φ
  have hv : (S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤))) ^ k = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
  have hn : IsNilpotent (S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤)) - 1) := by
    have := germ_isNilpotent S _ hε q
    rwa [map_sub, map_one] at this
  have := eq_one_of_pow_eq_one_of_isNilpotent hk' hv hn
  change S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤)) = S.presheaf.germ ⊤ q trivial ((1 : Γ(S, ⊤)ˣ) : Γ(S, ⊤))
  rw [this, Units.val_one, map_one]

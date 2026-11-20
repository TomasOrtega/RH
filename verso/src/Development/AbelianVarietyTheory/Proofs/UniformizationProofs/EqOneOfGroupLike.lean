import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompRedIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.UnitRigid

/- English proof (translation)
Proceed by induction on `a using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a a' h h' => simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']`. Consider the case `single p r`. Proceed by induction on `b using AddMonoidAlgebra.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add b b' h h' => simp only [map_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']`. Consider the case `single q s`. Simplify using `only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]`. Apply the tactic sequence `by_cases h₁ : p = x <;> by_cases h₂ : q = y <;> simp [h₁, h₂]`.
-/
theorem coeff_inl_mul_inr {B X : Type} [CommRing B] [AddCommGroup X] (a b : AddMonoidAlgebra B X) (x y : X) :
    (AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) a *
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) b).coeff (x, y) = a.coeff x * b.coeff y := by
  classical
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' h h' => simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']
  | single p r =>
    induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' h h' => simp only [map_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']
    | single q s =>
      simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases h₁ : p = x <;> by_cases h₂ : q = y <;> simp [h₁, h₂]

/- English proof (translation)
Establish `idem : ∀ x, IsIdempotentElem (g.coeff x)` using `fun x => by`. Establish `e` using `congrArg (fun a => a.coeff (x, x)) h`. Simplify using `only [coeff_inl_mul_inr] at e`. Use `e.symm.trans ?_` and prove the remaining obligations. Conclude with `Finsupp.mapDomain_apply (f := fun x : X => (x, x)) (fun _ _ q => congrArg Prod.fst q) g.coeff x`.

Use extensionality with `x`. Establish `e` using `congrArg (fun a => a.coeff x) h₁`. Simplify using `only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at e ⊢`. Use `split_ifs at e ⊢ with hx`. Establish `m : 1 - g.coeff x ∈ I`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self]`. Conclude with `(sub_eq_zero.1 ((idem x).one_sub.eq_zero_of_isNilpotent (hI _ m))).symm`. Conclude with `(idem x).eq_zero_of_isNilpotent (hI _ (Ideal.Quotient.eq_zero_iff_mem.1 e))`.
-/
theorem eq_one_of_groupLike {B X : Type} [CommRing B] [AddCommGroup X] (I : Ideal B) (hI : ∀ b ∈ I, IsNilpotent b)
    (g : AddMonoidAlgebra B X)
    (h : AddMonoidAlgebra.mapDomainRingHom B ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) g =
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) g *
        AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) g)
    (h₁ : AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I) g = 1) : g = 1 := by
  classical
  have idem : ∀ x, IsIdempotentElem (g.coeff x) := fun x => by
    have e := congrArg (fun a => a.coeff (x, x)) h
    simp only [coeff_inl_mul_inr] at e
    refine e.symm.trans ?_
    exact Finsupp.mapDomain_apply (f := fun x : X => (x, x)) (fun _ _ q => congrArg Prod.fst q) g.coeff x
  ext x
  have e := congrArg (fun a => a.coeff x) h₁
  simp only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply] at e ⊢
  split_ifs at e ⊢ with hx
  · have m : 1 - g.coeff x ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self]
    exact (sub_eq_zero.1 ((idem x).one_sub.eq_zero_of_isNilpotent (hI _ m))).symm
  · exact (idem x).eq_zero_of_isNilpotent (hI _ (Ideal.Quotient.eq_zero_iff_mem.1 e))

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

/- English proof (translation)
Rewrite using `[chV_val, chV_val, Rosenlicht.over_appTop_comp]`.
-/
theorem chV_comp {Z Z' : Over S} (σ : Z' ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (σ ≫ t) χ).val = σ.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

/- English proof (translation)
The claim follows from `(splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun a => Units.ext (h a.toAdd))`.
-/
theorem point_ext {Z : Over S} {t t' : Z ⟶ splitTorus S X} (h : ∀ χ, (chV t χ).val = (chV t' χ).val) : t = t' :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun a => Units.ext (h a.toAdd))

/- English proof (translation)
Assemble the required witnesses or components as `⟨(splitTorusPointsEquiv S X Z).symm c.toHomUnits, fun χ => by rw [chV, MulEquiv.apply_symm_apply]; rfl⟩`.
-/
theorem exists_point (Z : Over S) (c : Multiplicative X →* Γ(Z.left, ⊤)) :
    ∃ t : Z ⟶ splitTorus S X, ∀ χ, (chV t χ).val = c (Multiplicative.ofAdd χ) :=
  ⟨(splitTorusPointsEquiv S X Z).symm c.toHomUnits, fun χ => by rw [chV, MulEquiv.apply_symm_apply]; rfl⟩

/- English proof (translation)
Take `⟨U, y₀, e, -, -, H⟩` from `RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) X) AddMonoidAlgebra.singleZeroRingHom`. Take `⟨t₀, ht₀⟩` from `exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))`. Use `⟨e ((lift t₀ (y₀ ≫ y)).left.appTop.hom u), fun Z s t θ h₁ h₂ => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ, hθ⟩` from `H Z s θ h₁`. Establish `ht : σ ≫ t₀ = t` using `point_ext fun χ => by`.

Rewrite using `[chV_comp, hθ, ht₀, ← h₂]`. Conclude with `congrArg θ (e.apply_symm_apply _)`. Rewrite using `[← hθ, ← ht, ← hσ, Category.assoc, ← comp_lift, Rosenlicht.over_appTop_comp]`.
-/
theorem exists_universal {Y W : Over S} [IsAffine W.left] (y : W ⟶ Y) (u : Γ((splitTorus S X ⊗ Y).left, ⊤)) :
    ∃ g : AddMonoidAlgebra Γ(W.left, ⊤) X, ∀ (Z : Over S) (s : Z ⟶ W) (t : Z ⟶ splitTorus S X)
      (θ : AddMonoidAlgebra Γ(W.left, ⊤) X →+* Γ(Z.left, ⊤)),
      (∀ b, θ (AddMonoidAlgebra.single 0 b) = s.left.appTop.hom b) →
      (∀ χ, θ (AddMonoidAlgebra.single χ 1) = (chV t χ).val) → (lift t (s ≫ y)).left.appTop.hom u = θ g := by
  obtain ⟨U, y₀, e, -, -, H⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) X)
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, ht₀⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
  refine ⟨e ((lift t₀ (y₀ ≫ y)).left.appTop.hom u), fun Z s t θ h₁ h₂ => ?_⟩
  obtain ⟨σ, hσ, hθ⟩ := H Z s θ h₁
  have ht : σ ≫ t₀ = t := point_ext fun χ => by
    rw [chV_comp, hθ, ht₀, ← h₂]
    exact congrArg θ (e.apply_symm_apply _)
  rw [← hθ, ← ht, ← hσ, Category.assoc, ← comp_lift, Rosenlicht.over_appTop_comp]

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_universal y u`. Set `I : Ideal Γ(W.left, ⊤)` to `J.map (RingPoint.strMap W)`. Establish `hI : ∀ b ∈ I, IsNilpotent b` using `fun b hb => by`. Take `⟨n, hn⟩` from `hJ`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Use `Ideal.pow_mem_pow hb n` as an intermediate fact. Rewrite `this` using `[← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]`. Conclude with `this`. Establish `one : g = 1`. Use `eq_one_of_groupLike I hI g ?_ ?_` and prove the remaining obligations.

Take `⟨U, s, e, -, he, -⟩` from `RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) (X × X)) AddMonoidAlgebra.singleZeroRingHom`. Establish `key : ∀ (f : X →+ X × X) (t : U ⟶ splitTorus _ X), (∀ χ, (chV t χ).val = e.symm (AddMonoidAlgebra.single (f χ) 1)) → (lift t (s ≫ y)).left.appTop.hom u = e.symm (AddMonoidAlgebra.mapDomainRingHom _ f g)` using `fun f t ht => hg U s t (e.symm.toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom _ f)) (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [ht]; simp)`. Take `⟨t₁, ht₁⟩` from `exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl X X))))`. Take `⟨t₂, ht₂⟩` from `exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr X X))))`. Establish `a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inl X X χ) 1)` using `ht₁`.

Establish `a₂ : ∀ χ, (chV t₂ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inr X X χ) 1)` using `ht₂`. Apply `e.symm.injective` to reduce the goal to its premises. Rewrite using `[map_mul, ← key _ t₁ a₁, ← key _ t₂ a₂, ← hm, key]`. Introduce `χ`. Rewrite using `[chV_mul, Units.val_mul, a₁, a₂, ← map_mul, AddMonoidAlgebra.single_mul_single]`.

Simplify using the standard rewrite rules. Take `⟨U, s, e, -, he, -⟩` from `RingPoint.exists_ringPoint W (AddMonoidAlgebra (Γ(W.left, ⊤) ⧸ I) X) (AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk I))`. Take `⟨t₁, ht₁⟩` from `exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))`. Establish `a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single χ 1)` using `ht₁`. Establish `hU : ∃ s, s ≫ red J = U.hom` using `(RingPoint.exists_comp_red_iff J U).2 fun a ha => by`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[← RingPoint.appTop_strMap s, he, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero, map_zero]`. Establish `k` using `hg U s t₁ (e.symm.toRingHom.comp (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I))) (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [a₁]; simp)`. Apply `e.symm.injective` to reduce the goal to its premises. Rewrite using `[map_one]`.

Conclude with `k.symm.trans (h₁ U hU _ _)`. Establish `k` using `hg W (𝟙 W) t (AddMonoidAlgebra.liftNCRingHom (RingHom.id _) ((Units.coeHom _).comp (splitTorusPointsEquiv _ X W t)) fun _ _ => Commute.all _ _) (fun b => by simp) (fun χ => by simp [chV])`. Rewrite `k` using `[Category.id_comp, one, map_one]`. Then use the resulting hypothesis.
-/
theorem eq_one_affine {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) {Y W : Over (Spec (CommRingCat.of A))}
    [IsAffine W.left] (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤))
    (hm : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u = (lift t y).left.appTop.hom u * (lift t' y).left.appTop.hom u)
    (h₁ : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift t y).left.appTop.hom u = 1) (t : W ⟶ splitTorus _ X) (y : W ⟶ Y) : (lift t y).left.appTop.hom u = 1 := by
  obtain ⟨g, hg⟩ := exists_universal y u
  let I : Ideal Γ(W.left, ⊤) := J.map (RingPoint.strMap W)
  have hI : ∀ b ∈ I, IsNilpotent b := fun b hb => by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hb n
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot] at this
    exact this
  have one : g = 1 := by
    refine eq_one_of_groupLike I hI g ?_ ?_
    · obtain ⟨U, s, e, -, he, -⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) (X × X))
        AddMonoidAlgebra.singleZeroRingHom
      have key : ∀ (f : X →+ X × X) (t : U ⟶ splitTorus _ X),
          (∀ χ, (chV t χ).val = e.symm (AddMonoidAlgebra.single (f χ) 1)) →
          (lift t (s ≫ y)).left.appTop.hom u = e.symm (AddMonoidAlgebra.mapDomainRingHom _ f g) := fun f t ht =>
        hg U s t (e.symm.toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom _ f))
          (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [ht]; simp)
      obtain ⟨t₁, ht₁⟩ := exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inl X X))))
      obtain ⟨t₂, ht₂⟩ := exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inr X X))))
      have a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inl X X χ) 1) := ht₁
      have a₂ : ∀ χ, (chV t₂ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inr X X χ) 1) := ht₂
      apply e.symm.injective
      rw [map_mul, ← key _ t₁ a₁, ← key _ t₂ a₂, ← hm, key]
      intro χ
      rw [chV_mul, Units.val_mul, a₁, a₂, ← map_mul, AddMonoidAlgebra.single_mul_single]
      simp
    · obtain ⟨U, s, e, -, he, -⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra (Γ(W.left, ⊤) ⧸ I) X)
        (AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk I))
      obtain ⟨t₁, ht₁⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
      have a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single χ 1) := ht₁
      have hU : ∃ s, s ≫ red J = U.hom := (RingPoint.exists_comp_red_iff J U).2 fun a ha => by
        apply e.injective
        rw [← RingPoint.appTop_strMap s, he, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero, map_zero]
      have k := hg U s t₁ (e.symm.toRingHom.comp (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I)))
        (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [a₁]; simp)
      apply e.symm.injective
      rw [map_one]
      exact k.symm.trans (h₁ U hU _ _)
  have k := hg W (𝟙 W) t (AddMonoidAlgebra.liftNCRingHom (RingHom.id _)
    ((Units.coeHom _).comp (splitTorusPointsEquiv _ X W t)) fun _ _ => Commute.all _ _)
    (fun b => by simp) (fun χ => by simp [chV])
  rwa [Category.id_comp, one, map_one] at k

/- English proof (translation)
Introduce `A _ J hJ X _ Y u hm h₁`. Establish `hm' : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y), (lift (t * t') y).left.appTop.hom u.val = (lift t y).left.appTop.hom u.val * (lift t' y).left.appTop.hom u.val` using `fun Z t t' y => by`. Establish `e : Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom u = Units.map (lift t y).left.appTop.hom.toMonoidHom u * Units.map (lift t' y).left.appTop.hom.toMonoidHom u` using `unit_ext fun z _ => by rw [map_mul, ← gm_top, ← gm_top, ← gm_top, hm]`. Conclude with `congrArg Units.val e`. Establish `h₁' : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y), (lift t y).left.appTop.hom u.val = 1` using `fun Z hZ t y => by`.

Establish `e : Units.map (lift t y).left.appTop.hom.toMonoidHom u = 1` using `unit_ext fun z _ => by rw [map_one, ← gm_top, h₁ Z hZ]`. Conclude with `congrArg Units.val e`. Use `unit_ext fun z _ => ?_` and prove the remaining obligations. Set `𝒰` to `(splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left.affineCover`. Take `⟨i, w, rfl⟩` from `𝒰.exists_eq z`.

Set `W : Over (Spec (CommRingCat.of A))` to `Over.mk (𝒰.f i ≫ (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).hom)`. Use `haveI : IsAffine W.left := inferInstanceAs (IsAffine (𝒰.X i))`. Set `κ : W ⟶ splitTorus (Spec (CommRingCat.of A)) X ⊗ Y` to `Over.homMk (𝒰.f i) rfl`. Establish `e` using `eq_one_affine J hJ u.val hm' h₁' (κ ≫ fst _ _) (κ ≫ snd _ _)`. Rewrite `e` using `[lift_comp_fst_snd]`.

Establish `e' : Units.map (𝒰.f i).appTop.hom.toMonoidHom u = 1` using `Units.ext e`. Use `gm_inj (U := ⊤) (U' := ⊤) (𝒰.f i) w trivial trivial ?_` and prove the remaining obligations. Rewrite using `[gm_top, e', map_one, map_one]`.
-/
theorem unit_eq_one : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (Y : Over (Spec (CommRingCat.of A))) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ), (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift (t * t') y).left z ⊤ u = gm (lift t y).left z ⊤ u * gm (lift t' y).left z ⊤ u) → (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t y).left z ⊤ u = 1) → u = 1 := by
  intro A _ J hJ X _ Y u hm h₁
  have hm' : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u.val =
        (lift t y).left.appTop.hom u.val * (lift t' y).left.appTop.hom u.val := fun Z t t' y => by
    have e : Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom u =
        Units.map (lift t y).left.appTop.hom.toMonoidHom u * Units.map (lift t' y).left.appTop.hom.toMonoidHom u :=
      unit_ext fun z _ => by rw [map_mul, ← gm_top, ← gm_top, ← gm_top, hm]
    exact congrArg Units.val e
  have h₁' : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) →
      ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y), (lift t y).left.appTop.hom u.val = 1 := fun Z hZ t y => by
    have e : Units.map (lift t y).left.appTop.hom.toMonoidHom u = 1 :=
      unit_ext fun z _ => by rw [map_one, ← gm_top, h₁ Z hZ]
    exact congrArg Units.val e
  refine unit_ext fun z _ => ?_
  let 𝒰 := (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left.affineCover
  obtain ⟨i, w, rfl⟩ := 𝒰.exists_eq z
  let W : Over (Spec (CommRingCat.of A)) := Over.mk (𝒰.f i ≫ (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).hom)
  haveI : IsAffine W.left := inferInstanceAs (IsAffine (𝒰.X i))
  let κ : W ⟶ splitTorus (Spec (CommRingCat.of A)) X ⊗ Y := Over.homMk (𝒰.f i) rfl
  have e := eq_one_affine J hJ u.val hm' h₁' (κ ≫ fst _ _) (κ ≫ snd _ _)
  rw [lift_comp_fst_snd] at e
  have e' : Units.map (𝒰.f i).appTop.hom.toMonoidHom u = 1 := Units.ext e
  refine gm_inj (U := ⊤) (U' := ⊤) (𝒰.f i) w trivial trivial ?_
  rw [gm_top, e', map_one, map_one]

end GlobalTheory.UU.UnitRigid
end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorsDescent

/- English proof (translation)
Take `⟨φ, hφ⟩` from `Spec.map_surjective (f ≫ X.isoSpec.hom)`. Establish `hfix : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) a, σ (φ a) = φ a`. Introduce `σ a`. Establish `h1 : Spec.map (φ ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom) = Spec.map φ`. Rewrite using `[Spec.map_comp, hφ, ← Category.assoc]`.

Conclude with `congrArg (· ≫ X.isoSpec.hom) (hf σ)`. Conclude with `congrArg (fun g => g.hom a) (Spec.map_injective h1)`. Establish `hmem : ∀ a, φ a ∈ Set.range (algebraMap K (AlgebraicClosure K))`. Introduce `a`. Establish `hb` using `InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))`.

Establish `h2 : φ a ∈ IntermediateField.fixedField (⊥ : IntermediateField K (AlgebraicClosure K)).fixingSubgroup` using `(IntermediateField.mem_fixedField_iff _ _).2 fun σ _ => hfix σ a`. Rewrite `h2` using `[hb]`. Conclude with `IntermediateField.mem_bot.1 h2`. Set `jb` to `algebraMap K (AlgebraicClosure K)`. Set `e` to `RingEquiv.ofBijective jb.rangeRestrict ⟨fun a b h => jb.injective (congrArg Subtype.val h), jb.rangeRestrict_surjective⟩`.

Set `ψ : Γ(X, ⊤) →+* K` to `e.symm.toRingHom.comp (φ.hom.codRestrict jb.range hmem)`. Establish `hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom jb = φ`. Use extensionality with `r`. Conclude with `congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict jb.range hmem r))`. Use `⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, spMap, ← Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.
-/
theorem descend_point {K : Type} [Field K] [CharZero K] (X : Scheme.{0}) [IsAffine X]
    (f : Sp (AlgebraicClosure K) ⟶ X)
    (hf : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, spMap σ.toAlgHom.toRingHom ≫ f = f) :
    ∃ g : Sp K ⟶ X, spMap (algebraMap K (AlgebraicClosure K)) ≫ g = f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (f ≫ X.isoSpec.hom)
  have hfix : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) a, σ (φ a) = φ a := by
    intro σ a
    have h1 : Spec.map (φ ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom) = Spec.map φ := by
      rw [Spec.map_comp, hφ, ← Category.assoc]
      exact congrArg (· ≫ X.isoSpec.hom) (hf σ)
    exact congrArg (fun g => g.hom a) (Spec.map_injective h1)
  have hmem : ∀ a, φ a ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    intro a
    have hb := InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))
    have h2 : φ a ∈ IntermediateField.fixedField (⊥ : IntermediateField K (AlgebraicClosure K)).fixingSubgroup :=
      (IntermediateField.mem_fixedField_iff _ _).2 fun σ _ => hfix σ a
    rw [hb] at h2
    exact IntermediateField.mem_bot.1 h2
  let jb := algebraMap K (AlgebraicClosure K)
  let e := RingEquiv.ofBijective jb.rangeRestrict
    ⟨fun a b h => jb.injective (congrArg Subtype.val h), jb.rangeRestrict_surjective⟩
  let ψ : Γ(X, ⊤) →+* K := e.symm.toRingHom.comp (φ.hom.codRestrict jb.range hmem)
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom jb = φ := by
    ext r
    exact congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict jb.range hmem r))
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_⟩
  rw [← Category.assoc, spMap, ← Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/- English proof (translation)
Introduce `R _ _ _ G _ _ G' _ _ A gen inc pr n hgen hinc hpr hret hn hfix`. Use `haveI := hgen`. Use `haveI := hinc`. Use `haveI := hpr`. Introduce `Ω _ _ κ x hx`.

Use `letI : Algebra (FractionRing R) Ω := κ.toAlgebra`. Set `jb` to `algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))`. Set `i₁ : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] Ω` to `IsAlgClosed.lift`. Establish `hκ : κ = i₁.toRingHom.comp jb`. Use extensionality with `a`.

Conclude with `(i₁.commutes a).symm`. Establish `hκs : spMap κ = spMap i₁.toRingHom ≫ spMap jb`. Rewrite using `[hκ, spMap, spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hip : inc.left ≫ pr.left = 𝟙 _` using `by rw [← Over.comp_left, hret, Over.id_left]`.

Establish `hpb` using `isGrpPullback_pullback G' (jK R)`. Set `T : Over (Sp (FractionRing R))` to `Over.mk (spMap κ)`. Set `x1 : Over.mk (T.hom ≫ jK R) ⟶ G'` to `x ≫ inc`. Establish `hx1 : x1 ^ n = 1` using `by show (x ≫ inc) ^ n = 1`. Rewrite using `[← MonObj.pow_comp, hx, MonObj.one_comp]`.

Set `x2` to `(ObjPull.pushEquiv hpb T).symm x1`. Establish `hx2 : x2 ^ n = 1` using `by simp only [x2, ← map_pow, hx1, map_one]`. Establish `hx2l : x2.left ≫ pullback.fst G'.hom (jK R) = x.left ≫ inc.left` using `ObjPull.pushEquiv_symm_left hpb T x1`. Set `x3` to `x2 ≫ gen.hom`. Establish `hx3 : x3 ^ n = 1` using `by rw [← MonObj.pow_comp, hx2, MonObj.one_comp]`.

Establish `hmul : x3 ≫ mulN A.A n = toUnit _ ≫ η`. Rewrite using `[GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx3, Hom.one_def]`. Set `t : T ⟶ torsion A.A n` to `pullback.lift x3 (toUnit _) hmul`. Establish `ht : t ≫ torsion.ι A.A n = x3` using `pullback.lift_fst _ _ _`. Establish `hfin` using `(AbTorsionAnyBase.isFinite_and_flat_torsion _ A.A A.isAb n hn).1`.

Take `⟨K', _, _, _, H⟩` from `TorsRational.exists_ext_points (FractionRing R) (torsion A.A n) hfin`. Set `i' : K' →ₐ[FractionRing R] AlgebraicClosure (FractionRing R)` to `IsAlgClosed.lift`. Use `letI : Algebra K' (AlgebraicClosure (FractionRing R)) := i'.toRingHom.toAlgebra`. Use `haveI : IsScalarTower (FractionRing R) K' (AlgebraicClosure (FractionRing R)) := IsScalarTower.of_algebraMap_eq fun a => (i'.commutes a).symm`. Take `⟨w, hw⟩` from `H (AlgebraicClosure (FractionRing R)) Ω i₁.toRingHom t.left (by`.

Rewrite using `[Over.w t]`. Use `show spMap κ = _`. Rewrite using `[hκ])`. Establish `hw2 : w ≫ (torsion A.A n).hom = spMap jb`. Use `spec_map_field_cancel i₁.toRingHom _ _ ?_` and prove the remaining obligations.

Rewrite using `[← Category.assoc, hw, Over.w t]`. Conclude with `hκs`. Set `Tb : Over (Sp (FractionRing R))` to `Over.mk (spMap jb)`. Set `t₀ : Tb ⟶ torsion A.A n` to `Over.homMk w hw2`. Set `g₀ : Tb ⟶ (Over.pullback (jK R)).obj G'` to `t₀ ≫ torsion.ι A.A n ≫ gen.inv`.

Set `y₁` to `ObjPull.pushEquiv hpb Tb g₀`. Establish `hy₁l : y₁.left = w ≫ (torsion.ι A.A n).left ≫ gen.inv.left ≫ pullback.fst G'.hom (jK R)`. Rewrite using `[ObjPull.pushEquiv_left]`. Simplify using `only [g₀, t₀, Over.comp_left, Over.homMk_left, Category.assoc]`. Establish `hkey : spMap i₁.toRingHom ≫ y₁.left = x.left ≫ inc.left`.

Establish `hgh : gen.hom.left ≫ gen.inv.left = 𝟙 _` using `by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]`. Rewrite using `[hy₁l, ← Category.assoc, hw, ← hx2l, ← Category.assoc, ← Over.comp_left, ht]`. Use `show (x2.left ≫ gen.hom.left) ≫ gen.inv.left ≫ _ = _`. Rewrite using `[Category.assoc, ← Category.assoc gen.hom.left, hgh, Category.id_comp]`. Set `y₀ : Over.mk (Tb.hom ≫ jK R) ⟶ G` to `y₁ ≫ pr`.

Establish `hy₀ : y₀ ^ n = 1`. Establish `h0 : (t₀ ≫ torsion.ι A.A n) ≫ mulN A.A n = toUnit _ ≫ η`. Establish `hc : torsion.ι A.A n ≫ mulN A.A n = pullback.snd (mulN A.A n) η[A.A] ≫ η` using `pullback.condition`. Rewrite using `[Category.assoc, hc]`. Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ η) (toUnit_unique _ _))`.

Rewrite `h0` using `[GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]`. Establish `h1 : g₀ ^ n = 1` using `by show (t₀ ≫ torsion.ι A.A n ≫ gen.inv) ^ n = 1`. Rewrite using `[← Category.assoc, ← MonObj.pow_comp, h0, ← Hom.one_def, MonObj.one_comp]`. Use `show (y₁ ≫ pr) ^ n = 1`. Rewrite using `[← MonObj.pow_comp, ← map_pow, h1, map_one, MonObj.one_comp]`.

Establish `hy₁inc : y₁.left ≫ pr.left ≫ inc.left = y₁.left`. Use `spec_map_field_cancel i₁.toRingHom _ _ ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hkey, Category.assoc, reassoc_of% hip]`. Establish `hy₁fix : ∀ σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R), spMap σ.toAlgHom.toRingHom ≫ y₁.left = y₁.left`. Introduce `σ`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Category.assoc, hy₁inc]`. Use `_ = (y₁.left ≫ pr.left) ≫ inc.left := by`. Rewrite using `[← Category.assoc]`. Conclude with `congrArg (· ≫ inc.left) (hfix σ y₀ hy₀)`.

Use `_ = y₁.left := by rw [Category.assoc, hy₁inc]`. Use `haveI : Mono (torsion.ι A.A n) := inferInstanceAs (Mono (pullback.fst _ _))`. Establish `hwfix : ∀ σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R), spMap σ.toAlgHom.toRingHom ≫ w = w`. Introduce `σ`. Establish `hσ : spMap σ.toAlgHom.toRingHom ≫ Tb.hom = Tb.hom` using `by show spMap _ ≫ spMap jb = spMap jb`.

Rewrite using `[spMap, spMap, ← Spec.map_comp]`. Use `congr 2`. Use extensionality with `a`. Conclude with `σ.commutes a`. Set `eσ : Tb ⟶ Tb` to `Over.homMk (spMap σ.toAlgHom.toRingHom) hσ`.

Establish `h1 : eσ ≫ g₀ = g₀`. Apply `(ObjPull.pushEquiv hpb Tb).injective` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[ObjPull.pushEquiv_left, ObjPull.pushEquiv_left, Over.comp_left, Category.assoc]`. Conclude with `hy₁fix σ`.

Establish `h2 : eσ ≫ t₀ = t₀`. Rewrite using `[← cancel_mono (torsion.ι A.A n ≫ gen.inv)]`. Simplify `h1` using `only [Category.assoc]`. Conclude with `congrArg (fun f => f.left) h2`. Use `haveI := hfin`.

Use `haveI : IsAffine (torsion A.A n).left := isAffine_of_isAffineHom (torsion A.A n).hom`. Take `⟨w₁, hw₁⟩` from `descend_point (torsion A.A n).left w hwfix`. Establish `hw₁s : w₁ ≫ (torsion A.A n).hom = 𝟙 _`. Use `spec_map_field_cancel jb _ _ ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hw₁, hw2, Category.comp_id]`.

Set `z : Sp (FractionRing R) ⟶ G'.left` to `w₁ ≫ (torsion.ι A.A n).left ≫ gen.inv.left ≫ pullback.fst G'.hom (jK R)`. Establish `hz : z ≫ G'.hom = jK R`. Simplify using `only [z, Category.assoc]`. Establish `hgi : gen.inv.left ≫ pullback.snd G'.hom (jK R) = A.A.hom` using `Over.w gen.inv`. Rewrite using `[pullback.condition, ← Category.assoc gen.inv.left, hgi, ← Category.assoc (torsion.ι A.A n).left, Over.w (torsion.ι A.A n), ← Category.assoc w₁, hw₁s, Category.id_comp]`.

Use `⟨Over.homMk z hz ≫ pr, ?_⟩` and prove the remaining obligations. Establish `hz' : spMap κ ≫ z = x.left ≫ inc.left`. Establish `e1 : spMap κ ≫ z = spMap i₁.toRingHom ≫ y₁.left` using `by show spMap κ ≫ (w₁ ≫ _ ≫ _ ≫ _) = _`. Rewrite using `[hκs, Category.assoc, ← Category.assoc (spMap jb), hw₁, hy₁l]`. Rewrite using `[e1, hkey]`.

Use `show x.left = spMap κ ≫ z ≫ pr.left`. Rewrite using `[← Category.assoc, hz', Category.assoc, hip, Category.comp_id]`.
-/
theorem torsRat_of_retract_galoisFixed : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G' ≅ A.A) (inc : G ⟶ G') (pr : G' ⟶ G) (n : ℕ), IsMonHom gen.hom → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → 1 ≤ n → (∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left) → TorsRat G n := by
  intro R _ _ _ G _ _ G' _ _ A gen inc pr n hgen hinc hpr hret hn hfix
  haveI := hgen
  haveI := hinc
  haveI := hpr
  intro Ω _ _ κ x hx
  letI : Algebra (FractionRing R) Ω := κ.toAlgebra
  let jb := algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))
  let i₁ : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] Ω := IsAlgClosed.lift
  have hκ : κ = i₁.toRingHom.comp jb := by
    ext a
    exact (i₁.commutes a).symm
  have hκs : spMap κ = spMap i₁.toRingHom ≫ spMap jb := by
    rw [hκ, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hip : inc.left ≫ pr.left = 𝟙 _ := by rw [← Over.comp_left, hret, Over.id_left]

  have hpb := isGrpPullback_pullback G' (jK R)
  let T : Over (Sp (FractionRing R)) := Over.mk (spMap κ)
  let x1 : Over.mk (T.hom ≫ jK R) ⟶ G' := x ≫ inc
  have hx1 : x1 ^ n = 1 := by
    show (x ≫ inc) ^ n = 1
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  let x2 := (ObjPull.pushEquiv hpb T).symm x1
  have hx2 : x2 ^ n = 1 := by simp only [x2, ← map_pow, hx1, map_one]
  have hx2l : x2.left ≫ pullback.fst G'.hom (jK R) = x.left ≫ inc.left := ObjPull.pushEquiv_symm_left hpb T x1
  let x3 := x2 ≫ gen.hom
  have hx3 : x3 ^ n = 1 := by rw [← MonObj.pow_comp, hx2, MonObj.one_comp]
  have hmul : x3 ≫ mulN A.A n = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx3, Hom.one_def]
  let t : T ⟶ torsion A.A n := pullback.lift x3 (toUnit _) hmul
  have ht : t ≫ torsion.ι A.A n = x3 := pullback.lift_fst _ _ _

  have hfin := (AbTorsionAnyBase.isFinite_and_flat_torsion _ A.A A.isAb n hn).1
  obtain ⟨K', _, _, _, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A n) hfin
  let i' : K' →ₐ[FractionRing R] AlgebraicClosure (FractionRing R) := IsAlgClosed.lift
  letI : Algebra K' (AlgebraicClosure (FractionRing R)) := i'.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) K' (AlgebraicClosure (FractionRing R)) :=
    IsScalarTower.of_algebraMap_eq fun a => (i'.commutes a).symm
  obtain ⟨w, hw⟩ := H (AlgebraicClosure (FractionRing R)) Ω i₁.toRingHom t.left (by
    rw [Over.w t]
    show spMap κ = _
    rw [hκ])
  have hw2 : w ≫ (torsion A.A n).hom = spMap jb := by
    refine spec_map_field_cancel i₁.toRingHom _ _ ?_
    rw [← Category.assoc, hw, Over.w t]
    exact hκs
  let Tb : Over (Sp (FractionRing R)) := Over.mk (spMap jb)
  let t₀ : Tb ⟶ torsion A.A n := Over.homMk w hw2
  let g₀ : Tb ⟶ (Over.pullback (jK R)).obj G' := t₀ ≫ torsion.ι A.A n ≫ gen.inv
  let y₁ := ObjPull.pushEquiv hpb Tb g₀
  have hy₁l : y₁.left = w ≫ (torsion.ι A.A n).left ≫ gen.inv.left ≫ pullback.fst G'.hom (jK R) := by
    rw [ObjPull.pushEquiv_left]
    simp only [g₀, t₀, Over.comp_left, Over.homMk_left, Category.assoc]
  have hkey : spMap i₁.toRingHom ≫ y₁.left = x.left ≫ inc.left := by
    have hgh : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    rw [hy₁l, ← Category.assoc, hw, ← hx2l, ← Category.assoc, ← Over.comp_left, ht]
    show (x2.left ≫ gen.hom.left) ≫ gen.inv.left ≫ _ = _
    rw [Category.assoc, ← Category.assoc gen.hom.left, hgh, Category.id_comp]

  let y₀ : Over.mk (Tb.hom ≫ jK R) ⟶ G := y₁ ≫ pr
  have hy₀ : y₀ ^ n = 1 := by
    have h0 : (t₀ ≫ torsion.ι A.A n) ≫ mulN A.A n = toUnit _ ≫ η := by
      have hc : torsion.ι A.A n ≫ mulN A.A n = pullback.snd (mulN A.A n) η[A.A] ≫ η := pullback.condition
      rw [Category.assoc, hc]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ η) (toUnit_unique _ _))
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id] at h0
    have h1 : g₀ ^ n = 1 := by
      show (t₀ ≫ torsion.ι A.A n ≫ gen.inv) ^ n = 1
      rw [← Category.assoc, ← MonObj.pow_comp, h0, ← Hom.one_def, MonObj.one_comp]
    show (y₁ ≫ pr) ^ n = 1
    rw [← MonObj.pow_comp, ← map_pow, h1, map_one, MonObj.one_comp]
  have hy₁inc : y₁.left ≫ pr.left ≫ inc.left = y₁.left := by
    refine spec_map_field_cancel i₁.toRingHom _ _ ?_
    rw [← Category.assoc, hkey, Category.assoc, reassoc_of% hip]
  have hy₁fix : ∀ σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R),
      spMap σ.toAlgHom.toRingHom ≫ y₁.left = y₁.left := by
    intro σ
    calc spMap σ.toAlgHom.toRingHom ≫ y₁.left = spMap σ.toAlgHom.toRingHom ≫ (y₁.left ≫ pr.left) ≫ inc.left := by
          rw [Category.assoc, hy₁inc]
      _ = (y₁.left ≫ pr.left) ≫ inc.left := by
          rw [← Category.assoc]
          exact congrArg (· ≫ inc.left) (hfix σ y₀ hy₀)
      _ = y₁.left := by rw [Category.assoc, hy₁inc]
  haveI : Mono (torsion.ι A.A n) := inferInstanceAs (Mono (pullback.fst _ _))
  have hwfix : ∀ σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R),
      spMap σ.toAlgHom.toRingHom ≫ w = w := by
    intro σ
    have hσ : spMap σ.toAlgHom.toRingHom ≫ Tb.hom = Tb.hom := by
      show spMap _ ≫ spMap jb = spMap jb
      rw [spMap, spMap, ← Spec.map_comp]
      congr 2
      ext a
      exact σ.commutes a
    let eσ : Tb ⟶ Tb := Over.homMk (spMap σ.toAlgHom.toRingHom) hσ
    have h1 : eσ ≫ g₀ = g₀ := by
      apply (ObjPull.pushEquiv hpb Tb).injective
      apply Over.OverMorphism.ext
      rw [ObjPull.pushEquiv_left, ObjPull.pushEquiv_left, Over.comp_left, Category.assoc]
      exact hy₁fix σ
    have h2 : eσ ≫ t₀ = t₀ := by
      rw [← cancel_mono (torsion.ι A.A n ≫ gen.inv)]
      simpa only [Category.assoc] using h1
    exact congrArg (fun f => f.left) h2

  haveI := hfin
  haveI : IsAffine (torsion A.A n).left := isAffine_of_isAffineHom (torsion A.A n).hom
  obtain ⟨w₁, hw₁⟩ := descend_point (torsion A.A n).left w hwfix
  have hw₁s : w₁ ≫ (torsion A.A n).hom = 𝟙 _ := by
    refine spec_map_field_cancel jb _ _ ?_
    rw [← Category.assoc, hw₁, hw2, Category.comp_id]
  let z : Sp (FractionRing R) ⟶ G'.left :=
    w₁ ≫ (torsion.ι A.A n).left ≫ gen.inv.left ≫ pullback.fst G'.hom (jK R)
  have hz : z ≫ G'.hom = jK R := by
    simp only [z, Category.assoc]
    have hgi : gen.inv.left ≫ pullback.snd G'.hom (jK R) = A.A.hom := Over.w gen.inv
    rw [pullback.condition, ← Category.assoc gen.inv.left, hgi, ← Category.assoc (torsion.ι A.A n).left,
      Over.w (torsion.ι A.A n), ← Category.assoc w₁, hw₁s, Category.id_comp]
  refine ⟨Over.homMk z hz ≫ pr, ?_⟩
  have hz' : spMap κ ≫ z = x.left ≫ inc.left := by
    have e1 : spMap κ ≫ z = spMap i₁.toRingHom ≫ y₁.left := by
      show spMap κ ≫ (w₁ ≫ _ ≫ _ ≫ _) = _
      rw [hκs, Category.assoc, ← Category.assoc (spMap jb), hw₁, hy₁l]
    rw [e1, hkey]
  show x.left = spMap κ ≫ z ≫ pr.left
  rw [← Category.assoc, hz', Category.assoc, hip, Category.comp_id]

end GlobalTheory.TorsDescent

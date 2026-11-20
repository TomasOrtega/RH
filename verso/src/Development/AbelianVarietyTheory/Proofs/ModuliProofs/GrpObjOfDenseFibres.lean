import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreGrp

/- English proof (translation)
Establish `: IsReduced X.left` using `GlobalTheory.isReduced_of_smooth_of_isReduced X.hom`. Use `choose U j hj hfg using h`. Set `incl : (∐ fun q : Sg => pullback X.hom (j q.1 q.2)) ⟶ X.left` to `Sigma.desc fun q : Sg => pullback.fst X.hom (j q.1 q.2)`. Establish `hincl : ∀ q : Sg, Sigma.ι (fun q : Sg => pullback X.hom (j q.1 q.2)) q ≫ incl = pullback.fst X.hom (j q.1 q.2)` using `fun q => Sigma.ι_desc _ q`. Establish `hdense : Dense (X.hom ⁻¹' Sg)` using `hSg.preimage X.hom.isOpenMap`.

Establish `: IsDominant incl`. Use `⟨Dense.mono ?_ hdense⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : x ∈ Set.range (pullback.fst X.hom (j _ hx))`. Rewrite using `[Scheme.Pullback.range_fst]`.

Conclude with `hj _ hx`. Take `⟨y, hy⟩` from `hx'`. Use `⟨Sigma.ι (fun q : Sg => pullback X.hom (j q.1 q.2)) ⟨_, hx⟩ y, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hincl]`. Conclude with `hy`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `ext_of_isDominant_of_isSeparated Y.hom (by rw [Over.w f, Over.w g]) incl ?_` and prove the remaining obligations. Use `Sigma.hom_ext _ _ fun q => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hincl, ← Category.assoc, hincl]`. Establish `key` using `hfg q.1 q.2 (Over.mk (pullback.snd X.hom (j q.1 q.2))) (Over.homMk (pullback.fst X.hom (j q.1 q.2)) (by simp only [Over.mk_hom]; exact pullback.condition))`.

Conclude with `congrArg CommaMorphism.left key`.
-/
theorem hom_ext_of_fibres {S : Scheme.{0}} [IsReduced S] {Sg : Set S} (hSg : Dense Sg) {X Y : Over S}
    [Smooth X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ p ∈ Sg, ∃ (U : Scheme.{0}) (j : U ⟶ S), p ∈ Set.range j ∧
      ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have : IsReduced X.left := GlobalTheory.isReduced_of_smooth_of_isReduced X.hom
  choose U j hj hfg using h
  let incl : (∐ fun q : Sg => pullback X.hom (j q.1 q.2)) ⟶ X.left :=
    Sigma.desc fun q : Sg => pullback.fst X.hom (j q.1 q.2)
  have hincl : ∀ q : Sg, Sigma.ι (fun q : Sg => pullback X.hom (j q.1 q.2)) q ≫ incl =
      pullback.fst X.hom (j q.1 q.2) := fun q => Sigma.ι_desc _ q
  have hdense : Dense (X.hom ⁻¹' Sg) := hSg.preimage X.hom.isOpenMap
  have : IsDominant incl := by
    refine ⟨Dense.mono ?_ hdense⟩
    intro x hx
    have hx' : x ∈ Set.range (pullback.fst X.hom (j _ hx)) := by
      rw [Scheme.Pullback.range_fst]
      exact hj _ hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨Sigma.ι (fun q : Sg => pullback X.hom (j q.1 q.2)) ⟨_, hx⟩ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hincl]
    exact hy
  apply Over.OverMorphism.ext
  refine ext_of_isDominant_of_isSeparated Y.hom (by rw [Over.w f, Over.w g]) incl ?_
  refine Sigma.hom_ext _ _ fun q => ?_
  rw [← Category.assoc, hincl, ← Category.assoc, hincl]
  have key := hfg q.1 q.2 (Over.mk (pullback.snd X.hom (j q.1 q.2)))
    (Over.homMk (pullback.fst X.hom (j q.1 q.2)) (by simp only [Over.mk_hom]; exact pullback.condition))
  exact congrArg CommaMorphism.left key

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Smooth (pullback.fst P.hom Q.hom ≫ P.hom)`. Use `infer_instance`.
-/
private theorem smooth_tensor_hom {S : Scheme.{0}} (P Q : Over S) [Smooth P.hom] [Smooth Q.hom] :
    Smooth (P ⊗ Q).hom := by
  change Smooth (pullback.fst P.hom Q.hom ≫ P.hom)
  infer_instance

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Smooth (𝟙 S)`. Use `infer_instance`.
-/
private theorem smooth_tensorUnit_hom (S : Scheme.{0}) : Smooth (𝟙_ (Over S)).hom := by
  change Smooth (𝟙 S)
  infer_instance

/- English proof (translation)
Use `hom_ext_of_fibres hSg fun p hp => ?_` and prove the remaining obligations. Take `⟨K, _, x, A, _, φ, hx, hc, pb, hm, hi, he⟩` from `hfib p hp`. Conclude with `⟨Sp K, x, hx, H K x A φ pb hm hi he⟩`.
-/
private theorem eq_of_points_lemma_3 {R : Type} [CommRing R] [IsReduced R] {Z : Over (Sp R)} [IsSeparated Z.hom]
    {m : Z ⊗ Z ⟶ Z} {i : Z ⟶ Z} {e : 𝟙_ (Over (Sp R)) ⟶ Z} {Sg : Set (Sp R)} (hSg : Dense Sg)
    (hfib : ∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (A : Over (Sp K)) (_ : GrpObj A) (φ : A.left ⟶ Z.left), p ∈ Set.range x ∧ IsCommMonObj A ∧ IsPullback φ A.hom Z.hom x ∧ (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) ∧ φ ≫ i.left = (ι[A]).left ≫ φ ∧ x ≫ e.left = (η[A]).left ≫ φ)
    {P : Over (Sp R)} [Smooth P.hom] {u v : P ⟶ Z}
    (H : ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
      (φ : A.left ⟶ Z.left), IsPullback φ A.hom Z.hom x →
      (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) →
      φ ≫ i.left = (ι[A]).left ≫ φ → x ≫ e.left = (η[A]).left ≫ φ →
      ∀ (T : Over (Sp K)) (t : Over.mk (T.hom ≫ x) ⟶ P), t ≫ u = t ≫ v) : u = v := by
  refine hom_ext_of_fibres hSg fun p hp => ?_
  obtain ⟨K, _, x, A, _, φ, hx, hc, pb, hm, hi, he⟩ := hfib p hp
  exact ⟨Sp K, x, hx, H K x A φ pb hm hi he⟩

end GlobalTheory.FibreGrp

namespace GlobalTheory

open GrpDense FibreGrp

/- English proof (translation)
Introduce `R _ _ Z m i e Sg hSg hsm hpr hgc hfib`. Establish `: Smooth Z.hom` using `hsm`. Establish `: IsProper Z.hom` using `hpr`. Establish `: Smooth (𝟙_ (Over (Sp R))).hom` using `smooth_tensorUnit_hom (Sp R)`. Establish `: Smooth (Z ⊗ Z).hom` using `smooth_tensor_hom Z Z`.

Establish `: Smooth (𝟙_ (Over (Sp R)) ⊗ Z).hom` using `smooth_tensor_hom _ _`. Establish `: Smooth (Z ⊗ 𝟙_ (Over (Sp R))).hom` using `smooth_tensor_hom _ _`. Establish `: Smooth ((Z ⊗ Z) ⊗ Z).hom` using `smooth_tensor_hom _ _`. Establish `one_mul' : e ▷ Z ≫ m = (λ_ Z).hom`. Use `eq_of_points_lemma_3 hSg hfib ?_` and prove the remaining obligations.

Introduce `K _ x A _ _ φ pb hm hi he T t`. Take `⟨c, hc⟩` from `GrpDense.pushPt_surjective pb T (t ≫ snd (𝟙_ (Over (Sp R))) Z)`. Rewrite using `[← lift_comp_fst_snd t, toUnit_unique (t ≫ fst (𝟙_ (Over (Sp R))) Z) (toUnit _), lift_whiskerRight_assoc, lift_leftUnitor_hom, ← hc, GrpDense.pushPt_one pb.w he T, GrpDense.pushPt_mul pb.w hm, _root_.one_mul]`. Establish `mul_one' : Z ◁ e ≫ m = (ρ_ Z).hom`. Use `eq_of_points_lemma_3 hSg hfib ?_` and prove the remaining obligations.

Introduce `K _ x A _ _ φ pb hm hi he T t`. Take `⟨c, hc⟩` from `GrpDense.pushPt_surjective pb T (t ≫ fst Z (𝟙_ (Over (Sp R))))`. Rewrite using `[← lift_comp_fst_snd t, toUnit_unique (t ≫ snd Z (𝟙_ (Over (Sp R)))) (toUnit _), lift_whiskerLeft_assoc, lift_rightUnitor_hom, ← hc, GrpDense.pushPt_one pb.w he T, GrpDense.pushPt_mul pb.w hm, _root_.mul_one]`. Establish `mul_assoc' : m ▷ Z ≫ m = (α_ Z Z Z).hom ≫ Z ◁ m ≫ m`. Use `eq_of_points_lemma_3 hSg hfib ?_` and prove the remaining obligations.

Introduce `K _ x A _ _ φ pb hm hi he T t`. Take `⟨a, ha⟩` from `GrpDense.pushPt_surjective pb T (t ≫ fst (Z ⊗ Z) Z ≫ fst Z Z)`. Take `⟨b, hb⟩` from `GrpDense.pushPt_surjective pb T (t ≫ fst (Z ⊗ Z) Z ≫ snd Z Z)`. Take `⟨c, hc⟩` from `GrpDense.pushPt_surjective pb T (t ≫ snd (Z ⊗ Z) Z)`. Establish `ht : t = lift (lift (pushPt pb.w a) (pushPt pb.w b)) (pushPt pb.w c)`.

Rewrite using `[ha, hb, hc]`. Simplify using `only [← Category.assoc, lift_comp_fst_snd]`. Rewrite using `[ht]`. Simplify using `only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, GrpDense.pushPt_mul pb.w hm, _root_.mul_assoc]`. Establish `left_inv' : lift i (𝟙 Z) ≫ m = toUnit Z ≫ e`.

Use `eq_of_points_lemma_3 hSg hfib ?_` and prove the remaining obligations. Introduce `K _ x A _ _ φ pb hm hi he T t`. Take `⟨c, rfl⟩` from `GrpDense.pushPt_surjective pb T t`. Rewrite using `[comp_lift_assoc, Category.comp_id, GrpDense.pushPt_inv pb.w hi, GrpDense.pushPt_mul pb.w hm, ← Category.assoc (pushPt pb.w c) (toUnit Z) e, toUnit_unique (pushPt pb.w c ≫ toUnit Z) (toUnit _), GrpDense.pushPt_one pb.w he T, _root_.inv_mul_cancel]`. Establish `right_inv' : lift (𝟙 Z) i ≫ m = toUnit Z ≫ e`.

Use `eq_of_points_lemma_3 hSg hfib ?_` and prove the remaining obligations. Introduce `K _ x A _ _ φ pb hm hi he T t`. Take `⟨c, rfl⟩` from `GrpDense.pushPt_surjective pb T t`. Rewrite using `[comp_lift_assoc, Category.comp_id, GrpDense.pushPt_inv pb.w hi, GrpDense.pushPt_mul pb.w hm, ← Category.assoc (pushPt pb.w c) (toUnit Z) e, toUnit_unique (pushPt pb.w c ≫ toUnit Z) (toUnit _), GrpDense.pushPt_one pb.w he T, _root_.mul_inv_cancel]`. Establish `comm' : (β_ Z Z).hom ≫ m = m`.

Use `eq_of_points_lemma_3 hSg hfib ?_` and prove the remaining obligations. Introduce `K _ x A _ _ φ pb hm hi he T t`. Take `⟨a, ha⟩` from `GrpDense.pushPt_surjective pb T (t ≫ fst Z Z)`. Take `⟨b, hb⟩` from `GrpDense.pushPt_surjective pb T (t ≫ snd Z Z)`. Establish `ht : t = lift (pushPt pb.w a) (pushPt pb.w b)` using `by rw [ha, hb, lift_comp_fst_snd]`.

Rewrite using `[ht, lift_braiding_hom_assoc, GrpDense.pushPt_mul pb.w hm, GrpDense.pushPt_mul pb.w hm, _root_.mul_comm]`. Set `G : GrpObj Z` to `{ one := e, mul := m, one_mul := one_mul', mul_one := mul_one', mul_assoc := mul_assoc', inv := i, left_inv := left_inv', right_inv := right_inv' }`. Use `⟨G, rfl, rfl, rfl, ?_, ?_⟩` and prove the remaining obligations. Conclude with `{ comm := ⟨comm'⟩, smooth := hsm, proper := hpr, geomConnected := hgc }`. Introduce `S' x A _ φ pb hm'`.

Use `⟨pb, fun T a b a₀ b₀ ha hb => ?_⟩` and prove the remaining obligations. Establish `ea : a₀ = pushPt pb.w a` using `Over.OverMorphism.ext ha`. Establish `eb : b₀ = pushPt pb.w b` using `Over.OverMorphism.ext hb`. Substitute `ea eb` using the available equality. Conclude with `congrArg CommaMorphism.left (GrpDense.pushPt_mul pb.w hm' a b)`.
-/
theorem grpObj_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsReduced R] (Z : Over (Sp R)) (m : Z ⊗ Z ⟶ Z) (i : Z ⟶ Z) (e : 𝟙_ (Over (Sp R)) ⟶ Z) (Sg : Set (Sp R)), Dense Sg → Smooth Z.hom → IsProper Z.hom → GeometricallyConnected Z.hom → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (A : Over (Sp K)) (_ : GrpObj A) (φ : A.left ⟶ Z.left), p ∈ Set.range x ∧ IsCommMonObj A ∧ IsPullback φ A.hom Z.hom x ∧ (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) ∧ φ ≫ i.left = (ι[A]).left ≫ φ ∧ x ≫ e.left = (η[A]).left ≫ φ) → ∃ _ : GrpObj Z, μ[Z] = m ∧ η[Z] = e ∧ ι[Z] = i ∧ IsAbelianScheme Z ∧ ∀ (S' : Scheme.{0}) (x : S' ⟶ Sp R) (A : Over S') [GrpObj A] (φ : A.left ⟶ Z.left), IsPullback φ A.hom Z.hom x → (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) → IsGrpPullback A Z x φ := by
  intro R _ _ Z m i e Sg hSg hsm hpr hgc hfib
  have : Smooth Z.hom := hsm
  have : IsProper Z.hom := hpr
  have : Smooth (𝟙_ (Over (Sp R))).hom := smooth_tensorUnit_hom (Sp R)
  have : Smooth (Z ⊗ Z).hom := smooth_tensor_hom Z Z
  have : Smooth (𝟙_ (Over (Sp R)) ⊗ Z).hom := smooth_tensor_hom _ _
  have : Smooth (Z ⊗ 𝟙_ (Over (Sp R))).hom := smooth_tensor_hom _ _
  have : Smooth ((Z ⊗ Z) ⊗ Z).hom := smooth_tensor_hom _ _
  have one_mul' : e ▷ Z ≫ m = (λ_ Z).hom := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd (𝟙_ (Over (Sp R))) Z)
    rw [← lift_comp_fst_snd t, toUnit_unique (t ≫ fst (𝟙_ (Over (Sp R))) Z) (toUnit _),
      lift_whiskerRight_assoc, lift_leftUnitor_hom, ← hc, GrpDense.pushPt_one pb.w he T,
      GrpDense.pushPt_mul pb.w hm, _root_.one_mul]
  have mul_one' : Z ◁ e ≫ m = (ρ_ Z).hom := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst Z (𝟙_ (Over (Sp R))))
    rw [← lift_comp_fst_snd t, toUnit_unique (t ≫ snd Z (𝟙_ (Over (Sp R)))) (toUnit _),
      lift_whiskerLeft_assoc, lift_rightUnitor_hom, ← hc, GrpDense.pushPt_one pb.w he T,
      GrpDense.pushPt_mul pb.w hm, _root_.mul_one]
  have mul_assoc' : m ▷ Z ≫ m = (α_ Z Z Z).hom ≫ Z ◁ m ≫ m := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨a, ha⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst (Z ⊗ Z) Z ≫ fst Z Z)
    obtain ⟨b, hb⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst (Z ⊗ Z) Z ≫ snd Z Z)
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd (Z ⊗ Z) Z)
    have ht : t = lift (lift (pushPt pb.w a) (pushPt pb.w b)) (pushPt pb.w c) := by
      rw [ha, hb, hc]
      simp only [← Category.assoc, lift_comp_fst_snd]
    rw [ht]
    simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
      GrpDense.pushPt_mul pb.w hm, _root_.mul_assoc]
  have left_inv' : lift i (𝟙 Z) ≫ m = toUnit Z ≫ e := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, rfl⟩ := GrpDense.pushPt_surjective pb T t
    rw [comp_lift_assoc, Category.comp_id, GrpDense.pushPt_inv pb.w hi, GrpDense.pushPt_mul pb.w hm,
      ← Category.assoc (pushPt pb.w c) (toUnit Z) e, toUnit_unique (pushPt pb.w c ≫ toUnit Z) (toUnit _),
      GrpDense.pushPt_one pb.w he T, _root_.inv_mul_cancel]
  have right_inv' : lift (𝟙 Z) i ≫ m = toUnit Z ≫ e := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, rfl⟩ := GrpDense.pushPt_surjective pb T t
    rw [comp_lift_assoc, Category.comp_id, GrpDense.pushPt_inv pb.w hi, GrpDense.pushPt_mul pb.w hm,
      ← Category.assoc (pushPt pb.w c) (toUnit Z) e, toUnit_unique (pushPt pb.w c ≫ toUnit Z) (toUnit _),
      GrpDense.pushPt_one pb.w he T, _root_.mul_inv_cancel]
  have comm' : (β_ Z Z).hom ≫ m = m := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨a, ha⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst Z Z)
    obtain ⟨b, hb⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd Z Z)
    have ht : t = lift (pushPt pb.w a) (pushPt pb.w b) := by rw [ha, hb, lift_comp_fst_snd]
    rw [ht, lift_braiding_hom_assoc, GrpDense.pushPt_mul pb.w hm, GrpDense.pushPt_mul pb.w hm, _root_.mul_comm]
  let G : GrpObj Z :=
    { one := e, mul := m, one_mul := one_mul', mul_one := mul_one', mul_assoc := mul_assoc',
      inv := i, left_inv := left_inv', right_inv := right_inv' }
  refine ⟨G, rfl, rfl, rfl, ?_, ?_⟩
  · exact { comm := ⟨comm'⟩, smooth := hsm, proper := hpr, geomConnected := hgc }
  · intro S' x A _ φ pb hm'
    refine ⟨pb, fun T a b a₀ b₀ ha hb => ?_⟩
    have ea : a₀ = pushPt pb.w a := Over.OverMorphism.ext ha
    have eb : b₀ = pushPt pb.w b := Over.OverMorphism.ext hb
    subst ea eb
    exact congrArg CommaMorphism.left (GrpDense.pushPt_mul pb.w hm' a b)

end GlobalTheory

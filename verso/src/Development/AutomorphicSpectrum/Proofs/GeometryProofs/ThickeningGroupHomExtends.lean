import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AdicCompleteAlgebraLiftingUniqueStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.LiftHom
open GlobalTheory.AdicColimit

section SpecForm
variable {R : Type} [CommRing R] (I : Ideal R)

abbrev specOver (A : Type) [CommRing A] [Algebra R A] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

variable (A : Type) [CommRing A] [Algebra R A]

abbrev redA (e : ℕ) : Type := A ⧸ (I ^ (e + 1)).map (algebraMap R A)

def redι (e : ℕ) : Spec (CommRingCat.of (redA I A e)) ⟶ (thickObj R I e (specOver A)).left :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm.toRingEquiv.toRingHom) ≫
    (pullbackSpecIso R A (R ⧸ I ^ (e + 1))).inv

instance isIso_redι (e : ℕ) : IsIso (redι I A e) := by
  unfold redι
  have : IsIso (CommRingCat.ofHom
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm.toRingEquiv.toRingHom) :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm.toRingEquiv.toCommRingCatIso).isIso_hom
  infer_instance

/- English proof (translation)
Establish `h` using `pullbackSpecIso_inv_fst R A (R ⧸ I ^ (e + 1))`. Establish `h2 : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] (R ⧸ I ^ (e + 1))) = Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R A))`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm (a ⊗ₜ[R] 1) = _`. Rewrite using `[← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply]`.

Unfold `redι`. Rewrite using `[Category.assoc]`. Use `(congrArg (fun t => Spec.map _ ≫ t) h).trans ?_` and prove the remaining obligations. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, h2]`.
-/
theorem redι_fst (e : ℕ) : redι I A e ≫ thickι I e (specOver A) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R A)))) := by
  have h := pullbackSpecIso_inv_fst R A (R ⧸ I ^ (e + 1))
  have h2 : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] (R ⧸ I ^ (e + 1))) =
      Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R A)) := by
    ext a
    change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm (a ⊗ₜ[R] 1) = _
    rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply]
  unfold redι
  rw [Category.assoc]
  refine (congrArg (fun t => Spec.map _ ≫ t) h).trans ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h2]

/- English proof (translation)
The claim follows from `Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))`.
-/
theorem map_le (e : ℕ) : (I ^ (e + 1 + 1)).map (algebraMap R A) ≤ (I ^ (e + 1)).map (algebraMap R A) :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))

/- English proof (translation)
Rewrite using `[← cancel_mono (thickι I (e + 1) (specOver A)), Category.assoc, Category.assoc, redι_fst, thickMap_ι, redι_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression.
-/
theorem redι_trans (e : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (map_le I A e))) ≫ redι I A (e + 1) =
      redι I A e ≫ thickMap R I e (specOver A) := by
  rw [← cancel_mono (thickι I (e + 1) (specOver A)), Category.assoc, Category.assoc, redι_fst, thickMap_ι,
    redι_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end SpecForm

section Lift
variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

/- English proof (translation)
Establish `hfe : ∀ e, Spec.map (Spec.preimage (redι I A e ≫ v e)) = redι I A e ≫ v e` using `fun e => Spec.map_preimage _`. Establish `hlin : ∀ e, CommRingCat.ofHom (algebraMap R B) ≫ Spec.preimage (redι I A e ≫ v e) = CommRingCat.ofHom (algebraMap R (redA I A e))` using `fun e => by`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hfe, Category.assoc]`. Use `(congrArg (fun t => redι I A e ≫ t) (hover e)).trans ?_` and prove the remaining obligations.

Rewrite using `[← Category.assoc, redι_fst]`. Conclude with `(Spec.map_comp _ _).symm`. Set `f : ∀ e, B →ₐ[R] redA I A e` to `fun e => { (Spec.preimage (redι I A e ≫ v e)).hom with commutes' := fun r => congrArg (fun φ => φ.hom r) (hlin e) }`. Establish `hf : ∀ e, CommRingCat.ofHom (f e : B →+* redA I A e) = Spec.preimage (redι I A e ≫ v e)` using `fun e => rfl`. Establish `hcompat : ∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b`.

Introduce `e b a h`. Establish `key : Spec.preimage (redι I A (e + 1) ≫ v (e + 1)) ≫ CommRingCat.ofHom (Ideal.Quotient.factor (map_le I A e)) = Spec.preimage (redι I A e ≫ v e)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hfe, hfe, ← Category.assoc, redι_trans, Category.assoc, hc]`. Establish `h2` using `congrArg (fun φ => φ.hom b) key`.

Establish `h3` using `congrArg (Ideal.Quotient.factor (map_le I A e)) h`. Rewrite `h3` using `[Ideal.Quotient.factor_mk]`. Conclude with `h3.trans h2`. Take `⟨g, hg, hu⟩` from `GlobalTheory.T.adic_complete_algebra_lifting_unique R A B I f hcompat`. Establish `hgover : Spec.map (CommRingCat.ofHom (g : B →+* A)) ≫ (specOver (R` using `R) B).hom = (specOver (R := R) A).hom := by`.

Express the relevant statement in the definitionally equal form `_ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, g.comp_algebraMap]`. Use `⟨Over.homMk (Spec.map (CommRingCat.ofHom (g : B →+* A))) hgover, fun e => ?_, fun c' hc' => ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_epi (redι I A e), ← Category.assoc, redι_fst]`. Express the relevant statement in the definitionally equal form `_ ≫ Spec.map _ = _`.

Rewrite using `[← hfe, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hf]`. Use `congr 2`. Use extensionality with `b`. Conclude with `hg e b`. Establish `hp : Spec.map (Spec.preimage c'.left) = c'.left` using `Spec.map_preimage _`.

Establish `hlin' : CommRingCat.ofHom (algebraMap R B) ≫ Spec.preimage c'.left = CommRingCat.ofHom (algebraMap R A)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hp]`. Conclude with `Over.w c'`. Set `g' : B →ₐ[R] A` to `{ (Spec.preimage c'.left).hom with commutes' := fun r => congrArg (fun φ => φ.hom r) hlin' }`.

Establish `hg' : CommRingCat.ofHom (g' : B →+* A) = Spec.preimage c'.left` using `rfl`. Establish `e1 : g' = g` using `hu g' fun e b => by`. Establish `key : Spec.preimage c'.left ≫ CommRingCat.ofHom (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R A))) = Spec.preimage (redι I A e ≫ v e)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hfe, hp, ← redι_fst, Category.assoc, hc']`.

Conclude with `congrArg (fun φ => φ.hom b) key`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← hp, ← hg', e1]`. Both sides reduce to the same expression.
-/
theorem spec_lift (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A]
    (v : ∀ e, (thickObj R I e (specOver A)).left ⟶ Spec (CommRingCat.of B))
    (hover : ∀ e, v e ≫ (specOver B).hom = thickι I e (specOver A) ≫ (specOver A).hom)
    (hc : ∀ e, thickMap R I e (specOver A) ≫ v (e + 1) = v e) :
    ∃! c : specOver A ⟶ specOver B, ∀ e, thickι I e (specOver A) ≫ c.left = v e := by
  have hfe : ∀ e, Spec.map (Spec.preimage (redι I A e ≫ v e)) = redι I A e ≫ v e := fun e => Spec.map_preimage _
  have hlin : ∀ e, CommRingCat.ofHom (algebraMap R B) ≫ Spec.preimage (redι I A e ≫ v e) =
      CommRingCat.ofHom (algebraMap R (redA I A e)) := fun e => by
    apply Spec.map_injective
    rw [Spec.map_comp, hfe, Category.assoc]
    refine (congrArg (fun t => redι I A e ≫ t) (hover e)).trans ?_
    rw [← Category.assoc, redι_fst]
    exact (Spec.map_comp _ _).symm
  let f : ∀ e, B →ₐ[R] redA I A e := fun e =>
    { (Spec.preimage (redι I A e ≫ v e)).hom with
      commutes' := fun r => congrArg (fun φ => φ.hom r) (hlin e) }
  have hf : ∀ e, CommRingCat.ofHom (f e : B →+* redA I A e) = Spec.preimage (redι I A e ≫ v e) := fun e => rfl
  have hcompat : ∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b := by
    intro e b a h
    have key : Spec.preimage (redι I A (e + 1) ≫ v (e + 1)) ≫
        CommRingCat.ofHom (Ideal.Quotient.factor (map_le I A e)) = Spec.preimage (redι I A e ≫ v e) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hfe, hfe, ← Category.assoc, redι_trans, Category.assoc, hc]
    have h2 := congrArg (fun φ => φ.hom b) key
    have h3 := congrArg (Ideal.Quotient.factor (map_le I A e)) h
    rw [Ideal.Quotient.factor_mk] at h3
    exact h3.trans h2
  obtain ⟨g, hg, hu⟩ := GlobalTheory.T.adic_complete_algebra_lifting_unique R A B I f hcompat
  have hgover : Spec.map (CommRingCat.ofHom (g : B →+* A)) ≫ (specOver (R := R) B).hom = (specOver (R := R) A).hom := by
    change _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, g.comp_algebraMap]
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom (g : B →+* A))) hgover, fun e => ?_, fun c' hc' => ?_⟩
  · rw [← cancel_epi (redι I A e), ← Category.assoc, redι_fst]
    change _ ≫ Spec.map _ = _
    rw [← hfe, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hf]
    congr 2
    ext b
    exact hg e b
  · have hp : Spec.map (Spec.preimage c'.left) = c'.left := Spec.map_preimage _
    have hlin' : CommRingCat.ofHom (algebraMap R B) ≫ Spec.preimage c'.left = CommRingCat.ofHom (algebraMap R A) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hp]
      exact Over.w c'
    let g' : B →ₐ[R] A :=
      { (Spec.preimage c'.left).hom with commutes' := fun r => congrArg (fun φ => φ.hom r) hlin' }
    have hg' : CommRingCat.ofHom (g' : B →+* A) = Spec.preimage c'.left := rfl
    have e1 : g' = g := hu g' fun e b => by
      have key : Spec.preimage c'.left ≫ CommRingCat.ofHom (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R A))) =
          Spec.preimage (redι I A e ≫ v e) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hfe, hp, ← redι_fst, Category.assoc, hc']
      exact congrArg (fun φ => φ.hom b) key
    apply Over.OverMorphism.ext
    rw [← hp, ← hg', e1]
    rfl

omit [IsNoetherianRing R] in

/- English proof (translation)
Establish `: IsAffine X.left` using `isAffine_of_isAffineHom X.hom`. Set `ψ : CommRingCat.of R ⟶ Γ(X.left, ⊤)` to `Spec.preimage (X.left.isoSpec.inv ≫ X.hom)`. Establish `hψ : Spec.map ψ = X.left.isoSpec.inv ≫ X.hom` using `Spec.map_preimage _`. Set `_ : Algebra R Γ(X.left, ⊤)` to `ψ.hom.toAlgebra`. Establish `hfin : IsFinite (Spec.map ψ)` using `by rw [hψ]; infer_instance`.

Establish `hfin' : ψ.hom.Finite` using `(IsFinite.SpecMap_iff ψ).1 hfin`. Use `⟨Γ(X.left, ⊤), inferInstance, inferInstance, hfin', ⟨Over.isoMk X.left.isoSpec ?_⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ≫ Spec.map ψ = _`. Rewrite using `[hψ, Iso.hom_inv_id_assoc]`.
-/
theorem exists_specOver (X : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A), Nonempty (X ≅ specOver A) := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let ψ : CommRingCat.of R ⟶ Γ(X.left, ⊤) := Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  have hψ : Spec.map ψ = X.left.isoSpec.inv ≫ X.hom := Spec.map_preimage _
  let _ : Algebra R Γ(X.left, ⊤) := ψ.hom.toAlgebra
  have hfin : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have hfin' : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).1 hfin
  refine ⟨Γ(X.left, ⊤), inferInstance, inferInstance, hfin', ⟨Over.isoMk X.left.isoSpec ?_⟩⟩
  change _ ≫ Spec.map ψ = _
  rw [hψ, Iso.hom_inv_id_assoc]

/- English proof (translation)
Take `⟨A, _, _, _, ⟨α⟩⟩` from `exists_specOver X`. Take `⟨B, _, _, _, ⟨β⟩⟩` from `exists_specOver Y`. Establish `hid : ∀ {T T' : Over (Spec (CommRingCat.of R))} (a : T ≅ T') (e : ℕ), thickHom I e a.hom ≫ thickHom I e a.inv = 𝟙 _` using `fun a e => by`. Rewrite using `[← Over.comp_left, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]`. Both sides reduce to the same expression.

Take `⟨c', hc', hu⟩` from `spec_lift I A B (fun e => thickHom I e α.inv ≫ v e ≫ β.hom.left) (fun e => by`. Rewrite using `[Category.assoc, Category.assoc, Over.w β.hom, hover, thickHom_ι_assoc, Over.w α.inv])`. Use the proof step `(fun e => by`. Rewrite using `[thickMap_thickHom_assoc, reassoc_of% (hc e)])`. Use `⟨α.hom ≫ c' ≫ β.inv, fun e => ?_, fun c2 h2 => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hc' e`. Rewrite using `[Over.comp_left, Over.comp_left, ← thickHom_ι_assoc, reassoc_of% h1, reassoc_of% (hid α e)]`. Rewrite using `[← Over.comp_left, Iso.hom_inv_id]`. Conclude with `Category.comp_id _`. Establish `h3` using `hu (α.inv ≫ c2 ≫ β.hom) fun e => by`.

Rewrite using `[Over.comp_left, Over.comp_left, ← thickHom_ι_assoc, reassoc_of% (h2 e)]`. Rewrite using `[← h3]`. Simplify using the standard rewrite rules.
-/
theorem over_lift (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom]
    (v : ∀ e, (thickObj R I e X).left ⟶ Y.left)
    (hover : ∀ e, v e ≫ Y.hom = thickι I e X ≫ X.hom)
    (hc : ∀ e, thickMap R I e X ≫ v (e + 1) = v e) :
    ∃! c : X ⟶ Y, ∀ e, thickι I e X ≫ c.left = v e := by
  obtain ⟨A, _, _, _, ⟨α⟩⟩ := exists_specOver X
  obtain ⟨B, _, _, _, ⟨β⟩⟩ := exists_specOver Y
  have hid : ∀ {T T' : Over (Spec (CommRingCat.of R))} (a : T ≅ T') (e : ℕ),
      thickHom I e a.hom ≫ thickHom I e a.inv = 𝟙 _ := fun a e => by
    rw [← Over.comp_left, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  obtain ⟨c', hc', hu⟩ := spec_lift I A B (fun e => thickHom I e α.inv ≫ v e ≫ β.hom.left)
    (fun e => by
      rw [Category.assoc, Category.assoc, Over.w β.hom, hover, thickHom_ι_assoc, Over.w α.inv])
    (fun e => by
      rw [thickMap_thickHom_assoc, reassoc_of% (hc e)])
  refine ⟨α.hom ≫ c' ≫ β.inv, fun e => ?_, fun c2 h2 => ?_⟩
  · have h1 := hc' e
    rw [Over.comp_left, Over.comp_left, ← thickHom_ι_assoc, reassoc_of% h1, reassoc_of% (hid α e)]
    rw [← Over.comp_left, Iso.hom_inv_id]
    exact Category.comp_id _
  · have h3 := hu (α.inv ≫ c2 ≫ β.hom) fun e => by
      rw [Over.comp_left, Over.comp_left, ← thickHom_ι_assoc, reassoc_of% (h2 e)]
    rw [← h3]
    simp

/- English proof (translation)
Establish `hiff : ∀ (c : X ⟶ Y) e, (Over.pullback (thick R I e)).map c = f e ↔ thickι I e X ≫ c.left = (f e).left ≫ thickι I e Y` using `fun c e => by`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← h, thickHom_ι]`. Introduce `h`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← cancel_mono (thickι I e Y), thickHom_ι, h]`. Take `⟨c, hc, hu⟩` from `over_lift I X Y (fun e => (f e).left ≫ thickι I e Y) (fun e => by`. Establish `h1` using `Over.w (f e)`. Simplify using `only [Over.pullback_obj_hom] at h1`.

Rewrite using `[Category.assoc, pullback.condition, reassoc_of% h1, ← pullback.condition])`. Use the proof step `(fun e => by`. Rewrite using `[reassoc_of% (hf e), thickMap_ι])`. Conclude with `⟨c, fun e => (hiff c e).2 (hc e), fun c' h => hu c' fun e => (hiff c' e).1 (h e)⟩`.
-/
theorem scheme_lift (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom]
    (f : ∀ e, thickObj R I e X ⟶ thickObj R I e Y)
    (hf : ∀ e, thickMap R I e X ≫ (f (e + 1)).left = (f e).left ≫ thickMap R I e Y) :
    ∃! c : X ⟶ Y, ∀ e, (Over.pullback (thick R I e)).map c = f e := by
  have hiff : ∀ (c : X ⟶ Y) e, (Over.pullback (thick R I e)).map c = f e ↔
      thickι I e X ≫ c.left = (f e).left ≫ thickι I e Y := fun c e => by
    constructor
    · intro h
      rw [← h, thickHom_ι]
    · intro h
      apply Over.OverMorphism.ext
      rw [← cancel_mono (thickι I e Y), thickHom_ι, h]
  obtain ⟨c, hc, hu⟩ := over_lift I X Y (fun e => (f e).left ≫ thickι I e Y)
    (fun e => by
      have h1 := Over.w (f e)
      simp only [Over.pullback_obj_hom] at h1
      rw [Category.assoc, pullback.condition, reassoc_of% h1, ← pullback.condition])
    (fun e => by
      rw [reassoc_of% (hf e), thickMap_ι])
  exact ⟨c, fun e => (hiff c e).2 (hc e), fun c' h => hu c' fun e => (hiff c' e).1 (h e)⟩

/- English proof (translation)
Take `⟨c₀, -, hu⟩` from `scheme_lift I X Y (fun e => (Over.pullback (thick R I e)).map c') (fun e => thickMap_thickHom I e c')`. Conclude with `(hu c h).trans (hu c' fun _ => rfl).symm`.
-/
theorem hom_ext_of_finite {X Y : Over (Spec (CommRingCat.of R))} [IsFinite X.hom] [IsFinite Y.hom] (c c' : X ⟶ Y)
    (h : ∀ e, (Over.pullback (thick R I e)).map c = (Over.pullback (thick R I e)).map c') : c = c' := by
  obtain ⟨c₀, -, hu⟩ := scheme_lift I X Y (fun e => (Over.pullback (thick R I e)).map c')
    (fun e => thickMap_thickHom I e c')
  exact (hu c h).trans (hu c' fun _ => rfl).symm

end Lift

section Hom

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono j, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]`. Rewrite using `[← cancel_mono j, Category.assoc, IsMonHom.mul_hom (g ≫ j), Category.assoc, IsMonHom.mul_hom j, tensorHom_comp_tensorHom_assoc]`.
-/
theorem isMonHom_of_comp_mono {C : Type*} [Category C] [CartesianMonoidalCategory C] {A B D : C} [MonObj A] [MonObj B]
    [MonObj D] (g : A ⟶ B) (j : B ⟶ D) [IsMonHom j] [Mono j] [IsMonHom (g ≫ j)] : IsMonHom g := by
  refine ⟨?_, ?_⟩
  · rw [← cancel_mono j, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom (g ≫ j), Category.assoc, IsMonHom.mul_hom j,
      tensorHom_comp_tensorHom_assoc]

variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: IsFinite (𝟙_ (Over (Spec (CommRingCat.of R)))).hom` using `inferInstanceAs (IsFinite (𝟙 _))`. Use `hom_ext_of_finite I _ _ fun n => ?_` and prove the remaining obligations. Establish `e` using `(h n).one_hom`. Rewrite `e` using `[Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi, ← Functor.map_comp]`.

Conclude with `e`. Establish `: IsFinite (P ⊗ P).hom` using `inferInstanceAs (IsFinite (pullback.fst P.hom P.hom ≫ P.hom))`. Use `hom_ext_of_finite I _ _ fun n => ?_` and prove the remaining obligations. Establish `e` using `(h n).mul_hom`. Rewrite `e` using `[Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc, cancel_epi, ← Functor.map_comp, ← Functor.map_comp]`.

Conclude with `e`.
-/
theorem isMonHom_of_reductions {P Q : Over (Spec (CommRingCat.of R))} [GrpObj P] [GrpObj Q] [IsFinite P.hom]
    [IsFinite Q.hom] (c : P ⟶ Q) (h : ∀ e, IsMonHom ((Over.pullback (thick R I e)).map c)) : IsMonHom c := by
  refine ⟨?_, ?_⟩
  · have : IsFinite (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (IsFinite (𝟙 _))
    refine hom_ext_of_finite I _ _ fun n => ?_
    have e := (h n).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi, ← Functor.map_comp] at e
    exact e
  · have : IsFinite (P ⊗ P).hom := inferInstanceAs (IsFinite (pullback.fst P.hom P.hom ≫ P.hom))
    refine hom_ext_of_finite I _ _ fun n => ?_
    have e := (h n).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
      cancel_epi, ← Functor.map_comp, ← Functor.map_comp] at e
    exact e

end Hom

/- English proof (translation)
Introduce `R _ _ _ I _ P Q P' Q' _ _ _ _ _ _ jP jQ _ _ _ φ hφ hcomp hw`. Use `choose w hw using hw`. Establish `hmono : ∀ e, Mono ((Over.pullback (thick R I e)).map jQ)` using `fun e => inferInstance`. Establish `hmonoL : ∀ e, Mono (thickHom I e jQ)` using `fun e => by`. Use `hmono e` as an intermediate fact.

Conclude with `inferInstanceAs (Mono ((Over.forget _).map ((Over.pullback (thick R I e)).map jQ)))`. Establish `hwc : ∀ e, thickMap R I e P ≫ (w (e + 1)).left = (w e).left ≫ thickMap R I e Q` using `fun e => by`. Use `hmonoL (e + 1)` as an intermediate fact. Rewrite using `[← cancel_mono (thickHom I (e + 1) jQ), Category.assoc, Category.assoc, thickMap_thickHom]`. Establish `h1 : (w (e + 1)).left ≫ thickHom I (e + 1) jQ = thickHom I (e + 1) jP ≫ (φ (e + 1)).left` using `congrArg (fun t => t.left) (hw (e + 1))`.

Establish `h2 : (w e).left ≫ thickHom I e jQ = thickHom I e jP ≫ (φ e).left` using `congrArg (fun t => t.left) (hw e)`. Rewrite using `[h1, reassoc_of% h2, thickMap_thickHom_assoc, hcomp]`. Take `⟨c, hc, -⟩` from `scheme_lift I P Q w hwc`. Establish `hcj : ∀ e, (Over.pullback (thick R I e)).map (c ≫ jQ) = (Over.pullback (thick R I e)).map jP ≫ φ e` using `fun e => by rw [Functor.map_comp, hc, hw]`. Use `⟨c, isMonHom_of_reductions I c fun e => ?_, hcj⟩` and prove the remaining obligations.

Use `hφ e` as an intermediate fact. Use `hmono e` as an intermediate fact. Establish `: IsMonHom ((Over.pullback (thick R I e)).map c ≫ (Over.pullback (thick R I e)).map jQ)`. Rewrite using `[← Functor.map_comp, hcj]`. Use `infer_instance`.

Conclude with `isMonHom_of_comp_mono _ ((Over.pullback (thick R I e)).map jQ)`.
-/
theorem lift_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P Q P' Q' : Over (Spec (CommRingCat.of R))) [GrpObj P] [GrpObj Q] [GrpObj P'] [GrpObj Q'] [IsFinite P.hom] [IsFinite Q.hom] (jP : P ⟶ P') (jQ : Q ⟶ Q') [IsMonHom jP] [IsMonHom jQ] [Mono jQ] (φ : ∀ e, thickObj R I e P' ⟶ thickObj R I e Q'), (∀ e, IsMonHom (φ e)) → (∀ e, thickMap R I e P' ≫ (φ (e + 1)).left = (φ e).left ≫ thickMap R I e Q') → (∀ e, ∃ w : thickObj R I e P ⟶ thickObj R I e Q, w ≫ (Over.pullback (thick R I e)).map jQ = (Over.pullback (thick R I e)).map jP ≫ φ e) → ∃ c : P ⟶ Q, IsMonHom c ∧ ∀ e, (Over.pullback (thick R I e)).map (c ≫ jQ) = (Over.pullback (thick R I e)).map jP ≫ φ e := by
  intro R _ _ _ I _ P Q P' Q' _ _ _ _ _ _ jP jQ _ _ _ φ hφ hcomp hw
  choose w hw using hw
  have hmono : ∀ e, Mono ((Over.pullback (thick R I e)).map jQ) := fun e => inferInstance
  have hmonoL : ∀ e, Mono (thickHom I e jQ) := fun e => by
    have := hmono e
    exact inferInstanceAs (Mono ((Over.forget _).map ((Over.pullback (thick R I e)).map jQ)))
  have hwc : ∀ e, thickMap R I e P ≫ (w (e + 1)).left = (w e).left ≫ thickMap R I e Q := fun e => by
    have := hmonoL (e + 1)
    rw [← cancel_mono (thickHom I (e + 1) jQ), Category.assoc, Category.assoc, thickMap_thickHom]
    have h1 : (w (e + 1)).left ≫ thickHom I (e + 1) jQ =
        thickHom I (e + 1) jP ≫ (φ (e + 1)).left := congrArg (fun t => t.left) (hw (e + 1))
    have h2 : (w e).left ≫ thickHom I e jQ = thickHom I e jP ≫ (φ e).left := congrArg (fun t => t.left) (hw e)
    rw [h1, reassoc_of% h2, thickMap_thickHom_assoc, hcomp]
  obtain ⟨c, hc, -⟩ := scheme_lift I P Q w hwc
  have hcj : ∀ e, (Over.pullback (thick R I e)).map (c ≫ jQ) = (Over.pullback (thick R I e)).map jP ≫ φ e :=
    fun e => by rw [Functor.map_comp, hc, hw]
  refine ⟨c, isMonHom_of_reductions I c fun e => ?_, hcj⟩
  have := hφ e
  have := hmono e
  have : IsMonHom ((Over.pullback (thick R I e)).map c ≫ (Over.pullback (thick R I e)).map jQ) := by
    rw [← Functor.map_comp, hcj]
    infer_instance
  exact isMonHom_of_comp_mono _ ((Over.pullback (thick R I e)).map jQ)

end GlobalTheory.CompanionTheory.Ar.BT.LiftHom

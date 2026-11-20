import Mathlib
import GroundTheory.TateCohomology.InducedNorm
import GroundTheory.TateCohomology.DimensionShift
import GroundTheory.TateCohomology.TateConnecting
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Linear

/- English proof (translation)
Establish `: Mono S.f` using `(Rep.mono_iff_injective _).2 hf`. Establish `: Epi S.g` using `(Rep.epi_iff_surjective _).2 hg`. Use `ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance` and prove the remaining obligations. Rewrite using `[← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)), ShortComplex.moduleCat_exact_iff]`. Conclude with `h`.
-/
theorem shortExact_of_linear {S : ShortComplex (Rep.{u} k G)} (hf : Function.Injective S.f.hom)
    (hg : Function.Surjective S.g.hom) (h : ∀ y : S.X₂, S.g.hom y = 0 → ∃ x, S.f.hom x = y) :
    S.ShortExact := by
  have : Mono S.f := (Rep.mono_iff_injective _).2 hf
  have : Epi S.g := (Rep.epi_iff_surjective _).2 hg
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
    ShortComplex.moduleCat_exact_iff]
  exact h

end Linear

variable (k G)

noncomputable def augmentation : (Rep.leftRegular k G).V →ₗ[k] k :=
  Finsupp.linearCombination k (fun _ : G => (1 : k)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

variable {k G}

@[simp]
/- English proof (translation)
Simplify using `[augmentation]`.
-/
theorem augmentation_single (g : G) (r : k) :
    augmentation k G (MonoidAlgebra.single g r) = r := by
  simp [augmentation]

/- English proof (translation)
Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `single h r`. Simplify using `only [Representation.ofMulAction_single, smul_eq_mul]`.

Rewrite using `[augmentation_single, augmentation_single]`.
-/
theorem augmentation_ρ (g : G) (x : (Rep.leftRegular k G).V) :
    augmentation k G ((Rep.leftRegular k G).ρ g x) = augmentation k G x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single h r =>
    simp only [Representation.ofMulAction_single, smul_eq_mul]
    rw [augmentation_single, augmentation_single]

variable (k G)

/- English proof (translation)
Introduce `x hx`. Simplify using `only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢`. Rewrite using `[augmentation_ρ, hx]`.
-/
theorem ker_augmentation_le_comap (g : G) :
    LinearMap.ker (augmentation k G) ≤
      (LinearMap.ker (augmentation k G)).comap ((Rep.leftRegular k G).ρ g) := by
  intro x hx
  simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
  rw [augmentation_ρ, hx]

noncomputable abbrev augIdeal : Rep.{u} k G :=
  Rep.subrepresentation (Rep.leftRegular k G) (LinearMap.ker (augmentation k G))
    (ker_augmentation_le_comap k G)

noncomputable abbrev augIdealι : augIdeal k G ⟶ Rep.leftRegular k G :=
  Rep.subtype _ _ _

noncomputable def augIdealRetract : (Rep.leftRegular k G).V →ₗ[k] (augIdeal k G).V :=
  LinearMap.codRestrict (LinearMap.ker (augmentation k G))
    (LinearMap.id - MonoidAlgebra.lsingle 1 ∘ₗ augmentation k G) fun x => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        map_sub]
      erw [MonoidAlgebra.lsingle_apply, augmentation_single, sub_self]

variable {k G}

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `hy : augmentation k G y.1 = 0` using `y.2`. Express the relevant statement in the definitionally equal form `y.1 - MonoidAlgebra.single 1 (augmentation k G y.1) = y.1`. Rewrite using `[hy, MonoidAlgebra.single_zero, sub_zero]`.
-/
theorem augIdealRetract_ι (y : augIdeal k G) : augIdealRetract k G ((augIdealι k G).hom y) = y := by
  apply Subtype.ext
  have hy : augmentation k G y.1 = 0 := y.2
  change y.1 - MonoidAlgebra.single 1 (augmentation k G y.1) = y.1
  rw [hy, MonoidAlgebra.single_zero, sub_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ι_augIdealRetract (x : (Rep.leftRegular k G).V) :
    ((augIdealι k G).hom (augIdealRetract k G x)) =
      x - MonoidAlgebra.single 1 (augmentation k G x) := rfl

instance : Module.Flat k (augIdeal k G).V :=
  Module.Flat.of_retract (augIdealι k G).hom.toLinearMap (augIdealRetract k G)
    (LinearMap.ext fun y => augIdealRetract_ι y)

noncomputable def augX (X : Rep.{u} k G) : Rep.leftRegular k G ⊗ X ⟶ X :=
  Rep.ofHom ⟨TensorProduct.lid k X ∘ₗ TensorProduct.map (augmentation k G) LinearMap.id,
    fun g => TensorProduct.ext' fun x a => by
      change TensorProduct.lid k X (TensorProduct.map (augmentation k G) LinearMap.id
        ((Rep.leftRegular k G).ρ g x ⊗ₜ X.ρ g a)) = X.ρ g (TensorProduct.lid k X
          (TensorProduct.map (augmentation k G) LinearMap.id (x ⊗ₜ a)))
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul, map_smul]
      exact congrArg (fun r => r • X.ρ g a) (augmentation_ρ g x)⟩

/- English proof (translation)
Simplify using `[augX]`.
-/
theorem augX_tmul (X : Rep.{u} k G) (x : (Rep.leftRegular k G).V) (a : X) :
    (augX X).hom (x ⊗ₜ[k] a : (Rep.leftRegular k G ⊗ X : Rep k G)) = augmentation k G x • a := by
  simp [augX]

section Tensor

variable {A B : Rep.{u} k G}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem whiskerRight_hom_tmul (f : A ⟶ B) (Y : Rep.{u} k G) (a : A) (y : Y) :
    (f ▷ Y).hom (a ⊗ₜ[k] y : (A ⊗ Y : Rep k G)) = f.hom a ⊗ₜ[k] y := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem whiskerLeft_hom_tmul (Y : Rep.{u} k G) (f : A ⟶ B) (y : Y) (a : A) :
    (Y ◁ f).hom (y ⊗ₜ[k] a : (Y ⊗ A : Rep k G)) = y ⊗ₜ[k] f.hom a := rfl

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y => rw [whiskerRight_hom_tmul, LinearMap.rTensor_tmul, hr]`. Consider the case `add s t hs ht => rw [map_add, map_add, hs, ht]`.
-/
theorem whiskerRight_retract (f : A ⟶ B) (r : B.V →ₗ[k] A.V)
    (hr : ∀ a, r (f.hom a) = a) (Y : Rep.{u} k G) (t : (A ⊗ Y : Rep k G)) :
    LinearMap.rTensor Y.V r ((f ▷ Y).hom t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [whiskerRight_hom_tmul, LinearMap.rTensor_tmul, hr]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul y a => rw [whiskerLeft_hom_tmul, LinearMap.lTensor_tmul, hr]`. Consider the case `add s t hs ht => rw [map_add, map_add, hs, ht]`.
-/
theorem whiskerLeft_retract (f : A ⟶ B) (r : B.V →ₗ[k] A.V)
    (hr : ∀ a, r (f.hom a) = a) (Y : Rep.{u} k G) (t : (Y ⊗ A : Rep k G)) :
    LinearMap.lTensor Y.V r ((Y ◁ f).hom t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul y a => rw [whiskerLeft_hom_tmul, LinearMap.lTensor_tmul, hr]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y => rfl`. Consider the case `add s t hs ht => rw [map_add, map_add, hs, ht]`.
-/
theorem whiskerRight_hom_eq_rTensor (f : A ⟶ B) (Y : Rep.{u} k G) (t : (A ⊗ Y : Rep k G)) :
    (f ▷ Y).hom t = LinearMap.rTensor Y.V f.hom.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y => rfl`. Consider the case `add s t hs ht => rw [map_add, map_add, hs, ht]`.
-/
theorem whiskerLeft_hom_eq_lTensor (Y : Rep.{u} k G) (f : A ⟶ B) (t : (Y ⊗ A : Rep k G)) :
    (Y ◁ f).hom t = LinearMap.lTensor Y.V f.hom.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/- English proof (translation)
Establish `h` using `hS.exact.map (forget₂ (Rep.{u} k G) (ModuleCat.{u} k))`. Rewrite `h` using `[ShortComplex.moduleCat_exact_iff_range_eq_ker]`. Conclude with `LinearMap.exact_iff.mpr h.symm`.
-/
theorem function_exact_of_shortExact {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) :
    Function.Exact S.f.hom.toLinearMap S.g.hom.toLinearMap := by
  have h := hS.exact.map (forget₂ (Rep.{u} k G) (ModuleCat.{u} k))
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  exact LinearMap.exact_iff.mpr h.symm

/- English proof (translation)
Establish `hg : Function.Surjective S.g.hom` using `(Rep.epi_iff_surjective _).1 hS.epi_g`. Establish `hex` using `rTensor_exact Y.V (function_exact_of_shortExact hS) hg`. Use `shortExact_of_linear hinj (fun t => ?_) (fun t ht => ?_)` and prove the remaining obligations. Take `⟨s, hs⟩` from `LinearMap.rTensor_surjective Y.V hg t`. Conclude with `⟨s, (whiskerRight_hom_eq_rTensor _ _ s).trans hs⟩`.

Establish `ht' : LinearMap.rTensor Y.V S.g.hom.toLinearMap t = 0` using `(whiskerRight_hom_eq_rTensor _ _ t).symm.trans ht`. Take `⟨s, hs⟩` from `(hex t).1 ht'`. Conclude with `⟨s, (whiskerRight_hom_eq_rTensor _ _ s).trans hs⟩`.
-/
theorem shortExact_map_tensorRight {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (Y : Rep.{u} k G) (hinj : Function.Injective (S.f ▷ Y).hom) :
    (S.map (tensorRight Y)).ShortExact := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex := rTensor_exact Y.V (function_exact_of_shortExact hS) hg
  refine shortExact_of_linear hinj (fun t => ?_) (fun t ht => ?_)
  · obtain ⟨s, hs⟩ := LinearMap.rTensor_surjective Y.V hg t
    exact ⟨s, (whiskerRight_hom_eq_rTensor _ _ s).trans hs⟩
  · have ht' : LinearMap.rTensor Y.V S.g.hom.toLinearMap t = 0 :=
      (whiskerRight_hom_eq_rTensor _ _ t).symm.trans ht
    obtain ⟨s, hs⟩ := (hex t).1 ht'
    exact ⟨s, (whiskerRight_hom_eq_rTensor _ _ s).trans hs⟩

/- English proof (translation)
Establish `hg : Function.Surjective S.g.hom` using `(Rep.epi_iff_surjective _).1 hS.epi_g`. Establish `hex` using `lTensor_exact Y.V (function_exact_of_shortExact hS) hg`. Use `shortExact_of_linear hinj (fun t => ?_) (fun t ht => ?_)` and prove the remaining obligations. Take `⟨s, hs⟩` from `LinearMap.lTensor_surjective Y.V hg t`. Conclude with `⟨s, (whiskerLeft_hom_eq_lTensor _ _ s).trans hs⟩`.

Establish `ht' : LinearMap.lTensor Y.V S.g.hom.toLinearMap t = 0` using `(whiskerLeft_hom_eq_lTensor _ _ t).symm.trans ht`. Take `⟨s, hs⟩` from `(hex t).1 ht'`. Conclude with `⟨s, (whiskerLeft_hom_eq_lTensor _ _ s).trans hs⟩`.
-/
theorem shortExact_map_tensorLeft {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (Y : Rep.{u} k G) (hinj : Function.Injective (Y ◁ S.f).hom) :
    (S.map (tensorLeft Y)).ShortExact := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex := lTensor_exact Y.V (function_exact_of_shortExact hS) hg
  refine shortExact_of_linear hinj (fun t => ?_) (fun t ht => ?_)
  · obtain ⟨s, hs⟩ := LinearMap.lTensor_surjective Y.V hg t
    exact ⟨s, (whiskerLeft_hom_eq_lTensor _ _ s).trans hs⟩
  · have ht' : LinearMap.lTensor Y.V S.g.hom.toLinearMap t = 0 :=
      (whiskerLeft_hom_eq_lTensor _ _ t).symm.trans ht
    obtain ⟨s, hs⟩ := (hex t).1 ht'
    exact ⟨s, (whiskerLeft_hom_eq_lTensor _ _ s).trans hs⟩

section Flat

variable {W P₁ P₂ Q₁ Q₂ : Type u} [AddCommGroup W] [Module k W] [Module.Flat k W]
  [AddCommGroup P₁] [Module k P₁] [AddCommGroup P₂] [Module k P₂]
  [AddCommGroup Q₁] [Module k Q₁] [AddCommGroup Q₂] [Module k Q₂]

/- English proof (translation)
Introduce `x y hxy`. Apply `e₁.injective` to reduce the goal to its premises. Apply `Module.Flat.lTensor_preserves_injective_linearMap ψ hψ` to reduce the goal to its premises. Rewrite using `[← h, ← h, hxy]`.
-/
theorem injective_of_lTensor_conj (φ : P₁ →ₗ[k] P₂) (ψ : Q₁ →ₗ[k] Q₂)
    (hψ : Function.Injective ψ) (e₁ : P₁ ≃ₗ[k] TensorProduct k W Q₁)
    (e₂ : P₂ ≃ₗ[k] TensorProduct k W Q₂) (h : ∀ x, e₂ (φ x) = LinearMap.lTensor W ψ (e₁ x)) :
    Function.Injective φ := by
  intro x y hxy
  apply e₁.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap ψ hψ
  rw [← h, ← h, hxy]

end Flat

section FlatRep

variable (V : Rep.{u} k G) [Module.Flat k V.V] {X₁ X₂ : Rep.{u} k G} (f : X₁ ⟶ X₂)

/- English proof (translation)
Introduce `s t hst`. Apply `Module.Flat.lTensor_preserves_injective_linearMap (M := V.V) f.hom.toLinearMap hf` to reduce the goal to its premises. Rewrite using `[← whiskerLeft_hom_eq_lTensor, ← whiskerLeft_hom_eq_lTensor, hst]`.
-/
theorem injective_whiskerLeft_of_flat (hf : Function.Injective f.hom) :
    Function.Injective (V ◁ f).hom := by
  intro s t hst
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := V.V) f.hom.toLinearMap hf
  rw [← whiskerLeft_hom_eq_lTensor, ← whiskerLeft_hom_eq_lTensor, hst]

/- English proof (translation)
Use `injective_of_lTensor_conj (W := V.V) (f ▷ (V ⊗ Y)).hom.toLinearMap (f ▷ Y).hom.toLinearMap hf (TensorProduct.leftComm k X₁.V V.V Y.V) (TensorProduct.leftComm k X₂.V V.V Y.V) fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Consider the case `tmul a t`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]`. Consider the case `tmul v y => rfl`.
-/
theorem injective_whiskerRight_tensor_of_flat (Y : Rep.{u} k G)
    (hf : Function.Injective (f ▷ Y).hom) : Function.Injective (f ▷ (V ⊗ Y)).hom := by
  refine injective_of_lTensor_conj (W := V.V) (f ▷ (V ⊗ Y)).hom.toLinearMap (f ▷ Y).hom.toLinearMap
    hf (TensorProduct.leftComm k X₁.V V.V Y.V) (TensorProduct.leftComm k X₂.V V.V Y.V) fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a t =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]
    | tmul v y => rfl

/- English proof (translation)
Use `injective_of_lTensor_conj (W := V.V) ((V ◁ f) ▷ Y).hom.toLinearMap (f ▷ Y).hom.toLinearMap hf (TensorProduct.assoc k V.V X₁.V Y.V) (TensorProduct.assoc k V.V X₂.V Y.V) fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Consider the case `tmul t y`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]`. Consider the case `tmul v a => rfl`.
-/
theorem injective_whiskerLeft_whiskerRight_of_flat (Y : Rep.{u} k G)
    (hf : Function.Injective (f ▷ Y).hom) : Function.Injective ((V ◁ f) ▷ Y).hom := by
  refine injective_of_lTensor_conj (W := V.V) ((V ◁ f) ▷ Y).hom.toLinearMap (f ▷ Y).hom.toLinearMap
    hf (TensorProduct.assoc k V.V X₁.V Y.V) (TensorProduct.assoc k V.V X₂.V Y.V) fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul t y =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]
    | tmul v a => rfl

/- English proof (translation)
Use `injective_of_lTensor_conj (W := V.V) ((V ⊗ Y) ◁ f).hom.toLinearMap (Y ◁ f).hom.toLinearMap hf (TensorProduct.assoc k V.V Y.V X₁.V) (TensorProduct.assoc k V.V Y.V X₂.V) fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Consider the case `tmul t a`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]`. Consider the case `tmul v y => rfl`.
-/
theorem injective_tensor_whiskerLeft_of_flat (Y : Rep.{u} k G)
    (hf : Function.Injective (Y ◁ f).hom) : Function.Injective ((V ⊗ Y) ◁ f).hom := by
  refine injective_of_lTensor_conj (W := V.V) ((V ⊗ Y) ◁ f).hom.toLinearMap (Y ◁ f).hom.toLinearMap
    hf (TensorProduct.assoc k V.V Y.V X₁.V) (TensorProduct.assoc k V.V Y.V X₂.V) fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul t a =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]
    | tmul v y => rfl

/- English proof (translation)
Use `injective_of_lTensor_conj (W := V.V) (Y ◁ (V ◁ f)).hom.toLinearMap (Y ◁ f).hom.toLinearMap hf (TensorProduct.leftComm k Y.V V.V X₁.V) (TensorProduct.leftComm k Y.V V.V X₂.V) fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Consider the case `tmul y t`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]`. Consider the case `tmul v a => rfl`.
-/
theorem injective_whiskerLeft_whiskerLeft_of_flat (Y : Rep.{u} k G)
    (hf : Function.Injective (Y ◁ f).hom) : Function.Injective (Y ◁ (V ◁ f)).hom := by
  refine injective_of_lTensor_conj (W := V.V) (Y ◁ (V ◁ f)).hom.toLinearMap (Y ◁ f).hom.toLinearMap
    hf (TensorProduct.leftComm k Y.V V.V X₁.V) (TensorProduct.leftComm k Y.V V.V X₂.V) fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul y t =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]
    | tmul v a => rfl

end FlatRep

end Tensor

section AugSES

/- English proof (translation)
Use extensionality with `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul y a`. Express the relevant statement in the definitionally equal form `(augX X).hom ((augIdealι k G).hom y ⊗ₜ[k] a) = 0`.

Rewrite using `[augX_tmul]`. Establish `hy : augmentation k G y.1 = 0` using `y.2`. Conclude with `(congrArg (· • a) hy).trans (zero_smul k a)`. Consider the case `add s t hs ht => rw [map_add, map_add, hs, ht]`.
-/
theorem augSES_zero (X : Rep.{u} k G) : augIdealι k G ▷ X ≫ augX X = 0 := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul y a =>
    change (augX X).hom ((augIdealι k G).hom y ⊗ₜ[k] a) = 0
    rw [augX_tmul]
    have hy : augmentation k G y.1 = 0 := y.2
    exact (congrArg (· • a) hy).trans (zero_smul k a)
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/- English proof (translation)
Use extensionality with `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x a`. Express the relevant statement in the definitionally equal form `(augX Y).hom (x ⊗ₜ[k] f.hom a) = f.hom ((augX X).hom (x ⊗ₜ[k] a))`.

Rewrite using `[augX_tmul, augX_tmul, map_smul]`. Consider the case `add s t hs ht`. Rewrite using `[map_add, map_add, hs, ht]`.
-/
theorem augX_naturality {X Y : Rep.{u} k G} (f : X ⟶ Y) :
    Rep.leftRegular k G ◁ f ≫ augX Y = augX X ≫ f := by
  ext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    change (augX Y).hom (x ⊗ₜ[k] f.hom a) = f.hom ((augX X).hom (x ⊗ₜ[k] a))
    rw [augX_tmul, augX_tmul, map_smul]
  | add s t hs ht =>
    rw [map_add, map_add, hs, ht]

variable (k G) in

noncomputable def augSES : Rep.{u} k G ⥤ ShortComplex (Rep.{u} k G) where
  obj X := ShortComplex.mk (augIdealι k G ▷ X) (augX X) (augSES_zero X)
  map f :=
    { τ₁ := augIdeal k G ◁ f
      τ₂ := Rep.leftRegular k G ◁ f
      τ₃ := f
      comm₁₂ := whisker_exchange _ _
      comm₂₃ := augX_naturality f }
  map_id _ := ShortComplex.hom_ext _ _ (MonoidalCategory.whiskerLeft_id _ _)
    (MonoidalCategory.whiskerLeft_id _ _) rfl
  map_comp _ _ := ShortComplex.hom_ext _ _ (MonoidalCategory.whiskerLeft_comp _ _ _)
    (MonoidalCategory.whiskerLeft_comp _ _ _) rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem augSES_obj_X₁ (X : Rep.{u} k G) : ((augSES k G).obj X).X₁ = augIdeal k G ⊗ X := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem augSES_obj_X₂ (X : Rep.{u} k G) :
    ((augSES k G).obj X).X₂ = Rep.leftRegular k G ⊗ X := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem augSES_obj_X₃ (X : Rep.{u} k G) : ((augSES k G).obj X).X₃ = X := rfl

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x a`. Rewrite using `[LinearMap.rTensor_tmul, whiskerRight_hom_tmul, ι_augIdealRetract, augX_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', MonoidAlgebra.smul_single, smul_eq_mul, mul_one, ← TensorProduct.add_tmul, sub_add_cancel]`. Consider the case `add s t hs ht`.

Rewrite using `[map_add, map_add, map_add, TensorProduct.tmul_add]`. Use `conv_rhs => rw [← hs, ← ht]`. Normalize the expressions using the abelian group laws.
-/
theorem augSES_decomp (X : Rep.{u} k G) (t : (Rep.leftRegular k G ⊗ X : Rep k G)) :
    (augIdealι k G ▷ X).hom (LinearMap.rTensor X.V (augIdealRetract k G) t) +
      (MonoidAlgebra.single 1 1 ⊗ₜ[k] (augX X).hom t : (Rep.leftRegular k G ⊗ X : Rep k G)) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    rw [LinearMap.rTensor_tmul, whiskerRight_hom_tmul, ι_augIdealRetract, augX_tmul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', MonoidAlgebra.smul_single, smul_eq_mul,
      mul_one, ← TensorProduct.add_tmul, sub_add_cancel]
  | add s t hs ht =>
    rw [map_add, map_add, map_add, TensorProduct.tmul_add]
    conv_rhs => rw [← hs, ← ht]
    abel

/- English proof (translation)
The claim follows from `whiskerRight_retract _ _ augIdealRetract_ι X t`.
-/
theorem augSES_f_retract (X : Rep.{u} k G) (t : (augIdeal k G ⊗ X : Rep k G)) :
    LinearMap.rTensor X.V (augIdealRetract k G) (((augSES k G).obj X).f.hom t) = t :=
  whiskerRight_retract _ _ augIdealRetract_ι X t

/- English proof (translation)
The claim follows from `shortExact_of_linear (Function.LeftInverse.injective (augSES_f_retract X)) (fun (a : X) => ⟨(MonoidAlgebra.single 1 1 ⊗ₜ[k] a : (Rep.leftRegular k G ⊗ X : Rep k G)), by change (augX X).hom _ = a rw [augX_tmul, augmentation_single, one_smul]⟩) (fun t ht => ⟨LinearMap.rTensor X.V ( …`.
-/
theorem augSES_shortExact (X : Rep.{u} k G) : ((augSES k G).obj X).ShortExact :=
  shortExact_of_linear (Function.LeftInverse.injective (augSES_f_retract X))
    (fun (a : X) => ⟨(MonoidAlgebra.single 1 1 ⊗ₜ[k] a : (Rep.leftRegular k G ⊗ X : Rep k G)), by
      change (augX X).hom _ = a
      rw [augX_tmul, augmentation_single, one_smul]⟩)
    (fun t ht => ⟨LinearMap.rTensor X.V (augIdealRetract k G) t, by
      have h := augSES_decomp X t
      have ht' : (augX X).hom t = 0 := ht
      rw [ht', TensorProduct.tmul_zero, add_zero] at h
      exact h⟩)

/- English proof (translation)
The claim follows from `shortExact_map_tensorRight (augSES_shortExact A) B (Function.LeftInverse.injective (whiskerRight_retract _ _ (augSES_f_retract A) B))`.
-/
theorem augSES_tensorRight_shortExact (A B : Rep.{u} k G) :
    (((augSES k G).obj A).map (tensorRight B)).ShortExact :=
  shortExact_map_tensorRight (augSES_shortExact A) B
    (Function.LeftInverse.injective (whiskerRight_retract _ _ (augSES_f_retract A) B))

/- English proof (translation)
The claim follows from `shortExact_map_tensorLeft (augSES_shortExact B) A (Function.LeftInverse.injective (whiskerLeft_retract _ _ (augSES_f_retract B) A))`.
-/
theorem augSES_tensorLeft_shortExact (A B : Rep.{u} k G) :
    (((augSES k G).obj B).map (tensorLeft A)).ShortExact :=
  shortExact_map_tensorLeft (augSES_shortExact B) A
    (Function.LeftInverse.injective (whiskerLeft_retract _ _ (augSES_f_retract B) A))

variable [Fintype G]

/- English proof (translation)
The claim follows from `tateAcyclic_leftRegular_tensor X`.
-/
theorem tateAcyclic_augSES_X₂ (X : Rep.{u} k G) : TateAcyclic ((augSES k G).obj X).X₂ :=
  tateAcyclic_leftRegular_tensor X

/- English proof (translation)
The claim follows from `(tateAcyclic_leftRegular_tensor (A ⊗ B)).of_iso (α_ (Rep.leftRegular k G) A B)`.
-/
theorem tateAcyclic_augSES_tensorRight_X₂ (A B : Rep.{u} k G) :
    TateAcyclic (((augSES k G).obj A).map (tensorRight B)).X₂ :=
  (tateAcyclic_leftRegular_tensor (A ⊗ B)).of_iso (α_ (Rep.leftRegular k G) A B)

/- English proof (translation)
The claim follows from `(tateAcyclic_leftRegular_tensor (A ⊗ B)).of_iso ((α_ A (Rep.leftRegular k G) B).symm ≪≫ whiskerRightIso (β_ A (Rep.leftRegular k G)) B ≪≫ α_ (Rep.leftRegular k G) A B)`.
-/
theorem tateAcyclic_augSES_tensorLeft_X₂ (A B : Rep.{u} k G) :
    TateAcyclic (((augSES k G).obj B).map (tensorLeft A)).X₂ :=
  (tateAcyclic_leftRegular_tensor (A ⊗ B)).of_iso
    ((α_ A (Rep.leftRegular k G) B).symm ≪≫ whiskerRightIso (β_ A (Rep.leftRegular k G)) B ≪≫
      α_ (Rep.leftRegular k G) A B)

/- English proof (translation)
Substitute `hij` using the available equality. Conclude with `isIso_δ_of_tateAcyclic hS h i`.
-/
theorem isIso_tδ_of_tateAcyclic {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h : TateAcyclic S.X₂) (i j : ℤ) (hij : i + 1 = j) : IsIso (tδ hS i j hij) := by
  subst hij
  exact isIso_δ_of_tateAcyclic hS h i

end AugSES

end GroundTheory.GroupCoh

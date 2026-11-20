import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.PairingTensor

open TensorProduct

variable {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

noncomputable def contrR (l : B →ₗ[ℂ] ℂ) : TensorProduct ℂ A B →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ LinearMap.lTensor A l

noncomputable def contrL (l : A →ₗ[ℂ] ℂ) : TensorProduct ℂ A B →ₗ[ℂ] B :=
  (TensorProduct.lid ℂ B).toLinearMap ∘ₗ LinearMap.rTensor B l

/- English proof (translation)
Simplify using `[contrR]`.
-/
@[simp] theorem contrR_tmul (l : B →ₗ[ℂ] ℂ) (a : A) (b : B) :
    contrR l (a ⊗ₜ[ℂ] b) = l b • a := by
  simp [contrR]

/- English proof (translation)
Simplify using `[contrL]`.
-/
@[simp] theorem contrL_tmul (l : A →ₗ[ℂ] ℂ) (a : A) (b : B) :
    contrL l (a ⊗ₜ[ℂ] b) = l a • b := by
  simp [contrL]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [mul_comm]`. Consider the case `add x y hx hy => simp [hx, hy]`.
-/
theorem apply_contrR (l : A →ₗ[ℂ] ℂ) (m : B →ₗ[ℂ] ℂ) (z : TensorProduct ℂ A B) :
    l (contrR m z) = m (contrL l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add x y hx hy => simp [hx, hy]`.
-/
theorem contrR_map (m : B →ₗ[ℂ] ℂ) (a : Module.End ℂ A) (z : TensorProduct ℂ A B) :
    contrR m (TensorProduct.map a LinearMap.id z) = a (contrR m z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add x y hx hy => simp [hx, hy]`.
-/
theorem contrL_map (l : A →ₗ[ℂ] ℂ) (b : Module.End ℂ B) (z : TensorProduct ℂ A B) :
    contrL l (TensorProduct.map LinearMap.id b z) = b (contrL l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/- English proof (translation)
Set `bA` to `Module.Basis.ofVectorSpace ℂ A`. Establish `key : ∀ (w : TensorProduct ℂ A B) i, TensorProduct.equivFinsuppOfBasisLeft bA w i = contrL (bA.coord i) w`. Introduce `w i`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp`. Consider the case `add x y hx hy => simp [hx, hy]`. Apply `(TensorProduct.equivFinsuppOfBasisLeft bA).injective` to reduce the goal to its premises. Use extensionality with `i`. Rewrite using `[key, map_zero, Finsupp.zero_apply]`.

Apply `hm` to reduce the goal to its premises. Introduce `y`. Rewrite using `[← apply_contrR, hz, map_zero]`.
-/
theorem eq_zero_of_contrR {ι : Type} (m : ι → B →ₗ[ℂ] ℂ) (hm : ∀ b, (∀ y, m y b = 0) → b = 0)
    (z : TensorProduct ℂ A B) (hz : ∀ y, contrR (m y) z = 0) : z = 0 := by
  classical
  let bA := Module.Basis.ofVectorSpace ℂ A
  have key : ∀ (w : TensorProduct ℂ A B) i,
      TensorProduct.equivFinsuppOfBasisLeft bA w i = contrL (bA.coord i) w := by
    intro w i
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft bA).injective
  ext i
  rw [key, map_zero, Finsupp.zero_apply]
  apply hm
  intro y
  rw [← apply_contrR, hz, map_zero]

/- English proof (translation)
Apply `hi` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `inner_self_eq_zero.mp (h (i a))`.
-/
theorem inner_separates {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (i : A →ₗ[ℂ] H) (hi : Function.Injective i) (a : A) (h : ∀ x, inner ℂ x (i a) = 0) :
    a = 0 := by
  apply hi
  rw [map_zero]
  exact inner_self_eq_zero.mp (h (i a))

/- English proof (translation)
Introduce `V A B H₁ H₂ _ _ _ _ _ _ _ _ _ _ i₁ i₂ h₁ h₂ φ ψ hφψ hE`. Set `m : H₂ → B →ₗ[ℂ] ℂ` to `fun y => (innerₛₗ ℂ y) ∘ₗ i₂`. Set `l : H₁ → A →ₗ[ℂ] ℂ` to `fun x => (innerₛₗ ℂ x) ∘ₗ i₁`. Establish `hm : ∀ y b, m y b = inner ℂ y (i₂ b)` using `fun _ _ => rfl`. Establish `hl : ∀ x a, l x a = inner ℂ x (i₁ a)` using `fun _ _ => rfl`.

Establish `sepm : ∀ b, (∀ y, m y b = 0) → b = 0` using `fun b h => inner_separates i₂ h₂ b h`. Establish `sepl : ∀ a, (∀ x, l x a = 0) → a = 0` using `fun a h => inner_separates i₁ h₁ a h`. Establish `sepR : ∀ z w : TensorProduct ℂ A B, (∀ y, contrR (m y) z = contrR (m y) w) → z = w`. Introduce `z w h`. Rewrite using `[← sub_eq_zero]`.

Conclude with `eq_zero_of_contrR m sepm _ (fun y => by rw [map_sub, h, sub_self])`. Establish `sepL : ∀ z w : TensorProduct ℂ A B, (∀ x, contrL (l x) z = contrL (l x) w) → z = w`. Introduce `z w h`. Apply `sepR` to reduce the goal to its premises. Introduce `y`.

Rewrite using `[← sub_eq_zero]`. Apply `sepl` to reduce the goal to its premises. Introduce `x`. Rewrite using `[map_sub, apply_contrR, apply_contrR, h, sub_self]`. Establish `ex : ∀ P, ∃ z : TensorProduct ℂ A B, ∀ y, contrR (m y) z = φ y P`.

Introduce `P`. Take `⟨E, hfin, hmem⟩` from `hE P`. Set `e` to `stdOrthonormalBasis ℂ (E.map i₁)`. Establish `ha : ∀ j, ∃ a : A, i₁ a = (e j : H₁)` using `fun j => by`. Take `⟨a, -, ha⟩` from `(e j).2`.

Conclude with `⟨a, ha⟩`. Use `choose a ha using ha`. Use `⟨∑ j, a j ⊗ₜ[ℂ] ψ (e j) P, fun y => ?_⟩` and prove the remaining obligations. Apply `h₁` to reduce the goal to its premises. Use `congrArg (fun v : E.map i₁ => (v : H₁)) (e.sum_repr' ⟨i₁ (φ y P), Submodule.mem_map_of_mem (hmem y)⟩)` as an intermediate fact.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this`. Rewrite using `[← this, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[contrR_tmul, map_smul, ha, hm, ← hφψ]`. Use `choose g hg using ex`.

Set `f : V →ₗ[ℂ] TensorProduct ℂ A B` to `{ toFun := g map_add' := fun P Q => sepR _ _ fun y => by rw [map_add, hg, hg, hg, map_add] map_smul' := fun s P => sepR _ _ fun y => by`. Rewrite using `[map_smul, hg, hg, map_smul, RingHom.id_apply] }`. Establish `hf : ∀ P y, contrR (m y) (f P) = φ y P` using `hg`. Establish `hf' : ∀ P x, contrL (l x) (f P) = ψ x P`. Introduce `P x`.

Rewrite using `[← sub_eq_zero]`. Apply `sepm` to reduce the goal to its premises. Introduce `y`. Rewrite using `[map_sub, ← apply_contrR, hf, hl, hm, hφψ, sub_self]`. Use `⟨f, fun P hP y => by rw [← hf, hP, map_zero], fun c a h => ?_, fun c b h => ?_⟩` and prove the remaining obligations.

Use extensionality with `P`. Use `sepR _ _ fun y => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, contrR_map, hf, hf, h]`. Use extensionality with `P`. Use `sepL _ _ fun x => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, contrL_map, hf', hf', h]`.
-/
theorem exists_linearMap_tensor :
    ∀ (V A B H₁ H₂ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂), Function.Injective i₁ → Function.Injective i₂ → ∀ (φ : H₂ → V →ₗ[ℂ] A) (ψ : H₁ → V →ₗ[ℂ] B), (∀ x y P, inner ℂ x (i₁ (φ y P)) = inner ℂ y (i₂ (ψ x P))) → (∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) → ∃ f : V →ₗ[ℂ] TensorProduct ℂ A B, (∀ P, f P = 0 → ∀ y, φ y P = 0) ∧ (∀ (c : Module.End ℂ V) (a : Module.End ℂ A), (∀ y P, φ y (c P) = a (φ y P)) → f ∘ₗ c = TensorProduct.map a LinearMap.id ∘ₗ f) ∧ (∀ (c : Module.End ℂ V) (b : Module.End ℂ B), (∀ x P, ψ x (c P) = b (ψ x P)) → f ∘ₗ c = TensorProduct.map LinearMap.id b ∘ₗ f) := by
  intro V A B H₁ H₂ _ _ _ _ _ _ _ _ _ _ i₁ i₂ h₁ h₂ φ ψ hφψ hE
  let m : H₂ → B →ₗ[ℂ] ℂ := fun y => (innerₛₗ ℂ y) ∘ₗ i₂
  let l : H₁ → A →ₗ[ℂ] ℂ := fun x => (innerₛₗ ℂ x) ∘ₗ i₁
  have hm : ∀ y b, m y b = inner ℂ y (i₂ b) := fun _ _ => rfl
  have hl : ∀ x a, l x a = inner ℂ x (i₁ a) := fun _ _ => rfl
  have sepm : ∀ b, (∀ y, m y b = 0) → b = 0 := fun b h => inner_separates i₂ h₂ b h
  have sepl : ∀ a, (∀ x, l x a = 0) → a = 0 := fun a h => inner_separates i₁ h₁ a h
  have sepR : ∀ z w : TensorProduct ℂ A B, (∀ y, contrR (m y) z = contrR (m y) w) → z = w := by
    intro z w h
    rw [← sub_eq_zero]
    exact eq_zero_of_contrR m sepm _ (fun y => by rw [map_sub, h, sub_self])
  have sepL : ∀ z w : TensorProduct ℂ A B, (∀ x, contrL (l x) z = contrL (l x) w) → z = w := by
    intro z w h
    apply sepR
    intro y
    rw [← sub_eq_zero]
    apply sepl
    intro x
    rw [map_sub, apply_contrR, apply_contrR, h, sub_self]
  have ex : ∀ P, ∃ z : TensorProduct ℂ A B, ∀ y, contrR (m y) z = φ y P := by
    intro P
    obtain ⟨E, hfin, hmem⟩ := hE P
    let e := stdOrthonormalBasis ℂ (E.map i₁)
    have ha : ∀ j, ∃ a : A, i₁ a = (e j : H₁) := fun j => by
      obtain ⟨a, -, ha⟩ := (e j).2
      exact ⟨a, ha⟩
    choose a ha using ha
    refine ⟨∑ j, a j ⊗ₜ[ℂ] ψ (e j) P, fun y => ?_⟩
    apply h₁
    have := congrArg (fun v : E.map i₁ => (v : H₁))
      (e.sum_repr' ⟨i₁ (φ y P), Submodule.mem_map_of_mem (hmem y)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this
    rw [← this, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [contrR_tmul, map_smul, ha, hm, ← hφψ]
  choose g hg using ex
  let f : V →ₗ[ℂ] TensorProduct ℂ A B :=
    { toFun := g
      map_add' := fun P Q => sepR _ _ fun y => by rw [map_add, hg, hg, hg, map_add]
      map_smul' := fun s P => sepR _ _ fun y => by
        rw [map_smul, hg, hg, map_smul, RingHom.id_apply] }
  have hf : ∀ P y, contrR (m y) (f P) = φ y P := hg
  have hf' : ∀ P x, contrL (l x) (f P) = ψ x P := by
    intro P x
    rw [← sub_eq_zero]
    apply sepm
    intro y
    rw [map_sub, ← apply_contrR, hf, hl, hm, hφψ, sub_self]
  refine ⟨f, fun P hP y => by rw [← hf, hP, map_zero], fun c a h => ?_, fun c b h => ?_⟩
  · ext P
    refine sepR _ _ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrR_map, hf, hf, h]
  · ext P
    refine sepL _ _ fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrL_map, hf', hf', h]

end GlobalTheory.PairingTensor

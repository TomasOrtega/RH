import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport

noncomputable section

open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift.TensorFormProof

open GlobalTheory.Chain.IoLift

variable {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]

/- English proof (translation)
Unfold `contr`. Rewrite using `[LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.comp_apply, innerₛₗ_apply_apply]`. Conclude with `TensorProduct.rid_tmul _ _`.
-/
theorem contr_tmul (ι : V →ₗ[ℂ] H) (y : V) (a : A) (v : V) :
    contr ι y (a ⊗ₜ[ℂ] v) = ⟪ι y, ι v⟫_ℂ • a := by
  unfold contr
  rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.comp_apply, innerₛₗ_apply_apply]
  exact TensorProduct.rid_tmul _ _

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a v`. Rewrite using `[contr_tmul, map_smul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, inner_smul_right, smul_eq_mul, mul_comm]`. Consider the case `add s u hs hu => simp only [map_add, inner_add_right, hs, hu]`.
-/
theorem dual_contr (ι : V →ₗ[ℂ] H) (y : V) (l : A →ₗ[ℂ] ℂ) (t : A ⊗[ℂ] V) :
    l (contr ι y t) = ⟪ι y, ι (TensorProduct.lid ℂ V (LinearMap.rTensor V l t))⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [contr_tmul, map_smul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, inner_smul_right,
      smul_eq_mul, mul_comm]
  | add s u hs hu => simp only [map_add, inner_add_right, hs, hu]

/- English proof (translation)
Establish `hl : ∀ l : A →ₗ[ℂ] ℂ, LinearMap.rTensor V l t = 0`. Introduce `l`. Use `set w := TensorProduct.lid ℂ V (LinearMap.rTensor V l t) with hw`. Establish `h0 : ⟪ι w, ι w⟫_ℂ = 0`. Use `dual_contr ι w l t` as an intermediate fact.

Rewrite `this` using `[h w, map_zero]`. Conclude with `this.symm`. Establish `hw0 : w = 0` using `hι ((inner_self_eq_zero.mp h0).trans (map_zero ι).symm)`. Rewrite `hw0` using `[hw]`. Conclude with `(LinearEquiv.map_eq_zero_iff _).mp hw0`.

Set `e` to `(Module.Basis.ofVectorSpace ℂ A).repr`. Establish `hs : TensorProduct.finsuppScalarLeft ℂ V _ (LinearMap.rTensor V e.toLinearMap t) = 0`. Use extensionality with `i`. Rewrite using `[TensorProduct.finsuppScalarLeft_apply, ← LinearMap.rTensor_comp_apply, hl, map_zero]`. Both sides reduce to the same expression.

Establish `h2 : LinearMap.rTensor V e.toLinearMap t = 0` using `(LinearEquiv.map_eq_zero_iff _).mp hs`. Establish `h3` using `congrArg (LinearMap.rTensor V e.symm.toLinearMap) h2`. Rewrite `h3` using `[← LinearMap.rTensor_comp_apply, LinearEquiv.symm_comp, LinearMap.rTensor_id_apply, map_zero]`. Then use the resulting hypothesis.
-/
theorem eq_zero_of_contr (ι : V →ₗ[ℂ] H) (hι : Function.Injective ι) (t : A ⊗[ℂ] V)
    (h : ∀ y, contr ι y t = 0) : t = 0 := by

  have hl : ∀ l : A →ₗ[ℂ] ℂ, LinearMap.rTensor V l t = 0 := by
    intro l
    set w := TensorProduct.lid ℂ V (LinearMap.rTensor V l t) with hw
    have h0 : ⟪ι w, ι w⟫_ℂ = 0 := by
      have := dual_contr ι w l t
      rw [h w, map_zero] at this
      exact this.symm
    have hw0 : w = 0 := hι ((inner_self_eq_zero.mp h0).trans (map_zero ι).symm)
    rw [hw] at hw0
    exact (LinearEquiv.map_eq_zero_iff _).mp hw0

  let e := (Module.Basis.ofVectorSpace ℂ A).repr
  have hs : TensorProduct.finsuppScalarLeft ℂ V _ (LinearMap.rTensor V e.toLinearMap t) = 0 := by
    ext i
    rw [TensorProduct.finsuppScalarLeft_apply, ← LinearMap.rTensor_comp_apply, hl, map_zero]
    rfl
  have h2 : LinearMap.rTensor V e.toLinearMap t = 0 := (LinearEquiv.map_eq_zero_iff _).mp hs
  have h3 := congrArg (LinearMap.rTensor V e.symm.toLinearMap) h2
  rwa [← LinearMap.rTensor_comp_apply, LinearEquiv.symm_comp, LinearMap.rTensor_id_apply, map_zero] at h3

/- English proof (translation)
Use `set F : Submodule ℂ H := E.map ι with hF`. Use `haveI : FiniteDimensional ℂ F := by rw [hF]; infer_instance`. Set `b` to `stdOrthonormalBasis ℂ F`. Establish `hpre : ∀ k, ∃ e : V, e ∈ E ∧ ι e = (b k : H)` using `fun k => Submodule.mem_map.mp (b k).2`. Use `choose e heE he using hpre`.

Use `⟨∑ k, β (e k) ⊗ₜ[ℂ] e k, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Simplify using `only [contr_tmul, he]`. Use `set z : V := ∑ k, ⟪(b k : H), ι y⟫_ℂ • e k with hz`. Establish `hperp : ∀ x ∈ E, ⟪ι (y - z), ι x⟫_ℂ = 0`.

Introduce `x hx`. Establish `hxF : ι x ∈ F` using `Submodule.mem_map_of_mem hx`. Establish `hx' : ι x = ∑ j, ⟪(b j : H), ι x⟫_ℂ • (b j : H)`. Use `congrArg Subtype.val (b.sum_repr' ⟨ι x, hxF⟩)` as an intermediate fact. Simplify `this.symm` using `[Submodule.coe_inner]`.

Establish `key : ⟪ι y, ι x⟫_ℂ = ∑ j, ⟪ι y, (b j : H)⟫_ℂ * ⟪(b j : H), ι x⟫_ℂ` using `by conv_lhs => rw [hx']`. Rewrite using `[inner_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_right, mul_comm]`. Simplify using `only [hz, map_sub, map_sum, map_smul, he, inner_sub_left, sum_inner, inner_smul_left, inner_conj_symm]`.

Rewrite using `[key, sub_self]`. Establish `hyz` using `h (y - z) hperp`. Rewrite `hyz` using `[map_sub, sub_eq_zero]`. Rewrite using `[hyz, hz, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smulₛₗ, inner_conj_symm]`.
-/
theorem exists_tensor (ι : V →ₗ[ℂ] H) (β : V →ₛₗ[starRingEnd ℂ] A) (E : Submodule ℂ V) [FiniteDimensional ℂ E]
    (h : ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → β y = 0) : ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = β y := by

  set F : Submodule ℂ H := E.map ι with hF
  haveI : FiniteDimensional ℂ F := by rw [hF]; infer_instance
  let b := stdOrthonormalBasis ℂ F
  have hpre : ∀ k, ∃ e : V, e ∈ E ∧ ι e = (b k : H) := fun k => Submodule.mem_map.mp (b k).2
  choose e heE he using hpre
  refine ⟨∑ k, β (e k) ⊗ₜ[ℂ] e k, fun y => ?_⟩
  rw [map_sum]
  simp only [contr_tmul, he]

  set z : V := ∑ k, ⟪(b k : H), ι y⟫_ℂ • e k with hz
  have hperp : ∀ x ∈ E, ⟪ι (y - z), ι x⟫_ℂ = 0 := by
    intro x hx
    have hxF : ι x ∈ F := Submodule.mem_map_of_mem hx
    have hx' : ι x = ∑ j, ⟪(b j : H), ι x⟫_ℂ • (b j : H) := by
      have := congrArg Subtype.val (b.sum_repr' ⟨ι x, hxF⟩)
      simpa [Submodule.coe_inner] using this.symm
    have key : ⟪ι y, ι x⟫_ℂ = ∑ j, ⟪ι y, (b j : H)⟫_ℂ * ⟪(b j : H), ι x⟫_ℂ := by
      conv_lhs => rw [hx']
      rw [inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right, mul_comm]
    simp only [hz, map_sub, map_sum, map_smul, he, inner_sub_left, sum_inner, inner_smul_left, inner_conj_symm]
    rw [key, sub_self]
  have hyz := h (y - z) hperp
  rw [map_sub, sub_eq_zero] at hyz
  rw [hyz, hz, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, inner_conj_symm]

/- English proof (translation)
Introduce `U A V H _ _ _ _ _ _ _ _ ι hι`. Establish `sep : ∀ s u : A ⊗[ℂ] V, (∀ y, contr ι y s = contr ι y u) → s = u` using `fun s u hsu => sub_eq_zero.mp (eq_zero_of_contr ι hι _ fun y => by rw [map_sub, hsu, sub_self])`. Use `⟨fun t ht => eq_zero_of_contr ι hι t ht, fun B hB => ?_⟩` and prove the remaining obligations. Establish `hex : ∀ P, ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = B P y`. Introduce `P`.

Take `⟨E, hE, hk⟩` from `hB P`. Conclude with `exists_tensor ι (B P) E hk`. Use `choose g hg using hex`. Conclude with `⟨{ toFun := g map_add' := fun P Q => sep _ _ fun y => by simp [hg] map_smul' := fun c P => sep _ _ fun y => by simp [hg] }, hg⟩`.
-/
theorem tensorForm : TensorForm := by
  intro U A V H _ _ _ _ _ _ _ _ ι hι
  have sep : ∀ s u : A ⊗[ℂ] V, (∀ y, contr ι y s = contr ι y u) → s = u := fun s u hsu =>
    sub_eq_zero.mp (eq_zero_of_contr ι hι _ fun y => by rw [map_sub, hsu, sub_self])
  refine ⟨fun t ht => eq_zero_of_contr ι hι t ht, fun B hB => ?_⟩
  have hex : ∀ P, ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = B P y := by
    intro P
    obtain ⟨E, hE, hk⟩ := hB P
    exact exists_tensor ι (B P) E hk
  choose g hg using hex
  exact ⟨{ toFun := g
           map_add' := fun P Q => sep _ _ fun y => by simp [hg]
           map_smul' := fun c P => sep _ _ fun y => by simp [hg] }, hg⟩

end GlobalTheory.Chain.IoLift.TensorFormProof

end

import Mathlib
import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
import GroundTheory.ProfiniteCohomology.CupProducts.Projection
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

section Module

variable {k Γ : Type u} [CommRing k] [Group Γ] (W : Subgroup Γ) (V : Type u) [AddCommGroup V]
  [Module k V]

/- English proof (translation)
The claim follows from `f.2 w x`.
-/
theorem coind_trivial_apply_mul (f : Rep.coind W.subtype (Rep.trivial k W V)) (w : W) (x : Γ) :
    f.1 ((w : Γ) * x) = f.1 x :=
  f.2 w x

def coindSingleFun (a : V) : Rep.coind W.subtype (Rep.trivial k W V) :=
  ⟨(W : Set Γ).indicator fun _ => a, fun w x => by
    change (W : Set Γ).indicator (fun _ => a) ((w : Γ) * x) = (W : Set Γ).indicator (fun _ => a) x
    by_cases hx : x ∈ W
    · rw [Set.indicator_of_mem (W.mul_mem w.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      exact fun h => hx ((Subgroup.mul_mem_cancel_left W w.2).1 h)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coindSingleFun_apply (a : V) (x : Γ) :
    (coindSingleFun (k := k) W V a).1 x = (W : Set Γ).indicator (fun _ => a) x :=
  rfl

def coindSingle : Rep.trivial k W V ⟶ Rep.res W.subtype (Rep.coind W.subtype (Rep.trivial k W V)) :=
  Rep.ofHom ⟨{ toFun := coindSingleFun W V
               map_add' := fun a b => Subtype.ext (funext fun x => by
                 change (W : Set Γ).indicator (fun _ => a + b) x =
                   (W : Set Γ).indicator (fun _ => a) x + (W : Set Γ).indicator (fun _ => b) x
                 by_cases hx : x ∈ W <;> simp [hx])
               map_smul' := fun c a => Subtype.ext (funext fun x => by
                 change (W : Set Γ).indicator (fun _ => c • a) x =
                   c • (W : Set Γ).indicator (fun _ => a) x
                 by_cases hx : x ∈ W <;> simp [hx]) }, fun w => by
    refine LinearMap.ext fun a => Subtype.ext (funext fun x => ?_)
    change (W : Set Γ).indicator (fun _ => a) x = (W : Set Γ).indicator (fun _ => a) (x * w)
    by_cases hx : x ∈ W
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (W.mul_mem hx w.2)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      exact fun h => hx ((Subgroup.mul_mem_cancel_right W w.2).1 h)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coindSingle_hom_apply (a : V) (x : Γ) :
    ((coindSingle (k := k) W V).hom a).1 x = (W : Set Γ).indicator (fun _ => a) x :=
  rfl

variable (D : Rep.{u} k Γ)

def coindDualPairingFun (f : Rep.coind W.subtype (Rep.trivial k W V))
    (μ : Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V))) :
    Rep.coind W.subtype (Rep.res W.subtype D) :=
  ⟨fun x => (μ.1 x : V →ₗ[k] D) (f.1 x), fun w x => by
    have hμ : μ.1 ((w : Γ) * x) = _ := μ.2 w x
    have hf : f.1 ((w : Γ) * x) = _ := f.2 w x
    change (μ.1 ((w : Γ) * x) : V →ₗ[k] D) (f.1 ((w : Γ) * x)) =
      D.ρ (w : Γ) ((μ.1 x : V →ₗ[k] D) (f.1 x))
    rw [hμ, hf]
    rfl⟩

def coindDualPairing :
    Rep.coind W.subtype (Rep.trivial k W V) ⊗
        Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)) ⟶
      Rep.coind W.subtype (Rep.res W.subtype D) :=
  pairingHom (LinearMap.mk₂ k (coindDualPairingFun W V D)
      (fun _ _ μ => Subtype.ext (funext fun x => (μ.1 x : V →ₗ[k] D).map_add _ _))
      (fun _ _ μ => Subtype.ext (funext fun x => (μ.1 x : V →ₗ[k] D).map_smul _ _))
      (fun _ _ _ => Subtype.ext (funext fun _ => rfl))
      (fun _ _ _ => Subtype.ext (funext fun _ => rfl)))
    fun _ _ _ => Subtype.ext (funext fun _ => rfl)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coindDualPairing_tmul (f : Rep.coind W.subtype (Rep.trivial k W V))
    (μ : Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V))) (x : Γ) :
    ((coindDualPairing W V D).hom (f ⊗ₜ[k] μ)).1 x = (μ.1 x : V →ₗ[k] D) (f.1 x) :=
  rfl

/- English proof (translation)
Use extensionality with `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul f μ => rfl`. Consider the case `add z z' hz hz' => simp only [map_add, hz, hz']`.
-/
theorem res_coindDualPairing_comp_coindEvalOne :
    (Rep.resFunctor W.subtype).map (coindDualPairing W V D) ≫
        coindEvalOne W (Rep.res W.subtype D) =
      resTensorHom W.subtype (coindEvalOne W (Rep.trivial k W V))
          (coindEvalOne W (dualRep (Rep.res W.subtype D) (Rep.trivial k W V))) ≫
        evalPairing (Rep.res W.subtype D) (Rep.trivial k W V) := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul f μ => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

def coindDualRestrict :
    Rep.res W.subtype (dualRep D (Rep.coind W.subtype (Rep.trivial k W V))) ⟶
      dualRep (Rep.res W.subtype D) (Rep.trivial k W V) :=
  Rep.ofHom ⟨{ toFun := fun l => (l : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) ∘ₗ
                  (coindSingle (k := k) W V).hom.toLinearMap
               map_add' := fun _ _ => rfl
               map_smul' := fun _ _ => rfl }, fun w => by
    refine LinearMap.ext fun l => LinearMap.ext fun a => ?_
    change D.ρ (w : Γ) (l ((Rep.coind W.subtype (Rep.trivial k W V)).ρ (w : Γ)⁻¹
        ((coindSingle (k := k) W V).hom a))) =
      D.ρ (w : Γ) (l ((coindSingle (k := k) W V).hom ((Rep.trivial k W V).ρ w⁻¹ a)))
    rw [Rep.hom_comm_apply]
    rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coindDualRestrict_hom_apply
    (l : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) (a : V) :
    ((coindDualRestrict W V D).hom l : V →ₗ[k] D) a = l ((coindSingle (k := k) W V).hom a) :=
  rfl

def coindDualInv :
    dualRep D (Rep.coind W.subtype (Rep.trivial k W V)) ⟶
      Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)) :=
  Rep.resCoindToHom W.subtype _ _ (coindDualRestrict W V D)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coindDualInv_hom_apply (l : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) (x : Γ)
    (a : V) :
    (((coindDualInv W V D).hom l).1 x : V →ₗ[k] D) a =
      D.ρ x (l ((Rep.coind W.subtype (Rep.trivial k W V)).ρ x⁻¹
        ((coindSingle (k := k) W V).hom a))) :=
  rfl

/- English proof (translation)
Use `Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun l => ?_))` and prove the remaining obligations. Use `LinearMap.ext fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.ρ 1 (l ((Rep.coind W.subtype (Rep.trivial k W V)).ρ 1⁻¹ ((coindSingle (k := k) W V).hom a))) = l ((coindSingle (k := k) W V).hom a)`. Simplify using `only [inv_one, map_one, Module.End.one_apply]`.
-/
theorem res_coindDualInv_comp_coindEvalOne :
    (Rep.resFunctor W.subtype).map (coindDualInv W V D) ≫
        coindEvalOne W (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)) =
      coindDualRestrict W V D := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun l => ?_))
  refine LinearMap.ext fun a => ?_
  change D.ρ 1 (l ((Rep.coind W.subtype (Rep.trivial k W V)).ρ 1⁻¹
      ((coindSingle (k := k) W V).hom a))) = l ((coindSingle (k := k) W V).hom a)
  simp only [inv_one, map_one, Module.End.one_apply]

section Sum

variable [W.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single ((h⁻¹ : Γ) : Γ ⧸ W)]`. Take `⟨w, hw⟩` from `QuotientGroup.mk_out_eq_mul W h⁻¹`. Establish `hmem : h * (((h⁻¹ : Γ) : Γ ⧸ W).out) ∈ W`. Rewrite using `[hw, ← mul_assoc, mul_inv_cancel, one_mul]`. Conclude with `w.2`.

Express the relevant statement in the definitionally equal form `(if h * (((h⁻¹ : Γ) : Γ ⧸ W).out) ∈ W then F (((h⁻¹ : Γ) : Γ ⧸ W).out) else 0) = _`. Rewrite using `[if_pos hmem, hw, hF]`. Introduce `c _ hc`. Rewrite using `[if_neg]`. Introduce `hmem`.

Apply `hc` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.out_eq' c]`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Use `W.inv_mem hmem` as an intermediate fact. Rewrite `this` using `[mul_inv_rev]`. Then use the resulting hypothesis.

Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem sum_ite_mul_out_mem {M : Type*} [AddCommMonoid M] (F : Γ → M)
    (hF : ∀ (x : Γ) (w : W), F (x * w) = F x) (h : Γ) :
    ∑ c : Γ ⧸ W, (by classical exact if h * c.out ∈ W then F c.out else 0) = F h⁻¹ := by
  classical
  rw [Finset.sum_eq_single ((h⁻¹ : Γ) : Γ ⧸ W)]
  · obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W h⁻¹
    have hmem : h * (((h⁻¹ : Γ) : Γ ⧸ W).out) ∈ W := by
      rw [hw, ← mul_assoc, mul_inv_cancel, one_mul]
      exact w.2
    change (if h * (((h⁻¹ : Γ) : Γ ⧸ W).out) ∈ W then F (((h⁻¹ : Γ) : Γ ⧸ W).out) else 0) = _
    rw [if_pos hmem, hw, hF]
  · intro c _ hc
    rw [if_neg]
    intro hmem
    apply hc
    rw [← QuotientGroup.out_eq' c]
    refine QuotientGroup.eq.2 ?_
    have := W.inv_mem hmem
    rwa [mul_inv_rev] at this
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/- English proof (translation)
Use `Subtype.ext (funext fun h => ?_)` and prove the remaining obligations. Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Establish `key` using `sum_ite_mul_out_mem W (fun x => f.1 x⁻¹) (fun x w => by`. Rewrite using `[mul_inv_rev]`. Conclude with `coind_trivial_apply_mul W V f w⁻¹ x⁻¹) h`.

Rewrite `key` using `[inv_inv]`. Rewrite using `[← key]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(W : Set Γ).indicator (fun _ => f.1 c.out⁻¹) (h * c.out) = _`. Rewrite using `[Set.indicator_apply]`.

Both sides reduce to the same expression.
-/
theorem sum_coindSingle (f : Rep.coind W.subtype (Rep.trivial k W V)) :
    ∑ c : Γ ⧸ W, (Rep.coind W.subtype (Rep.trivial k W V)).ρ c.out
      ((coindSingle (k := k) W V).hom (f.1 c.out⁻¹)) = f := by
  classical
  refine Subtype.ext (funext fun h => ?_)
  rw [Submodule.coe_sum, Finset.sum_apply]
  have key := sum_ite_mul_out_mem W (fun x => f.1 x⁻¹) (fun x w => by
    rw [mul_inv_rev]
    exact coind_trivial_apply_mul W V f w⁻¹ x⁻¹) h
  rw [inv_inv] at key
  rw [← key]
  refine Finset.sum_congr rfl fun c _ => ?_
  change (W : Set Γ).indicator (fun _ => f.1 c.out⁻¹) (h * c.out) = _
  rw [Set.indicator_apply]
  rfl

def coindDualHom :
    Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)) ⟶
      dualRep D (Rep.coind W.subtype (Rep.trivial k W V)) :=
  Rep.tensorHomEquiv _ _ _ (coindDualPairing W V D ≫ coindTrace W D)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coindDualHom_hom_apply
    (μ : Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)))
    (f : Rep.coind W.subtype (Rep.trivial k W V)) :
    ((coindDualHom W V D).hom μ : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) f =
      (coindTrace W D).hom ((coindDualPairing W V D).hom (f ⊗ₜ[k] μ)) :=
  rfl

/- English proof (translation)
Use extensionality with `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul f μ => rfl`. Consider the case `add z z' hz hz' => simp only [map_add, hz, hz']`.
-/
theorem tensorHom_coindDualHom_evalPairing :
    (𝟙 _ ⊗ₘ coindDualHom W V D) ≫ evalPairing D (Rep.coind W.subtype (Rep.trivial k W V)) =
      coindDualPairing W V D ≫ coindTrace W D := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul f μ => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

/- English proof (translation)
Use `Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun l => ?_))` and prove the remaining obligations. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(coindTrace W D).hom ((coindDualPairing W V D).hom (f ⊗ₜ[k] (coindDualInv W V D).hom l)) = (l : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) f`. Rewrite using `[coindTrace_hom_apply]`. Use `conv_rhs => rw [← sum_coindSingle W V f, map_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.ρ c.out (D.ρ c.out⁻¹ (l ((Rep.coind W.subtype (Rep.trivial k W V)).ρ c.out⁻¹⁻¹ ((coindSingle (k := k) W V).hom (f.1 c.out⁻¹))))) = _`. Rewrite using `[inv_inv, Representation.self_inv_apply]`.
-/
theorem coindDualInv_comp_coindDualHom :
    coindDualInv W V D ≫ coindDualHom W V D = 𝟙 _ := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun l => ?_))
  refine LinearMap.ext fun f => ?_
  change (coindTrace W D).hom ((coindDualPairing W V D).hom (f ⊗ₜ[k] (coindDualInv W V D).hom l)) =
    (l : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) f
  rw [coindTrace_hom_apply]
  conv_rhs => rw [← sum_coindSingle W V f, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  change D.ρ c.out (D.ρ c.out⁻¹ (l ((Rep.coind W.subtype (Rep.trivial k W V)).ρ c.out⁻¹⁻¹
    ((coindSingle (k := k) W V).hom (f.1 c.out⁻¹))))) = _
  rw [inv_inv, Representation.self_inv_apply]

/- English proof (translation)
Use `Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun μ => ?_))` and prove the remaining obligations. Use `Subtype.ext (funext fun h => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(((coindDualInv W V D).hom ((coindDualHom W V D).hom μ)).1 h : V →ₗ[k] D) = (μ.1 h : V →ₗ[k] D)`. Use `LinearMap.ext fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.ρ h ((coindTrace W D).hom ((coindDualPairing W V D).hom ((Rep.coind W.subtype (Rep.trivial k W V)).ρ h⁻¹ ((coindSingle (k := k) W V).hom a) ⊗ₜ[k] μ))) = (μ.1 h : V →ₗ[k] D) a`.

Rewrite using `[coindTrace_hom_apply, map_sum]`. Establish `key` using `sum_ite_mul_out_mem W (fun x => D.ρ h (D.ρ x ((μ.1 x⁻¹ : V →ₗ[k] D) a))) (fun x w => by`. Establish `hμ : μ.1 ((w⁻¹ : W) * x⁻¹) = _` using `μ.2 w⁻¹ x⁻¹`. Express the relevant statement in the definitionally equal form `D.ρ h (D.ρ (x * w) ((μ.1 (x * w)⁻¹ : V →ₗ[k] D) a)) = _`. Rewrite using `[mul_inv_rev]`.

Express the relevant statement in the definitionally equal form `D.ρ h (D.ρ (x * w) ((μ.1 ((w⁻¹ : W) * x⁻¹) : V →ₗ[k] D) a)) = _`. Rewrite using `[hμ]`. Express the relevant statement in the definitionally equal form `D.ρ h (D.ρ (x * w) (D.ρ ((w⁻¹ : W) : Γ) ((μ.1 x⁻¹ : V →ₗ[k] D) ((Rep.trivial k W V).ρ (w⁻¹)⁻¹ a)))) = _`. Rewrite using `[map_mul, Module.End.mul_apply]`. Use `congr 2`.

Express the relevant statement in the definitionally equal form `D.ρ (w : Γ) (D.ρ (w : Γ)⁻¹ _) = _`. Rewrite using `[Representation.self_inv_apply]`. Use the proof step `rfl) h`. Rewrite `key` using `[inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[← key]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.ρ h (D.ρ c.out ((μ.1 c.out⁻¹ : V →ₗ[k] D) ((W : Set Γ).indicator (fun _ => a) (c.out⁻¹ * h⁻¹)))) = _`. Distinguish the cases in `hc : h * c.out ∈ W`. Rewrite using `[if_pos hc, Set.indicator_of_mem]`. Rewrite using `[← mul_inv_rev]`.

Conclude with `W.inv_mem hc`. Rewrite using `[if_neg hc, Set.indicator_of_notMem, map_zero, map_zero, map_zero]`. Introduce `hmem`. Apply `hc` to reduce the goal to its premises. Use `W.inv_mem hmem` as an intermediate fact.

Rewrite `this` using `[mul_inv_rev, inv_inv, inv_inv]`. Then use the resulting hypothesis.
-/
theorem coindDualHom_comp_coindDualInv :
    coindDualHom W V D ≫ coindDualInv W V D = 𝟙 _ := by
  classical
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun μ => ?_))
  refine Subtype.ext (funext fun h => ?_)
  change (((coindDualInv W V D).hom ((coindDualHom W V D).hom μ)).1 h : V →ₗ[k] D) =
    (μ.1 h : V →ₗ[k] D)
  refine LinearMap.ext fun a => ?_
  change D.ρ h ((coindTrace W D).hom ((coindDualPairing W V D).hom
    ((Rep.coind W.subtype (Rep.trivial k W V)).ρ h⁻¹ ((coindSingle (k := k) W V).hom a) ⊗ₜ[k] μ))) =
      (μ.1 h : V →ₗ[k] D) a
  rw [coindTrace_hom_apply, map_sum]
  have key := sum_ite_mul_out_mem W (fun x => D.ρ h (D.ρ x ((μ.1 x⁻¹ : V →ₗ[k] D) a)))
    (fun x w => by
      have hμ : μ.1 ((w⁻¹ : W) * x⁻¹) = _ := μ.2 w⁻¹ x⁻¹
      change D.ρ h (D.ρ (x * w) ((μ.1 (x * w)⁻¹ : V →ₗ[k] D) a)) = _
      rw [mul_inv_rev]
      change D.ρ h (D.ρ (x * w) ((μ.1 ((w⁻¹ : W) * x⁻¹) : V →ₗ[k] D) a)) = _
      rw [hμ]
      change D.ρ h (D.ρ (x * w) (D.ρ ((w⁻¹ : W) : Γ) ((μ.1 x⁻¹ : V →ₗ[k] D)
        ((Rep.trivial k W V).ρ (w⁻¹)⁻¹ a)))) = _
      rw [map_mul, Module.End.mul_apply]
      congr 2
      change D.ρ (w : Γ) (D.ρ (w : Γ)⁻¹ _) = _
      rw [Representation.self_inv_apply]
      rfl) h
  rw [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at key
  rw [← key]
  refine Finset.sum_congr rfl fun c _ => ?_
  change D.ρ h (D.ρ c.out ((μ.1 c.out⁻¹ : V →ₗ[k] D)
    ((W : Set Γ).indicator (fun _ => a) (c.out⁻¹ * h⁻¹)))) = _
  by_cases hc : h * c.out ∈ W
  · rw [if_pos hc, Set.indicator_of_mem]
    rw [← mul_inv_rev]
    exact W.inv_mem hc
  · rw [if_neg hc, Set.indicator_of_notMem, map_zero, map_zero, map_zero]
    intro hmem
    apply hc
    have := W.inv_mem hmem
    rwa [mul_inv_rev, inv_inv, inv_inv] at this

def coindDualIso :
    Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)) ≅
      dualRep D (Rep.coind W.subtype (Rep.trivial k W V)) where
  hom := coindDualHom W V D
  inv := coindDualInv W V D
  hom_inv_id := coindDualHom_comp_coindDualInv W V D
  inv_hom_id := coindDualInv_comp_coindDualHom W V D

end Sum

end Module

end GroundTheory.ProfCoh

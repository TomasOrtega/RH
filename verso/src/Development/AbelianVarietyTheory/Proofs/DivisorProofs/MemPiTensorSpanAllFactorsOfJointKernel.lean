import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClasses
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.JointKer

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

/- English proof (translation)
Rewrite using `[atPl, PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = w`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`.
-/
theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

/- English proof (translation)
Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r x`. Rewrite using `[map_smul, map_smul, map_smul, GlobalTheory.TensorFactorUnique.contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]`. Use `congr 1`. Rewrite using `[mul_comm]`.

Use `congr 1`. Conclude with `Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add]`.
-/
theorem dual_contr (f : ∀ i, Module.Dual ℂ (V i)) (w : T) (ν : Module.Dual ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    ν (GlobalTheory.TensorFactorUnique.contr f w y) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update f w ν)) y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, GlobalTheory.TensorFactorUnique.contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

/- English proof (translation)
Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r x`. Rewrite using `[map_smul, map_smul, map_smul, atPl_tprod, GlobalTheory.TensorFactorUnique.contr_tprod, GlobalTheory.TensorFactorUnique.contr_tprod, map_smul, Function.update_self, LinearMap.map_smul]`. Use `congr 2`. Conclude with `Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem contr_atPl (f : ∀ i, Module.Dual ℂ (V i)) (w : T) (L : Module.End ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    GlobalTheory.TensorFactorUnique.contr f w (atPl w L y) = L (GlobalTheory.TensorFactorUnique.contr f w y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, atPl_tprod, GlobalTheory.TensorFactorUnique.contr_tprod, GlobalTheory.TensorFactorUnique.contr_tprod,
      map_smul, Function.update_self, LinearMap.map_smul]
    congr 2
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Apply `GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib` to reduce the goal to its premises. Introduce `f`. Establish `hv : g (GlobalTheory.TensorFactorUnique.contr f w y) = 0` using `hg _ fun L hL => by rw [← contr_atPl, hy L hL, map_zero]`. Establish `h` using `dual_contr f w (f w) (atPl w g y)`. Rewrite `h` using `[contr_atPl, hv, map_zero, Function.update_eq_self]`.

Conclude with `h.symm`.
-/
theorem atPl_eq_zero_of_common (w : T) (F : Set (Module.End ℂ (V w))) (g : Module.End ℂ (V w))
    (hg : ∀ v, (∀ L ∈ F, L v = 0) → g v = 0) (y : ⨂[ℂ] i, V i) (hy : ∀ L ∈ F, atPl w L y = 0) :
    atPl w g y = 0 := by
  apply GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib
  intro f
  have hv : g (GlobalTheory.TensorFactorUnique.contr f w y) = 0 := hg _ fun L hL => by rw [← contr_atPl, hy L hL, map_zero]
  have h := dual_contr f w (f w) (atPl w g y)
  rw [contr_atPl, hv, map_zero, Function.update_eq_self] at h
  exact h.symm

/- English proof (translation)
Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r x`. Rewrite using `[map_smul, map_smul, atPl_tprod, atPl_tprod, LinearMap.sub_apply, Module.End.one_apply, MultilinearMap.map_update_sub, Function.update_eq_self, smul_sub]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`. Normalize the expressions using the abelian group laws.
-/
theorem atPl_sub_one (w : T) (p : Module.End ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    atPl w (p - 1) y = atPl w p y - y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, atPl_tprod, atPl_tprod, LinearMap.sub_apply, Module.End.one_apply,
      MultilinearMap.map_update_sub, Function.update_eq_self, smul_sub]
  | add a b ha hb => rw [map_add, map_add, ha, hb]; abel

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective A.subtype (Submodule.ker_subtype _)`. Use `⟨A.subtype ∘ₗ g, fun v => (g v).2, fun v hv => ?_⟩` and prove the remaining obligations. Use `congrArg (fun h => ((h ⟨v, hv⟩ : A) : M)) hg` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_proj {M : Type} [AddCommGroup M] [Module ℂ M] (A : Submodule ℂ M) :
    ∃ π : Module.End ℂ M, (∀ v, π v ∈ A) ∧ ∀ v ∈ A, π v = v := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.subtype (Submodule.ker_subtype _)
  refine ⟨A.subtype ∘ₗ g, fun v => (g v).2, fun v hv => ?_⟩
  have := congrArg (fun h => ((h ⟨v, hv⟩ : A) : M)) hg
  simpa using this

end GlobalTheory.HoweR.JointKer

namespace GlobalTheory.HoweR

open JointKer

/- English proof (translation)
Introduce `T _ _ V _ _ L H hH y hy`. Use `choose p hpK hpid using fun w => exists_proj (H w)`. Establish `hfix : ∀ w, atPl w (p w) y = y`. Introduce `w`. Establish `h0` using `atPl_eq_zero_of_common w (L w) (p w - 1) (fun v hv => by`.

Rewrite using `[LinearMap.sub_apply, Module.End.one_apply, hpid w v (hH w v hv), sub_self]) y (hy w)`. Rewrite `h0` using `[atPl_sub_one]`. Conclude with `sub_eq_zero.1 h0`. Establish `hmap : ∀ s : Finset T, PiTensorProduct.map (fun w => if w ∈ s then p w else (LinearMap.id : V w →ₗ[ℂ] V w)) y = y`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [PiTensorProduct.map_id]`. Consider the case `insert a s ha ih`. Establish `e : (fun w => if w ∈ insert a s then p w else (LinearMap.id : V w →ₗ[ℂ] V w)) = fun w => (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) a (p a) w) ∘ₗ (if w ∈ s then p w else LinearMap.id)`. Use function extensionality and compare the values at `w`.

Distinguish the cases in `hw : w = a`. Substitute `hw` using the available equality. Simplify using `[ha]`. Simplify using `[hw, Function.update_of_ne hw]`. Rewrite using `[e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]`.

Conclude with `hfix a`. Establish `hy' : PiTensorProduct.map p y = y`. Use `hmap Finset.univ` as an intermediate fact. Simplify using `using this`. Rewrite using `[← hy']`.

Use `clear hy' hmap hfix hy`. Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f`. Rewrite using `[map_smul, PiTensorProduct.map_tprod]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun w => p w (f w), fun w => hpK w _, rfl⟩)`.

Consider the case `add x z hx hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hz`.
-/
theorem mem_tensAll_of_killed : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (L : ∀ w, Set (Module.End ℂ (V w))) (H : ∀ w, Submodule ℂ (V w)),
    (∀ w v, (∀ l ∈ L w, l v = 0) → v ∈ H w) → ∀ y : PiTensorProduct ℂ V, (∀ w, ∀ l ∈ L w, atPl w l y = 0) →
    y ∈ tensAll H := by
  intro T _ _ V _ _ L H hH y hy
  choose p hpK hpid using fun w => exists_proj (H w)
  have hfix : ∀ w, atPl w (p w) y = y := by
    intro w
    have h0 := atPl_eq_zero_of_common w (L w) (p w - 1) (fun v hv => by
        rw [LinearMap.sub_apply, Module.End.one_apply, hpid w v (hH w v hv), sub_self]) y (hy w)
    rw [atPl_sub_one] at h0
    exact sub_eq_zero.1 h0
  have hmap : ∀ s : Finset T,
      PiTensorProduct.map (fun w => if w ∈ s then p w else (LinearMap.id : V w →ₗ[ℂ] V w)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [PiTensorProduct.map_id]
    | insert a s ha ih =>
      have e : (fun w => if w ∈ insert a s then p w else (LinearMap.id : V w →ₗ[ℂ] V w)) =
          fun w => (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) a (p a) w) ∘ₗ
            (if w ∈ s then p w else LinearMap.id) := by
        funext w
        by_cases hw : w = a
        · subst hw
          simp [ha]
        · simp [hw, Function.update_of_ne hw]
      rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
      exact hfix a
  have hy' : PiTensorProduct.map p y = y := by
    have := hmap Finset.univ
    simpa using this
  rw [← hy']
  clear hy' hmap hfix hy
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun w => p w (f w), fun w => hpK w _, rfl⟩)
  | add x z hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz

end GlobalTheory.HoweR

end

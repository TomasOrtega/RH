import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.HartFlatBaseChange

def divIdeal (A S X : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup X] [Module S X]
    (a : A) (y : X) : Ideal A where
  carrier := {u | ∃ x : X, algebraMap A S u • y = algebraMap A S a • x}
  add_mem' := by
    rintro u v ⟨x, hx⟩ ⟨x', hx'⟩
    exact ⟨x + x', by rw [map_add, add_smul, hx, hx', smul_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c u ⟨x, hx⟩
    refine ⟨algebraMap A S c • x, ?_⟩
    rw [smul_eq_mul, map_mul, mul_smul, hx, smul_comm]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul o n => simp [LinearMap.lTensor_tmul, algebraMap_smul, TensorProduct.tmul_smul]`. Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`.
-/
theorem lTensor_smul_id_apply (R M O : Type) [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    [Algebra R O] (r : R) (x : O ⊗[R] M) :
    (r • LinearMap.id : M →ₗ[R] M).lTensor O x = algebraMap R O r • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o n => simp [LinearMap.lTensor_tmul, algebraMap_smul, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

end GlobalTheory.HartFlatBaseChange

open GlobalTheory.HartFlatBaseChange in
/- English proof (translation)
Introduce `A R M O _ _ _ _ _ _ _ _ _ _ _ hM a ha m hm`. Take `⟨s, hs⟩` from `(IsNoetherian.noetherian (divIdeal A O (O ⊗[R] M) a m) : Submodule.FG _)`. Establish `hsI : ∀ b ∈ s, b ∈ divIdeal A O (O ⊗[R] M) a m` using `fun b hb => hs ▸ Ideal.subset_span hb`. Set `f : M →ₗ[R] M` to `algebraMap A R a • LinearMap.id`. Set `N : Submodule R M` to `LinearMap.range f`.

Set `g : M →ₗ[R] (s → M ⧸ N)` to `LinearMap.pi fun i => N.mkQ ∘ₗ (algebraMap A R i.1 • LinearMap.id)`. Establish `hex : Function.Exact f g`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `hyI : divIdeal A O (O ⊗[R] M) a m ≤ divIdeal A R M a y`. Rewrite using `[← hs, Ideal.span_le]`. Introduce `b hb`. Use `congrFun hy ⟨b, hb⟩` as an intermediate fact. Simplify using `only [g, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N, LinearMap.mem_range] at this`.

Take `⟨x, hx⟩` from `this`. Conclude with `⟨x, by simpa [f] using hx.symm⟩`. Take `⟨m', hm'⟩` from `hM a ha y fun p hp hp1 => by`. Take `⟨u, hup, hu⟩` from `hm p hp hp1`. Conclude with `⟨u, hup, hyI hu⟩`.

Conclude with `⟨m', by simp [f, hm']⟩`. Introduce and unpack `⟨x, rfl⟩`. Use function extensionality and compare the values at `i`. Simplify using `only [g, f, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N, LinearMap.mem_range]`. Conclude with `⟨algebraMap A R i.1 • x, by simp [f, smul_comm (algebraMap A R a)]⟩`.

Establish `hexO` using `Module.Flat.lTensor_exact O hex`. Establish `hcomp : ∀ (z : O ⊗[R] (s → M ⧸ N)) (i : s), TensorProduct.piRight R R O (fun _ : s => M ⧸ N) z i = (LinearMap.proj i).lTensor O z`. Introduce `z i`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul o n => simp [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]`. Consider the case `add x y hx hy => rw [map_add, Pi.add_apply, hx, hy, map_add]`. Establish `hg : g.lTensor O m = 0`. Apply `(TensorProduct.piRight R R O (fun _ : s => M ⧸ N)).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Rewrite using `[hcomp, map_zero, Pi.zero_apply, ← LinearMap.lTensor_comp_apply]`. Establish `hpg : (LinearMap.proj i).comp g = N.mkQ ∘ₗ (algebraMap A R i.1 • LinearMap.id)` using `rfl`. Take `⟨m', hm'⟩` from `hsI i.1 i.2`. Rewrite using `[hpg, LinearMap.lTensor_comp_apply, lTensor_smul_id_apply, ← IsScalarTower.algebraMap_apply, hm', IsScalarTower.algebraMap_apply A R O, ← lTensor_smul_id_apply, ← LinearMap.lTensor_comp_apply, LinearMap.range_mkQ_comp, LinearMap.lTensor_zero, LinearMap.zero_apply]`. Take `⟨m', hm'⟩` from `(hexO m).1 hg`.

Conclude with `⟨m', by rw [← hm', lTensor_smul_id_apply, ← IsScalarTower.algebraMap_apply]⟩`.
-/
theorem GlobalTheory.GoodEtale.hart_tensor_of_flat : ∀ (A R M O : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module R M] [CommRing O] [Algebra R O] [Algebra A O] [IsScalarTower A R O]
    [Module.Flat R O], GlobalTheory.GoodEtale.Hart A R M → GlobalTheory.GoodEtale.Hart A O (O ⊗[R] M) := by
  intro A R M O _ _ _ _ _ _ _ _ _ _ _ hM a ha m hm
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (divIdeal A O (O ⊗[R] M) a m) : Submodule.FG _)
  have hsI : ∀ b ∈ s, b ∈ divIdeal A O (O ⊗[R] M) a m := fun b hb => hs ▸ Ideal.subset_span hb
  let f : M →ₗ[R] M := algebraMap A R a • LinearMap.id
  let N : Submodule R M := LinearMap.range f
  let g : M →ₗ[R] (s → M ⧸ N) := LinearMap.pi fun i => N.mkQ ∘ₗ (algebraMap A R i.1 • LinearMap.id)
  have hex : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      have hyI : divIdeal A O (O ⊗[R] M) a m ≤ divIdeal A R M a y := by
        rw [← hs, Ideal.span_le]
        intro b hb
        have := congrFun hy ⟨b, hb⟩
        simp only [g, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N, LinearMap.mem_range] at this
        obtain ⟨x, hx⟩ := this
        exact ⟨x, by simpa [f] using hx.symm⟩
      obtain ⟨m', hm'⟩ := hM a ha y fun p hp hp1 => by
        obtain ⟨u, hup, hu⟩ := hm p hp hp1
        exact ⟨u, hup, hyI hu⟩
      exact ⟨m', by simp [f, hm']⟩
    · rintro ⟨x, rfl⟩
      funext i
      simp only [g, f, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N, LinearMap.mem_range]
      exact ⟨algebraMap A R i.1 • x, by simp [f, smul_comm (algebraMap A R a)]⟩
  have hexO := Module.Flat.lTensor_exact O hex
  have hcomp : ∀ (z : O ⊗[R] (s → M ⧸ N)) (i : s),
      TensorProduct.piRight R R O (fun _ : s => M ⧸ N) z i = (LinearMap.proj i).lTensor O z := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul o n => simp [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    | add x y hx hy => rw [map_add, Pi.add_apply, hx, hy, map_add]
  have hg : g.lTensor O m = 0 := by
    apply (TensorProduct.piRight R R O (fun _ : s => M ⧸ N)).injective
    funext i
    rw [hcomp, map_zero, Pi.zero_apply, ← LinearMap.lTensor_comp_apply]
    have hpg : (LinearMap.proj i).comp g = N.mkQ ∘ₗ (algebraMap A R i.1 • LinearMap.id) := rfl
    obtain ⟨m', hm'⟩ := hsI i.1 i.2
    rw [hpg, LinearMap.lTensor_comp_apply, lTensor_smul_id_apply, ← IsScalarTower.algebraMap_apply,
      hm', IsScalarTower.algebraMap_apply A R O, ← lTensor_smul_id_apply, ← LinearMap.lTensor_comp_apply,
      LinearMap.range_mkQ_comp, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨m', hm'⟩ := (hexO m).1 hg
  exact ⟨m', by rw [← hm', lTensor_smul_id_apply, ← IsScalarTower.algebraMap_apply]⟩

import Mathlib
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dens

open Polynomial Cardinal

section Schur

variable {R V : Type} [Ring R] [Algebra ℂ R] [AddCommGroup V] [Module ℂ V] [Module R V]
  [IsScalarTower ℂ R V] [IsSimpleModule R V]

/- English proof (translation)
Proceed by induction on `hn : p.natDegree generalizing p with`. Consider the case `zero`. It suffices to derive a contradiction. Rewrite `hn` using `[Polynomial.natDegree_eq_zero]`. Take `⟨c, rfl⟩` from `hn`.

Establish `hc : c ≠ 0` using `fun h => hp (by rw [h, map_zero])`. Establish `hnt : Nontrivial V` using `IsSimpleModule.nontrivial R V`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Rewrite `hφ` using `[aeval_C]`. Establish `h3` using `LinearMap.congr_fun hφ v`.

Rewrite `h3` using `[Module.algebraMap_end_apply, LinearMap.zero_apply]`. Conclude with `hv ((smul_eq_zero.mp h3).resolve_left hc)`. Consider the case `succ n ih`. Establish `hdeg : p.degree ≠ 0`. Introduce `h`.

Rewrite `h` using `[Polynomial.degree_eq_natDegree hp]`. Normalize the coercions in `at h`. Use linear arithmetic over natural numbers and integers. Take `⟨a, ha⟩` from `IsAlgClosed.exists_root p hdeg`. Establish `hpq : p = (X - C a) * (p /ₘ (X - C a))` using `(Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm`.

Establish `hq0 : p /ₘ (X - C a) ≠ 0`. Introduce `h`. Apply `hp` to reduce the goal to its premises. Rewrite using `[hpq, h, mul_zero]`. Establish `hqdeg : (p /ₘ (X - C a)).natDegree = n`.

Establish `h3` using `congrArg Polynomial.natDegree hpq`. Rewrite `h3` using `[Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0, Polynomial.natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Rewrite `hφ` using `[hpq, map_mul, map_sub, aeval_X, aeval_C]`. Break down `LinearMap.injective_or_eq_zero (φ - algebraMap ℂ (Module.End R V) a) with hinj | h0` into its components or cases.

Apply `ih hq0 _ hqdeg` to reduce the goal to its premises. Use extensionality with `v`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[LinearMap.zero_apply, map_zero]`. Conclude with `LinearMap.congr_fun hφ v`.

Conclude with `⟨a, sub_eq_zero.mp h0⟩`.
-/
theorem exists_eq_algebraMap_of_aeval_eq_zero (φ : Module.End R V) {p : ℂ[X]} (hp : p ≠ 0)
    (hφ : aeval φ p = 0) : ∃ c : ℂ, φ = algebraMap ℂ (Module.End R V) c := by
  induction hn : p.natDegree generalizing p with
  | zero =>
    exfalso
    rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    have hc : c ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hnt : Nontrivial V := IsSimpleModule.nontrivial R V
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    rw [aeval_C] at hφ
    have h3 := LinearMap.congr_fun hφ v
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply] at h3
    exact hv ((smul_eq_zero.mp h3).resolve_left hc)
  | succ n ih =>
    have hdeg : p.degree ≠ 0 := by
      intro h
      rw [Polynomial.degree_eq_natDegree hp] at h
      norm_cast at h
      omega
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
    have hpq : p = (X - C a) * (p /ₘ (X - C a)) := (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm
    have hq0 : p /ₘ (X - C a) ≠ 0 := by
      intro h
      apply hp
      rw [hpq, h, mul_zero]
    have hqdeg : (p /ₘ (X - C a)).natDegree = n := by
      have h3 := congrArg Polynomial.natDegree hpq
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0, Polynomial.natDegree_X_sub_C] at h3
      omega
    rw [hpq, map_mul, map_sub, aeval_X, aeval_C] at hφ
    rcases LinearMap.injective_or_eq_zero (φ - algebraMap ℂ (Module.End R V) a) with hinj | h0
    · apply ih hq0 _ hqdeg
      ext v
      apply hinj
      rw [LinearMap.zero_apply, map_zero]
      exact LinearMap.congr_fun hφ v
    · exact ⟨a, sub_eq_zero.mp h0⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hnt : Nontrivial V` using `IsSimpleModule.nontrivial R V`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Establish `htr : ∀ p : ℂ[X], p ≠ 0 → aeval φ p ≠ 0`.

Introduce `p hp h0`. Take `⟨c, hc⟩` from `exists_eq_algebraMap_of_aeval_eq_zero φ hp h0`. Take `⟨m, hm⟩` from `hne c`. Conclude with `hm (by rw [hc, Module.algebraMap_end_apply])`. Establish `hv0 : ∀ p : ℂ[X], aeval φ p v = 0 → p = 0`.

Introduce `p hpv`. Assume the negation of the conclusion as `hp`. Break down `LinearMap.injective_or_eq_zero (aeval φ p) with hinj | h0` into its components or cases. Conclude with `hv (hinj (by rw [hpv, map_zero]))`. Conclude with `htr p hp h0`.

Establish `hsurj : ∀ a : ℂ, Function.Surjective (aeval φ (X - C a))`. Introduce `a`. Break down `LinearMap.bijective_or_eq_zero (aeval φ (X - C a)) with hb | h0` into its components or cases. Conclude with `hb.2`. Conclude with `absurd h0 (htr _ (Polynomial.X_sub_C_ne_zero a))`.

Use `choose w hw using fun a => hsurj a v`. Establish `hli : LinearIndependent ℂ w`. Rewrite using `[linearIndependent_iff']`. Introduce `s g hg i hi`. Establish `key : ∀ k ∈ s, aeval φ (∏ j ∈ s, (X - C j)) (w k) = aeval φ (∏ j ∈ s.erase k, (X - C j)) v`.

Introduce `k hk`. Rewrite using `[← Finset.prod_erase_mul _ _ hk, map_mul, Module.End.mul_apply, hw]`. Establish `h3` using `congrArg (aeval φ (∏ j ∈ s, (X - C j))) hg`. Rewrite `h3` using `[map_sum, map_zero]`. Simplify using `only [LinearMap.map_smul_of_tower] at h3`.

Rewrite `h3` using `[Finset.sum_congr rfl (fun k hk => by rw [key k hk])]`. Establish `h4 : aeval φ (∑ k ∈ s, C (g k) * ∏ j ∈ s.erase k, (X - C j)) v = 0`. Rewrite using `[← h3, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]`.

Establish `hP` using `hv0 _ h4`. Establish `h5` using `congrArg (Polynomial.eval i) hP`. Establish `hz : ∀ k ∈ s.erase i, Polynomial.eval i (C (g k) * ∏ j ∈ s.erase k, (X - C j)) = 0`. Introduce `k hk`. Establish `hki` using `Finset.ne_of_mem_erase hk`.

Establish `him : i ∈ s.erase k` using `Finset.mem_erase_of_ne_of_mem (Ne.symm hki) hi`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_prod, Finset.prod_eq_zero him (by simp), mul_zero]`. Rewrite `h5` using `[Polynomial.eval_finsetSum, ← Finset.sum_erase_add _ _ hi, Finset.sum_eq_zero hz, zero_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_zero]`. Establish `hne2 : ∏ j ∈ s.erase i, Polynomial.eval i (X - C j) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun j hj => by`. Rewrite using `[Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`.

Conclude with `sub_ne_zero.mpr (Finset.ne_of_mem_erase hj).symm`. Conclude with `(mul_eq_zero.mp h5).resolve_right hne2`. Establish `hc` using `hli.cardinal_le_rank`. Rewrite `hc` using `[Cardinal.mk_complex]`. Conclude with `absurd (hc.trans hV) (not_le.mpr Cardinal.aleph0_lt_continuum)`.
-/
theorem exists_smul_of_rank_le_aleph0 (hV : Module.rank ℂ V ≤ ℵ₀) (φ : Module.End R V) :
    ∃ c : ℂ, ∀ m, φ m = c • m := by
  classical
  by_contra hne
  push Not at hne
  have hnt : Nontrivial V := IsSimpleModule.nontrivial R V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have htr : ∀ p : ℂ[X], p ≠ 0 → aeval φ p ≠ 0 := by
    intro p hp h0
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_aeval_eq_zero φ hp h0
    obtain ⟨m, hm⟩ := hne c
    exact hm (by rw [hc, Module.algebraMap_end_apply])
  have hv0 : ∀ p : ℂ[X], aeval φ p v = 0 → p = 0 := by
    intro p hpv
    by_contra hp
    rcases LinearMap.injective_or_eq_zero (aeval φ p) with hinj | h0
    · exact hv (hinj (by rw [hpv, map_zero]))
    · exact htr p hp h0
  have hsurj : ∀ a : ℂ, Function.Surjective (aeval φ (X - C a)) := by
    intro a
    rcases LinearMap.bijective_or_eq_zero (aeval φ (X - C a)) with hb | h0
    · exact hb.2
    · exact absurd h0 (htr _ (Polynomial.X_sub_C_ne_zero a))
  choose w hw using fun a => hsurj a v
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have key : ∀ k ∈ s, aeval φ (∏ j ∈ s, (X - C j)) (w k) = aeval φ (∏ j ∈ s.erase k, (X - C j)) v := by
      intro k hk
      rw [← Finset.prod_erase_mul _ _ hk, map_mul, Module.End.mul_apply, hw]
    have h3 := congrArg (aeval φ (∏ j ∈ s, (X - C j))) hg
    rw [map_sum, map_zero] at h3
    simp only [LinearMap.map_smul_of_tower] at h3
    rw [Finset.sum_congr rfl (fun k hk => by rw [key k hk])] at h3
    have h4 : aeval φ (∑ k ∈ s, C (g k) * ∏ j ∈ s.erase k, (X - C j)) v = 0 := by
      rw [← h3, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
    have hP := hv0 _ h4
    have h5 := congrArg (Polynomial.eval i) hP
    have hz : ∀ k ∈ s.erase i, Polynomial.eval i (C (g k) * ∏ j ∈ s.erase k, (X - C j)) = 0 := by
      intro k hk
      have hki := Finset.ne_of_mem_erase hk
      have him : i ∈ s.erase k := Finset.mem_erase_of_ne_of_mem (Ne.symm hki) hi
      rw [Polynomial.eval_mul, Polynomial.eval_prod, Finset.prod_eq_zero him (by simp), mul_zero]
    rw [Polynomial.eval_finsetSum, ← Finset.sum_erase_add _ _ hi, Finset.sum_eq_zero hz, zero_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_zero] at h5
    have hne2 : ∏ j ∈ s.erase i, Polynomial.eval i (X - C j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj => by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hj).symm
    exact (mul_eq_zero.mp h5).resolve_right hne2
  have hc := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at hc
  exact absurd (hc.trans hV) (not_le.mpr Cardinal.aleph0_lt_continuum)

end Schur

/- English proof (translation)
Set `A` to `Algebra.adjoin ℂ O`. Use `haveI : IsSimpleOrder (Submodule A V) := by`. Use `⟨fun N => ?_⟩` and prove the remaining obligations. Establish `hst : ∀ T ∈ O, ∀ x ∈ N.restrictScalars ℂ, T x ∈ N.restrictScalars ℂ`. Introduce `T hT x hx`.

Conclude with `N.smul_mem (⟨T, Algebra.subset_adjoin hT⟩ : A) hx`. Break down `hirr (N.restrictScalars ℂ) hst with h | h` into its components or cases. Use `left`. Rewrite using `[← Submodule.restrictScalars_eq_bot_iff ℂ]`. Conclude with `h`.

Use `right`. Rewrite using `[← Submodule.restrictScalars_eq_top_iff ℂ]`. Conclude with `h`. Use `haveI : IsSimpleModule A V := ⟨⟩`. Set `F : Module.End (Module.End A V) V` to `{ toFun := f map_add' := f.map_add map_smul' := fun ψ x => by`.

Take `⟨c, hc⟩` from `exists_smul_of_rank_le_aleph0 (R := A) hV ψ`. Use `show f (ψ x) = ψ (f x)`. Rewrite using `[hc, hc, f.map_smul] }`. Take `⟨r, hr⟩` from `jacobson_density F s`. Conclude with `⟨r, r.2, fun x hx => (hr x hx).symm⟩`.
-/
theorem exists_mem_adjoin_eq {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (O : Set (Module.End ℂ V)) (hV : Module.rank ℂ V ≤ ℵ₀)
    (hirr : ∀ N : Submodule ℂ V, (∀ T ∈ O, ∀ x ∈ N, T x ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : V →ₗ[ℂ] V) (s : Finset V) :
    ∃ T ∈ Algebra.adjoin ℂ O, ∀ x ∈ s, T x = f x := by
  classical
  let A := Algebra.adjoin ℂ O
  haveI : IsSimpleOrder (Submodule A V) := by
    refine ⟨fun N => ?_⟩
    have hst : ∀ T ∈ O, ∀ x ∈ N.restrictScalars ℂ, T x ∈ N.restrictScalars ℂ := by
      intro T hT x hx
      exact N.smul_mem (⟨T, Algebra.subset_adjoin hT⟩ : A) hx
    rcases hirr (N.restrictScalars ℂ) hst with h | h
    · left
      rw [← Submodule.restrictScalars_eq_bot_iff ℂ]
      exact h
    · right
      rw [← Submodule.restrictScalars_eq_top_iff ℂ]
      exact h
  haveI : IsSimpleModule A V := ⟨⟩
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun ψ x => by
        obtain ⟨c, hc⟩ := exists_smul_of_rank_le_aleph0 (R := A) hV ψ
        show f (ψ x) = ψ (f x)
        rw [hc, hc, f.map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, r.2, fun x hx => (hr x hx).symm⟩

/- English proof (translation)
Consider the cases of `nonempty_fintype α`. Establish `hcomp : ∀ (f g : ∀ a, X a →ₗ[ℂ] X a) (y : A ⊗[ℂ] PiTensorProduct ℂ X), LinearMap.lTensor A (PiTensorProduct.map fun a => f a ∘ₗ g a) y = LinearMap.lTensor A (PiTensorProduct.map f) (LinearMap.lTensor A (PiTensorProduct.map g) y)`. Introduce `f g y`. Rewrite using `[PiTensorProduct.map_comp, LinearMap.lTensor_comp_apply]`. Set `Asub : ∀ a, Subalgebra ℂ (Module.End ℂ (X a))` to `fun i => { carrier := {T | ∀ y ∈ N, LinearMap.lTensor A (PiTensorProduct.map (Function.update (fun b => (LinearMap.id : X b →ₗ[ℂ] X b)) i T)) y ∈ N} mul_mem' := fun {a b} ha hb y hy => by`.

Use `ha _ (hb y hy)` as an intermediate fact. Rewrite `this` using `[← hcomp]`. Use `this using 4` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `ρ`. Distinguish the cases in `hρ : ρ = i`.

Substitute `hρ` using the available equality. Simplify using `[Module.End.mul_eq_comp]`. Simplify using `[Function.update_of_ne hρ]`. Use the proof step `add_mem' := fun {a b} ha hb y hy => by`. Rewrite using `[PiTensorProduct.map_update_add, LinearMap.lTensor_add]`.

Conclude with `N.add_mem (ha y hy) (hb y hy)`. Use the proof step `algebraMap_mem' := fun c y hy => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul, LinearMap.lTensor_smul]`. Establish `: Function.update (fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ)) i (1 : Module.End ℂ (X i)) = fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ)` using `Function.update_eq_self i _`. Rewrite using `[this, PiTensorProduct.map_id, LinearMap.lTensor_id]`.

Conclude with `N.smul_mem c hy }`. Establish `hA : ∀ a, Algebra.adjoin ℂ (O a) ≤ Asub a` using `fun a => Algebra.adjoin_le fun T hT y hy => hN a T hT y hy`. Establish `h3 : ∀ T : ∀ a, Module.End ℂ (X a), (∀ a, T a ∈ Asub a) → ∀ y ∈ N, LinearMap.lTensor A (PiTensorProduct.map T) y ∈ N`. Introduce `T hT`. Establish `h2 : ∀ s : Finset α, ∀ y ∈ N, LinearMap.lTensor A (PiTensorProduct.map (fun a => if a ∈ s then T a else LinearMap.id)) y ∈ N`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `y hy`. Simplify using `using hy`.

Consider the case `insert j s hj ih`. Introduce `y hy`. Use `hT j _ (ih y hy)` as an intermediate fact. Rewrite `this` using `[← hcomp]`. Use `this using 4` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = j`. Substitute `hb` using the available equality. Simplify using `[hj]`. Simplify using `[hb]`.

Introduce `y hy`. Simplify using `using h2 Finset.univ y hy`. Set `b` to `fun a => Module.Free.chooseBasis ℂ (X a)`. Set `B` to `Basis.piTensorProduct b`. Set `e` to `TensorProduct.equivFinsuppOfBasisRight (M := A) B`.

Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, e x p ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hx0 (e.map_eq_zero_iff.1 (Finsupp.ext hcon))`. Use `⟨e x p, hp, ?_⟩` and prove the remaining obligations.

Establish `hsum : x = (e x).sum fun q a => a ⊗ₜ[ℂ] B q`. Rewrite using `[← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]`. Establish `hcoef : ∀ (t : PiTensorProduct ℂ X) (y : A ⊗[ℂ] PiTensorProduct ℂ X), LinearMap.lTensor A ((B.coord p).smulRight t) y = e y p ⊗ₜ[ℂ] t`. Introduce `t y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a n`. Simplify using `[e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, TensorProduct.smul_tmul']`. Consider the case `add y z hy hz => simp [hy, hz, TensorProduct.add_tmul]`. Establish `hpure : ∀ v : ∀ i, X i, e x p ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v ∈ N`.

Introduce `v`. Set `f : ∀ a, Module.End ℂ (X a)` to `fun a => ((b a).coord (p a)).smulRight (v a)`. Establish `hT : ∀ a, ∃ T ∈ Asub a, ∀ y ∈ (e x).support.image (fun q => b a (q a)), T y = f a y` using `fun a => by haveI := hnt a`. Take `⟨T, hT1, hT2⟩` from `exists_mem_adjoin_eq (O a) (hrank a) (hirr a) (f a) ((e x).support.image (fun q => b a (q a)))`. Conclude with `⟨T, hA a hT1, hT2⟩`.

Use `choose T hTA hTf using hT`. Establish `hf : PiTensorProduct.map f = (B.coord p).smulRight (PiTensorProduct.tprod ℂ v)`. Use extensionality with `w`. Simplify using `only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.smulRight_apply, Module.Basis.coord_apply, B, f, Basis.piTensorProduct_repr_tprod_apply]`. Conclude with `(PiTensorProduct.tprod ℂ).map_smul_univ _ v`.

Establish `hmap : LinearMap.lTensor A (PiTensorProduct.map T) x = LinearMap.lTensor A (PiTensorProduct.map f) x`. Rewrite using `[hsum, map_finsuppSum, map_finsuppSum]`. Use `Finsupp.sum_congr fun q hq => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]`. Use `congr 2`.

Use function extensionality and compare the values at `a`. Conclude with `hTf a _ (Finset.mem_image_of_mem _ hq)`. Establish `h4` using `h3 T hTA x hxN`. Rewrite `h4` using `[hmap, hf, hcoef]`. Then use the resulting hypothesis. Establish `hall : (⊤ : Submodule ℂ (PiTensorProduct ℂ X)) ≤ N.comap (TensorProduct.mk ℂ A (PiTensorProduct ℂ X) (e x p))`.

Rewrite using `[← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `hpure v`. Conclude with `fun y => hall (Submodule.mem_top (x := y))`.
-/
theorem exists_tmul_mem {α : Type} [Finite α] [DecidableEq α] {A : Type} [AddCommGroup A]
    [Module ℂ A] {X : α → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (O : ∀ i, Set (Module.End ℂ (X i))) (hrank : ∀ i, Module.rank ℂ (X i) ≤ Cardinal.aleph0)
    (hnt : ∀ i, Nontrivial (X i))
    (hirr : ∀ i (N : Submodule ℂ (X i)), (∀ T ∈ O i, ∀ x ∈ N, T x ∈ N) → N = ⊥ ∨ N = ⊤)
    (N : Submodule ℂ (A ⊗[ℂ] PiTensorProduct ℂ X))
    (hN : ∀ i, ∀ T ∈ O i, ∀ x ∈ N, LinearMap.lTensor A (PiTensorProduct.map
      (Function.update (fun j => (LinearMap.id : X j →ₗ[ℂ] X j)) i T)) x ∈ N)
    (x : A ⊗[ℂ] PiTensorProduct ℂ X) (hxN : x ∈ N) (hx0 : x ≠ 0) :
    ∃ a₀ : A, a₀ ≠ 0 ∧ ∀ y, a₀ ⊗ₜ[ℂ] y ∈ N := by
  classical
  cases nonempty_fintype α
  have hcomp : ∀ (f g : ∀ a, X a →ₗ[ℂ] X a) (y : A ⊗[ℂ] PiTensorProduct ℂ X),
      LinearMap.lTensor A (PiTensorProduct.map fun a => f a ∘ₗ g a) y =
        LinearMap.lTensor A (PiTensorProduct.map f) (LinearMap.lTensor A (PiTensorProduct.map g) y) := by
    intro f g y
    rw [PiTensorProduct.map_comp, LinearMap.lTensor_comp_apply]
  let Asub : ∀ a, Subalgebra ℂ (Module.End ℂ (X a)) := fun i =>
    { carrier := {T | ∀ y ∈ N, LinearMap.lTensor A (PiTensorProduct.map
        (Function.update (fun b => (LinearMap.id : X b →ₗ[ℂ] X b)) i T)) y ∈ N}
      mul_mem' := fun {a b} ha hb y hy => by
        have := ha _ (hb y hy)
        rw [← hcomp] at this
        convert this using 4
        funext ρ
        by_cases hρ : ρ = i
        · subst hρ; simp [Module.End.mul_eq_comp]
        · simp [Function.update_of_ne hρ]
      add_mem' := fun {a b} ha hb y hy => by
        rw [PiTensorProduct.map_update_add, LinearMap.lTensor_add]
        exact N.add_mem (ha y hy) (hb y hy)
      algebraMap_mem' := fun c y hy => by
        rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul, LinearMap.lTensor_smul]
        have : Function.update (fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ)) i (1 : Module.End ℂ (X i)) =
            fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ) := Function.update_eq_self i _
        rw [this, PiTensorProduct.map_id, LinearMap.lTensor_id]
        exact N.smul_mem c hy }
  have hA : ∀ a, Algebra.adjoin ℂ (O a) ≤ Asub a := fun a =>
    Algebra.adjoin_le fun T hT y hy => hN a T hT y hy
  have h3 : ∀ T : ∀ a, Module.End ℂ (X a), (∀ a, T a ∈ Asub a) →
      ∀ y ∈ N, LinearMap.lTensor A (PiTensorProduct.map T) y ∈ N := by
    intro T hT
    have h2 : ∀ s : Finset α, ∀ y ∈ N, LinearMap.lTensor A
        (PiTensorProduct.map (fun a => if a ∈ s then T a else LinearMap.id)) y ∈ N := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro y hy
        simpa using hy
      | insert j s hj ih =>
        intro y hy
        have := hT j _ (ih y hy)
        rw [← hcomp] at this
        convert this using 4
        funext b
        by_cases hb : b = j
        · subst hb; simp [hj]
        · simp [hb]
    intro y hy
    simpa using h2 Finset.univ y hy
  let b := fun a => Module.Free.chooseBasis ℂ (X a)
  let B := Basis.piTensorProduct b
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) B
  obtain ⟨p, hp⟩ : ∃ p, e x p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (e.map_eq_zero_iff.1 (Finsupp.ext hcon))
  refine ⟨e x p, hp, ?_⟩
  have hsum : x = (e x).sum fun q a => a ⊗ₜ[ℂ] B q := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hcoef : ∀ (t : PiTensorProduct ℂ X) (y : A ⊗[ℂ] PiTensorProduct ℂ X),
      LinearMap.lTensor A ((B.coord p).smulRight t) y = e y p ⊗ₜ[ℂ] t := by
    intro t y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a n =>
      simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, TensorProduct.smul_tmul']
    | add y z hy hz => simp [hy, hz, TensorProduct.add_tmul]
  have hpure : ∀ v : ∀ i, X i, e x p ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v ∈ N := by
    intro v
    let f : ∀ a, Module.End ℂ (X a) := fun a => ((b a).coord (p a)).smulRight (v a)
    have hT : ∀ a, ∃ T ∈ Asub a, ∀ y ∈ (e x).support.image (fun q => b a (q a)), T y = f a y :=
      fun a => by
        haveI := hnt a
        obtain ⟨T, hT1, hT2⟩ := exists_mem_adjoin_eq (O a) (hrank a) (hirr a) (f a)
          ((e x).support.image (fun q => b a (q a)))
        exact ⟨T, hA a hT1, hT2⟩
    choose T hTA hTf using hT
    have hf : PiTensorProduct.map f = (B.coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
      ext w
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
        LinearMap.smulRight_apply, Module.Basis.coord_apply, B, f,
        Basis.piTensorProduct_repr_tprod_apply]
      exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v
    have hmap : LinearMap.lTensor A (PiTensorProduct.map T) x =
        LinearMap.lTensor A (PiTensorProduct.map f) x := by
      rw [hsum, map_finsuppSum, map_finsuppSum]
      refine Finsupp.sum_congr fun q hq => ?_
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Basis.piTensorProduct_apply,
        PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
      congr 2
      funext a
      exact hTf a _ (Finset.mem_image_of_mem _ hq)
    have h4 := h3 T hTA x hxN
    rwa [hmap, hf, hcoef] at h4
  have hall : (⊤ : Submodule ℂ (PiTensorProduct ℂ X)) ≤
      N.comap (TensorProduct.mk ℂ A (PiTensorProduct ℂ X) (e x p)) := by
    rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hpure v
  exact fun y => hall (Submodule.mem_top (x := y))

/- English proof (translation)
Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : (v : ι) ∈ T`. Distinguish the cases in `hvi : (v : ι) = i`. Establish `hv' : v = ⟨i, hT i.2⟩` using `Subtype.ext hvi`. Substitute `hv'` using the available equality.

Simplify using the standard rewrite rules. Establish `h1 : (⟨v, hv⟩ : T) ≠ i` using `fun h => hvi (by rw [← h])`. Establish `h2 : v ≠ ⟨i, hT i.2⟩` using `fun h => hvi (by rw [h])`. Rewrite using `[dif_pos hv, Function.update_of_ne h1, Function.update_of_ne h2, dif_pos hv]`. Establish `h2 : v ≠ ⟨i, hT i.2⟩` using `fun h => hv (by rw [h]; exact i.2)`.

Rewrite using `[dif_neg hv, Function.update_of_ne h2, dif_neg hv]`.
-/
private theorem dite_update_eq_update_dite {ι : Type} [DecidableEq ι] {X : ι → Type} (T T₁ : Finset ι) (hT : T ⊆ T₁)
    (s : ∀ i, X i) [DecidableEq T] (m : ∀ v : T, X v) (i : T) (z : X i) :
    (fun v : T₁ => if h : (v : ι) ∈ T then Function.update m i z ⟨v, h⟩ else s v) =
      Function.update (fun v : T₁ => if h : (v : ι) ∈ T then m ⟨v, h⟩ else s v) ⟨i, hT i.2⟩ z := by
  funext v
  by_cases hv : (v : ι) ∈ T
  · by_cases hvi : (v : ι) = i
    · have hv' : v = ⟨i, hT i.2⟩ := Subtype.ext hvi
      subst hv'
      simp
    · have h1 : (⟨v, hv⟩ : T) ≠ i := fun h => hvi (by rw [← h])
      have h2 : v ≠ ⟨i, hT i.2⟩ := fun h => hvi (by rw [h])
      rw [dif_pos hv, Function.update_of_ne h1, Function.update_of_ne h2, dif_pos hv]
  · have h2 : v ≠ ⟨i, hT i.2⟩ := fun h => hv (by rw [h]; exact i.2)
    rw [dif_neg hv, Function.update_of_ne h2, dif_neg hv]

/- English proof (translation)
Set `f : MultilinearMap ℂ (fun v : T => X v) (PiTensorProduct ℂ fun v : T₁ => X v)` to `{ toFun := fun m => PiTensorProduct.tprod ℂ fun v : T₁ => if h : (v : ι) ∈ T then m ⟨v, h⟩ else s v map_update_add' := fun m i x y => by`. Simplify using `only [dite_update_eq_update_dite T T₁ hT s]`. Conclude with `(PiTensorProduct.tprod ℂ).map_update_add _ _ _ _`. Use the proof step `map_update_smul' := fun m i c x => by`. Simplify using `only [dite_update_eq_update_dite T T₁ hT s]`.

Conclude with `(PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }`. Use `⟨PiTensorProduct.lift f, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[PiTensorProduct.lift.tprod]`. Use `show PiTensorProduct.tprod ℂ _ = _`. Use `congr 1`.

Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : (v : ι) ∈ T`. Rewrite using `[dif_pos hv]`. Rewrite using `[dif_neg hv, hu v hv]`.
-/
theorem exists_ext {ι : Type} [DecidableEq ι] {X : ι → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (T T₁ : Finset ι) (hT : T ⊆ T₁) (s : ∀ i, X i) :
    ∃ e : (PiTensorProduct ℂ fun v : T => X v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T₁ => X v,
      ∀ u : ∀ i, X i, (∀ i ∉ T, u i = s i) →
        e (PiTensorProduct.tprod ℂ fun v : T => u v) = PiTensorProduct.tprod ℂ fun v : T₁ => u v := by
  classical
  let f : MultilinearMap ℂ (fun v : T => X v) (PiTensorProduct ℂ fun v : T₁ => X v) :=
    { toFun := fun m => PiTensorProduct.tprod ℂ fun v : T₁ => if h : (v : ι) ∈ T then m ⟨v, h⟩ else s v
      map_update_add' := fun m i x y => by
        simp only [dite_update_eq_update_dite T T₁ hT s]
        exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun m i c x => by
        simp only [dite_update_eq_update_dite T T₁ hT s]
        exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }
  refine ⟨PiTensorProduct.lift f, fun u hu => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  show PiTensorProduct.tprod ℂ _ = _
  congr 1
  funext v
  by_cases hv : (v : ι) ∈ T
  · rw [dif_pos hv]
  · rw [dif_neg hv, hu v hv]

end GlobalTheory.ThK.Dbl.Dens

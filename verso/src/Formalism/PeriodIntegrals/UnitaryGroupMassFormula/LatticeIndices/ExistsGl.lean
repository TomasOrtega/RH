import Mathlib

noncomputable section

namespace MassDataIdxLatFree

open scoped Matrix
open Module

variable {K : Type} [Field K] (O : ValuationSubring K) [IsPrincipalIdealRing O]
  {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use `haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hfg`. Use `haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'`. Set `ι` to `Module.Free.ChooseBasisIndex O M`. Set `bM : Module.Basis ι O M` to `Module.Free.chooseBasis O M`. Set `v : ι → (n → K)` to `fun i => (bM i : n → K)`.

Establish `hliO : LinearIndependent O v` using `bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)`. Establish `hli : LinearIndependent K v` using `(LinearIndependent.iff_fractionRing O K).mp hliO`. Establish `hsmul : ∀ (r : O) (w : n → K), r • w = (r : K) • w` using `fun r w => rfl`. Establish `hMsp : (M : Set (n → K)) ⊆ Submodule.span K (Set.range v)`. Introduce `y hy`.

Establish `h1` using `bM.sum_repr ⟨y, hy⟩`. Establish `h2 : y = ∑ i, (bM.repr ⟨y, hy⟩ i : K) • v i`. Establish `h3` using `congrArg (fun m : M => (m : n → K)) h1`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h3`. Use `conv_lhs => rw [← h3]`.

Both sides reduce to the same expression. Rewrite using `[h2]`. Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Establish `hsp : ⊤ ≤ Submodule.span K (Set.range v)`. Rewrite using `[← hsp]`.

Conclude with `Submodule.span_le.mpr hMsp`. Set `bK : Module.Basis ι K (n → K)` to `Module.Basis.mk hli hsp`. Establish `hbK : ∀ i, bK i = v i` using `fun i => Module.Basis.mk_apply hli hsp i`. Establish `hcard : Fintype.card ι = Fintype.card n`. Rewrite using `[← Module.finrank_eq_card_basis bK, Module.finrank_fintype_fun_eq_card]`.

Set `e : ι ≃ n` to `Fintype.equivOfCardEq hcard`. Set `Pm : Matrix n n K` to `fun i j => bK (e.symm j) i`. Set `Qm : Matrix n n K` to `fun i j => bK.repr (Pi.single j 1) (e.symm i)`. Establish `hQ : ∀ y : n → K, Qm *ᵥ y = fun i => bK.repr y (e.symm i)`. Introduce `y`.

Use function extensionality and compare the values at `i`. Establish `hy : y = ∑ j, y j • (Pi.single j (1 : K) : n → K)`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_rhs => rw [hy]`.

Simplify using `only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Qm]`. Conclude with `Finset.sum_congr rfl (fun j _ => mul_comm _ _)`. Establish `hQP : Qm * Pm = 1`. Use extensionality with `i k`. Establish `h1` using `congrFun (hQ (fun j => Pm j k)) i`.

Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mulVec, dotProduct] at h1`. Rewrite using `[h1]`. Establish `h2 : (fun j => Pm j k) = bK (e.symm k)` using `rfl`. Rewrite using `[h2, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]`.

Simplify using `[e.symm.injective.eq_iff, eq_comm]`. Establish `hPQ : Pm * Qm = 1` using `mul_eq_one_comm.mp hQP`. Use `⟨(⟨Pm, Qm, hPQ, hQP⟩ : GL n K), fun y => ?_⟩` and prove the remaining obligations. Use `show y ∈ M ↔ ∀ i, (Qm *ᵥ y) i ∈ O`. Rewrite using `[hQ]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy i`. Establish `h2 : y = ∑ j, (bM.repr ⟨y, hy⟩ j : K) • bK j`. Establish `h1` using `bM.sum_repr ⟨y, hy⟩`. Establish `h3` using `congrArg (fun m : M => (m : n → K)) h1`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h3`. Use `conv_lhs => rw [← h3]`. Conclude with `Finset.sum_congr rfl (fun j _ => by rw [hbK]; rfl)`. Establish `h4 : bK.repr y (e.symm i) = (bM.repr ⟨y, hy⟩ (e.symm i) : K)` using `by conv_lhs => rw [h2]`. Simplify using `[Module.Basis.repr_self, Finsupp.single_apply]`.

Use `show bK.repr y (e.symm i) ∈ O`. Rewrite using `[h4]`. Conclude with `(bM.repr ⟨y, hy⟩ (e.symm i)).2`. Introduce `hc`. Establish `hc' : ∀ j, bK.repr y j ∈ O`.

Introduce `j`. Use `hc (e j)` as an intermediate fact. Simplify using `using this`. Rewrite using `[← bK.sum_repr y]`. Use `Submodule.sum_mem _ (fun j _ => ?_)` and prove the remaining obligations.

Establish `h5 : bK.repr y j • bK j = (⟨bK.repr y j, hc' j⟩ : O) • (bM j : n → K)`. Rewrite using `[hsmul, hbK]`. Rewrite using `[h5]`. Conclude with `M.smul_mem _ (bM j).2`.
-/
theorem exists_gl (M : Submodule O (n → K)) (hfg : M.FG)
    (hsp : Submodule.span K (M : Set (n → K)) = ⊤) :
    ∃ P : GL n K, ∀ y, y ∈ M ↔ ∀ i, (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) i ∈ O := by
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O M
  let bM : Module.Basis ι O M := Module.Free.chooseBasis O M
  let v : ι → (n → K) := fun i => (bM i : n → K)
  have hliO : LinearIndependent O v := bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing O K).mp hliO
  have hsmul : ∀ (r : O) (w : n → K), r • w = (r : K) • w := fun r w => rfl
  have hMsp : (M : Set (n → K)) ⊆ Submodule.span K (Set.range v) := by
    intro y hy
    have h1 := bM.sum_repr ⟨y, hy⟩
    have h2 : y = ∑ i, (bM.repr ⟨y, hy⟩ i : K) • v i := by
      have h3 := congrArg (fun m : M => (m : n → K)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      conv_lhs => rw [← h3]
      rfl
    rw [h2]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hsp]
    exact Submodule.span_le.mpr hMsp
  let bK : Module.Basis ι K (n → K) := Module.Basis.mk hli hsp
  have hbK : ∀ i, bK i = v i := fun i => Module.Basis.mk_apply hli hsp i
  have hcard : Fintype.card ι = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fintype_fun_eq_card]
  let e : ι ≃ n := Fintype.equivOfCardEq hcard
  let Pm : Matrix n n K := fun i j => bK (e.symm j) i
  let Qm : Matrix n n K := fun i j => bK.repr (Pi.single j 1) (e.symm i)
  have hQ : ∀ y : n → K, Qm *ᵥ y = fun i => bK.repr y (e.symm i) := by
    intro y
    funext i
    have hy : y = ∑ j, y j • (Pi.single j (1 : K) : n → K) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hy]
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Qm]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hQP : Qm * Pm = 1 := by
    ext i k
    have h1 := congrFun (hQ (fun j => Pm j k)) i
    rw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct] at h1
    rw [h1]
    have h2 : (fun j => Pm j k) = bK (e.symm k) := rfl
    rw [h2, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    simp [e.symm.injective.eq_iff, eq_comm]
  have hPQ : Pm * Qm = 1 := mul_eq_one_comm.mp hQP
  refine ⟨(⟨Pm, Qm, hPQ, hQP⟩ : GL n K), fun y => ?_⟩
  show y ∈ M ↔ ∀ i, (Qm *ᵥ y) i ∈ O
  rw [hQ]
  constructor
  · intro hy i
    have h2 : y = ∑ j, (bM.repr ⟨y, hy⟩ j : K) • bK j := by
      have h1 := bM.sum_repr ⟨y, hy⟩
      have h3 := congrArg (fun m : M => (m : n → K)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      conv_lhs => rw [← h3]
      exact Finset.sum_congr rfl (fun j _ => by rw [hbK]; rfl)
    have h4 : bK.repr y (e.symm i) = (bM.repr ⟨y, hy⟩ (e.symm i) : K) := by
      conv_lhs => rw [h2]
      simp [Module.Basis.repr_self, Finsupp.single_apply]
    show bK.repr y (e.symm i) ∈ O
    rw [h4]
    exact (bM.repr ⟨y, hy⟩ (e.symm i)).2
  · intro hc
    have hc' : ∀ j, bK.repr y j ∈ O := by
      intro j
      have := hc (e j)
      simpa using this
    rw [← bK.sum_repr y]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have h5 : bK.repr y j • bK j = (⟨bK.repr y j, hc' j⟩ : O) • (bM j : n → K) := by
      rw [hsmul, hbK]
    rw [h5]
    exact M.smul_mem _ (bM j).2

end MassDataIdxLatFree

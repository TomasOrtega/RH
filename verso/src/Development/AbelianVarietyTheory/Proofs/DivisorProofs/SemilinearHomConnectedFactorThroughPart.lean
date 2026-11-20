import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEt
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hEt hConn hsplit x n a`. Establish `h1 : ∀ c : C.A n, i₁.app n (x.app n c) = algebraMap k' (G'₁.A n) (σ (counit (R` using `k) c)) := by`. Introduce `c`. Use `haveI := hEt n`. Establish `hmem : c - algebraMap k (C.A n) (counit (R` using `k) c) ∈ augIdeal k (C.A n) := by`.

Rewrite using `[mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k), ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]`. Establish `h` using `(((hConn n _ hmem).map (x.app n).toRingHom).map (i₁.app n)).eq_zero`. Express the relevant statement in the definitionally equal form `i₁.app n (x.app n (c - _)) = 0 at h`. Rewrite `h` using `[map_sub, SemiBialgHom.map_algebraMap, map_sub, AlgHomClass.commutes, sub_eq_zero]`. Conclude with `h`.

Establish `hP₁ : ∀ c : C.A n, (q₁ ≫ i₁).app n (x.app n c) = algebraMap k' (G'.A n) (σ (counit (R` using `k) c)) := by`. Introduce `c`. Rewrite using `[comp_app, BialgHom.comp_apply, h1, AlgHomClass.commutes]`. Establish `hid : ∀ b : G'.A n, ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n).ofConv b = b`. Introduce `b`.

Establish `h` using `congrArg (fun f : G' ⟶ G' => f.app n b) hsplit`. Conclude with `h`. Establish `key : ∀ c : C.A n ⊗[k] C.A n, Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n) ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two c) = (q₀ ≫ i₀).app n (x.app n (TensorProduct.rid k (C.A n) (LinearMap.lTensor (C.A n) (counit (R` using `k)) c))) := by`. Introduce `c`. Proceed by induction on `c with`.

Consider the case `zero => simp`. Consider the case `add c d hc hd => simp only [map_add, hc, hd]`. Consider the case `tmul b c`. Rewrite using `[TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]`. Express the relevant statement in the definitionally equal form `_ * (q₁ ≫ i₁).app n (x.app n c) = _`.

Rewrite using `[hP₁, (x.app n).smul_map, map_smul, Algebra.smul_def, mul_comm]`. Both sides reduce to the same expression. Establish `e : (toPts ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n)).ofConv (x.app n a) = x.app n a` using `hid (x.app n a)`. Rewrite `e` using `[map_mul, AlgHom.convMul_apply, toPts_ofConv, toPts_ofConv, ← (x.app n).two_comul]`. Establish `e2` using `key (comul (R := k) a)`.

Rewrite `e2` using `[Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]`. Conclude with `e2.symm.trans e`.
-/
theorem PDivGroup.semiHom_app_eq_conn_part :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hEt hConn hsplit x n a
  have h1 : ∀ c : C.A n,
      i₁.app n (x.app n c) = algebraMap k' (G'₁.A n) (σ (counit (R := k) c)) := by
    intro c
    haveI := hEt n
    have hmem : c - algebraMap k (C.A n) (counit (R := k) c) ∈ augIdeal k (C.A n) := by
      rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
        ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
    have h := (((hConn n _ hmem).map (x.app n).toRingHom).map (i₁.app n)).eq_zero
    change i₁.app n (x.app n (c - _)) = 0 at h
    rw [map_sub, SemiBialgHom.map_algebraMap, map_sub, AlgHomClass.commutes, sub_eq_zero] at h
    exact h
  have hP₁ : ∀ c : C.A n, (q₁ ≫ i₁).app n (x.app n c) =
      algebraMap k' (G'.A n) (σ (counit (R := k) c)) := by
    intro c
    rw [comp_app, BialgHom.comp_apply, h1, AlgHomClass.commutes]
  have hid : ∀ b : G'.A n, ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n).ofConv b = b := by
    intro b
    have h := congrArg (fun f : G' ⟶ G' => f.app n b) hsplit
    exact h
  have key : ∀ c : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two c) =
      (q₀ ≫ i₀).app n (x.app n (TensorProduct.rid k (C.A n)
        (LinearMap.lTensor (C.A n) (counit (R := k)) c))) := by
    intro c
    induction c with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | tmul b c =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
      change _ * (q₁ ≫ i₁).app n (x.app n c) = _
      rw [hP₁, (x.app n).smul_map, map_smul, Algebra.smul_def, mul_comm]
      rfl
  have e : (toPts ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n)).ofConv (x.app n a) = x.app n a :=
    hid (x.app n a)
  rw [map_mul, AlgHom.convMul_apply, toPts_ofConv, toPts_ofConv, ← (x.app n).two_comul] at e
  have e2 := key (comul (R := k) a)
  rw [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul] at e2
  exact e2.symm.trans e

end GlobalTheory

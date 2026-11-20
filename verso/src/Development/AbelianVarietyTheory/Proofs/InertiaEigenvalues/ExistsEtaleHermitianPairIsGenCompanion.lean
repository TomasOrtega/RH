import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyCompactModuleTopology

open Polynomial Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR

/- English proof (translation)
Use `set P : k[X] := X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) with hP`. Establish `hlt : (∑ i, C (p i) * X ^ (i : ℕ) : k[X]).degree < r` using `degree_sum_fin_lt p`. Establish `hm : P.Monic` using `monic_X_pow_add hlt`. Establish `hd : P.natDegree = r`. Establish `: P.degree = r`.

Rewrite using `[hP, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]`. Conclude with `natDegree_eq_of_degree_eq_some this`. Set `pb` to `AdjoinRoot.powerBasis' hm`. Establish `hdim : pb.dim = r` using `hd`. Set `b : Module.Basis (Fin r) k (AdjoinRoot P)` to `pb.basis.reindex (finCongr hdim)`.

Establish `hb : ∀ i : Fin r, b i = AdjoinRoot.root P ^ (i : ℕ)`. Introduce `i`. Simplify using `only [b, Module.Basis.reindex_apply, pb.basis_eq_pow]`. Both sides reduce to the same expression. Establish `hroot : AdjoinRoot.root P ^ r = ∑ i, (- p i) • b i`.

Establish `h0` using `AdjoinRoot.aeval_eq (f := P) P`. Rewrite `h0` using `[AdjoinRoot.mk_self]`. Establish `h2 : aeval (AdjoinRoot.root P) (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : k[X]) = 0` using `h0`. Simplify using `only [map_add, map_pow, map_sum, map_mul, aeval_X, aeval_C] at h2`. Rewrite using `[eq_neg_of_add_eq_zero_left h2, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hb, neg_smul, Algebra.smul_def]`. Establish `hmat : companion p = Algebra.leftMulMatrix b (AdjoinRoot.root P)`. Use extensionality with `i j`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, hb, ← pow_succ']`.

Simplify using `only [companion, Matrix.of_apply]`. Distinguish the cases in `hj : (j : ℕ) + 1 = r`. Rewrite using `[if_pos hj, hj, hroot, ← b.equivFun_symm_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[if_neg hj]`. Establish `hlt' : (j : ℕ) + 1 < r` using `lt_of_le_of_ne j.2 hj`.

Establish `: AdjoinRoot.root P ^ ((j : ℕ) + 1) = b ⟨(j : ℕ) + 1, hlt'⟩` using `by rw [hb]`. Rewrite using `[this, b.repr_self, Finsupp.single_apply]`. Distinguish the cases in `hi : (i : ℕ) = (j : ℕ) + 1`. Rewrite using `[if_pos hi, if_pos (Fin.ext hi.symm)]`. Rewrite using `[if_neg hi, if_neg (fun h => hi (congrArg Fin.val h).symm)]`.

Establish `hP0 : P ≠ 0` using `hm.ne_zero`. Use `haveI : Module.Finite k (AdjoinRoot P) := pb.finite`. Rewrite using `[hmat, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, ← LinearMap.charpoly_toMatrix _ pb.basis, ← Algebra.leftMulMatrix_apply]`. Establish `hg : pb.gen = AdjoinRoot.root P` using `rfl`. Rewrite using `[← hg, charpoly_leftMulMatrix, hg, AdjoinRoot.minpoly_root hP0, hm.leadingCoeff, inv_one, C_1, mul_one]`.
-/
theorem charpoly_companion {k : Type} [Field k] {r : ℕ} (p : Fin r → k) :
    (companion p).charpoly = X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) := by
  set P : k[X] := X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) with hP
  have hlt : (∑ i, C (p i) * X ^ (i : ℕ) : k[X]).degree < r := degree_sum_fin_lt p
  have hm : P.Monic := monic_X_pow_add hlt
  have hd : P.natDegree = r := by
    have : P.degree = r := by
      rw [hP, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  let pb := AdjoinRoot.powerBasis' hm
  have hdim : pb.dim = r := hd
  let b : Module.Basis (Fin r) k (AdjoinRoot P) := pb.basis.reindex (finCongr hdim)
  have hb : ∀ i : Fin r, b i = AdjoinRoot.root P ^ (i : ℕ) := by
    intro i
    simp only [b, Module.Basis.reindex_apply, pb.basis_eq_pow]
    rfl
  have hroot : AdjoinRoot.root P ^ r = ∑ i, (- p i) • b i := by
    have h0 := AdjoinRoot.aeval_eq (f := P) P
    rw [AdjoinRoot.mk_self] at h0
    have h2 : aeval (AdjoinRoot.root P) (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : k[X]) = 0 := h0
    simp only [map_add, map_pow, map_sum, map_mul, aeval_X, aeval_C] at h2
    rw [eq_neg_of_add_eq_zero_left h2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, neg_smul, Algebra.smul_def]
  have hmat : companion p = Algebra.leftMulMatrix b (AdjoinRoot.root P) := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb, ← pow_succ']
    simp only [companion, Matrix.of_apply]
    by_cases hj : (j : ℕ) + 1 = r
    · rw [if_pos hj, hj, hroot, ← b.equivFun_symm_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    · rw [if_neg hj]
      have hlt' : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
      have : AdjoinRoot.root P ^ ((j : ℕ) + 1) = b ⟨(j : ℕ) + 1, hlt'⟩ := by rw [hb]
      rw [this, b.repr_self, Finsupp.single_apply]
      by_cases hi : (i : ℕ) = (j : ℕ) + 1
      · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
      · rw [if_neg hi, if_neg (fun h => hi (congrArg Fin.val h).symm)]
  have hP0 : P ≠ 0 := hm.ne_zero
  haveI : Module.Finite k (AdjoinRoot P) := pb.finite
  rw [hmat, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, ← LinearMap.charpoly_toMatrix _ pb.basis,
    ← Algebra.leftMulMatrix_apply]
  have hg : pb.gen = AdjoinRoot.root P := rfl
  rw [← hg, charpoly_leftMulMatrix, hg, AdjoinRoot.minpoly_root hP0, hm.leadingCoeff, inv_one, C_1, mul_one]

/- English proof (translation)
Introduce `F E _ _ _ _ _ r p hs`. Rewrite `hs` using `[charpoly_companion]`. Conclude with `EtExist.exists_isGen F E r p hs`.
-/
theorem exists_et_isGen_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F),
    (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  intro F E _ _ _ _ _ r p hs
  rw [charpoly_companion] at hs
  exact EtExist.exists_isGen F E r p hs

end GlobalTheory.JR

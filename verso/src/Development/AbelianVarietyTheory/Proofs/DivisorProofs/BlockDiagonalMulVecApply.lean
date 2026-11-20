import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory.OrthSumGram

open Matrix

/- English proof (translation)
Simplify using `only [mulVec, dotProduct, Fintype.sum_sigma, blockDiagonal'_apply]`. Rewrite using `[Finset.sum_eq_single i]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Rewrite using `[dif_neg (Ne.symm hk), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem blockDiagonal'_mulVec_apply' {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (M : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (u : (Σ i, Fin (n i)) → ℂ) (i : ι) (j : Fin (n i)) :
    (blockDiagonal' M *ᵥ u) ⟨i, j⟩ = (M i *ᵥ fun l => u ⟨i, l⟩) j := by
  simp only [mulVec, dotProduct, Fintype.sum_sigma, blockDiagonal'_apply]
  rw [Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp
  · intro k _ hk
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [dif_neg (Ne.symm hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Introduce `K V _ _ _ _ ι _ N W hN hind htop hG hpy`. Establish `hint : DirectSum.IsInternal W` using `(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).2 ⟨hind, htop⟩`. Set `g` to `fun i => (hG i).some`. Set `n : ι → ℕ` to `fun i => (g i).1`. Set `b : ∀ i, Module.Basis (Fin (n i)) K (W i)` to `fun i => (g i).2.1.1`.

Set `X : ∀ i, InfinitePlace K → Matrix (Fin (n i)) (Fin (n i)) ℂ` to `fun i => (g i).2.1.2`. Establish `hX : ∀ i, IsGram (b i) (X i) (fun σ (x : W i) => N σ x)` using `fun i => (g i).2.2`. Set `B` to `hint.collectedBasis b`. Establish `hB : ∀ a, B a = (b a.1 a.2 : V)` using `fun a => by`. Simplify using `only [B, DirectSum.IsInternal.collectedBasis_coe]`.

Set `Xv : InfinitePlace K → Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℂ` to `fun v => blockDiagonal' fun i => X i v`. Establish `hmul : ∀ v, Xv v * blockDiagonal' (fun i => (X i v)⁻¹) = 1` using `fun v => by`. Simplify using `only [Xv, ← blockDiagonal'_mul]`. Rewrite using `[← blockDiagonal'_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `Matrix.mul_nonsing_inv _ ((hX i v).1)`. Use `IsGram.hasGram (b := B) (X := Xv) fun v => ⟨Matrix.isUnit_det_of_right_inverse (hmul v), fun x => ?_⟩` and prove the remaining obligations. Establish `hinv : (Xv v)⁻¹ = blockDiagonal' (fun i => (X i v)⁻¹)` using `Matrix.inv_eq_right_inv (hmul v)`. Set `c` to `B.repr x`.

Set `f : ∀ i, W i` to `fun i => ∑ j, c ⟨i, j⟩ • b i j`. Establish `hx : x = ∑ i, (f i : V)` using `by conv_lhs => rw [← B.sum_repr x]`. Rewrite using `[Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [f, Submodule.coe_sum, Submodule.coe_smul, hB]`.

Both sides reduce to the same expression. Establish `hrep : ∀ i j, (b i).repr (f i) j = c ⟨i, j⟩` using `fun i j => by`. Simplify using `only [f, Module.Basis.repr_sum_self]`. Establish `hcoord : ∀ i j, Formalism.HermitianLatticesTheory.fcoord B Xv v x ⟨i, j⟩ = Formalism.HermitianLatticesTheory.fcoord (b i) (X i) v (f i) j` using `fun i j => by`. Simplify using `only [Formalism.HermitianLatticesTheory.fcoord, hinv, blockDiagonal'_mulVec_apply']`.

Use `congr 1`. Use function extensionality and compare the values at `l`. Simplify using `only [Formalism.HermitianLatticesTheory.vecAt, hrep, c]`. Establish `hsq : Formalism.HermitianLatticesTheory.normAt B Xv v x ^ 2 = N v.embedding x ^ 2`. Rewrite using `[hx, hpy, ← hx]`.

Simplify using `only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `e : Formalism.HermitianLatticesTheory.normAt (b i) (X i) v (f i) = N v.embedding (f i)` using `(hX i v).2 (f i)`. Rewrite using `[← e]`.

Simplify using `only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hcoord]`. Establish `h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt B Xv v x` using `Real.sqrt_nonneg _`.

Conclude with `(sq_eq_sq₀ h0 (hN _ _)).1 hsq`.
-/
theorem orth_sum_hasGram : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (ι : Type) [Fintype ι] (N : (K →+* ℂ) → V → ℝ) (W : ι → Submodule K V), (∀ σ x, 0 ≤ N σ x) → iSupIndep W → ⨆ i, W i = ⊤ → (∀ i, HasGram (fun σ (x : W i) => N σ x)) → (∀ σ, ∀ f : ∀ i, W i, N σ (∑ i, (f i : V)) ^ 2 = ∑ i, N σ (f i) ^ 2) → HasGram N := by
  classical
  intro K V _ _ _ _ ι _ N W hN hind htop hG hpy
  have hint : DirectSum.IsInternal W :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).2 ⟨hind, htop⟩
  let g := fun i => (hG i).some
  let n : ι → ℕ := fun i => (g i).1
  let b : ∀ i, Module.Basis (Fin (n i)) K (W i) := fun i => (g i).2.1.1
  let X : ∀ i, InfinitePlace K → Matrix (Fin (n i)) (Fin (n i)) ℂ := fun i => (g i).2.1.2
  have hX : ∀ i, IsGram (b i) (X i) (fun σ (x : W i) => N σ x) := fun i => (g i).2.2
  let B := hint.collectedBasis b
  have hB : ∀ a, B a = (b a.1 a.2 : V) := fun a => by
    simp only [B, DirectSum.IsInternal.collectedBasis_coe]
  let Xv : InfinitePlace K → Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℂ := fun v => blockDiagonal' fun i => X i v
  have hmul : ∀ v, Xv v * blockDiagonal' (fun i => (X i v)⁻¹) = 1 := fun v => by
    simp only [Xv, ← blockDiagonal'_mul]
    rw [← blockDiagonal'_one]
    congr 1
    funext i
    exact Matrix.mul_nonsing_inv _ ((hX i v).1)
  refine IsGram.hasGram (b := B) (X := Xv) fun v => ⟨Matrix.isUnit_det_of_right_inverse (hmul v), fun x => ?_⟩
  have hinv : (Xv v)⁻¹ = blockDiagonal' (fun i => (X i v)⁻¹) := Matrix.inv_eq_right_inv (hmul v)
  let c := B.repr x
  let f : ∀ i, W i := fun i => ∑ j, c ⟨i, j⟩ • b i j
  have hx : x = ∑ i, (f i : V) := by
    conv_lhs => rw [← B.sum_repr x]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [f, Submodule.coe_sum, Submodule.coe_smul, hB]
    rfl
  have hrep : ∀ i j, (b i).repr (f i) j = c ⟨i, j⟩ := fun i j => by
    simp only [f, Module.Basis.repr_sum_self]
  have hcoord : ∀ i j, Formalism.HermitianLatticesTheory.fcoord B Xv v x ⟨i, j⟩ = Formalism.HermitianLatticesTheory.fcoord (b i) (X i) v (f i) j := fun i j => by
    simp only [Formalism.HermitianLatticesTheory.fcoord, hinv, blockDiagonal'_mulVec_apply']
    congr 1
    funext l
    simp only [Formalism.HermitianLatticesTheory.vecAt, hrep, c]
  have hsq : Formalism.HermitianLatticesTheory.normAt B Xv v x ^ 2 = N v.embedding x ^ 2 := by
    rw [hx, hpy, ← hx]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : Formalism.HermitianLatticesTheory.normAt (b i) (X i) v (f i) = N v.embedding (f i) := (hX i v).2 (f i)
    rw [← e]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoord]
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt B Xv v x := Real.sqrt_nonneg _
  exact (sq_eq_sq₀ h0 (hN _ _)).1 hsq

end GlobalTheory.OrthSumGram

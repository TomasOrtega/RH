import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvN.LagrangianNormalForm

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Take `⟨L, L', d, h⟩` from `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal X`. Use `set P := (L.map Matrix.TransvectionStruct.toMatrix).prod with hP`. Use `set Q := (L'.map Matrix.TransvectionStruct.toMatrix).prod with hQ`. Establish `dP : IsUnit P.det` using `by rw [hP, Matrix.TransvectionStruct.det_toMatrix_prod]; exact isUnit_one`. Establish `dQ : IsUnit Q.det` using `by rw [hQ, Matrix.TransvectionStruct.det_toMatrix_prod]; exact isUnit_one`.

Establish `hX : X = P⁻¹ * Matrix.diagonal d * Q⁻¹`. Rewrite using `[← h]`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ dQ, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ dP]`. Establish `hPX : P * X = Matrix.diagonal d * Q⁻¹`. Rewrite using `[← h]`.

Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ dQ, Matrix.mul_one]`. Use `⟨Q * Matrix.diagonal (fun i => (d i)⁻¹) * P, Pᵀ * P, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : Matrix.diagonal d * (Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d) = Matrix.diagonal d`. Rewrite using `[Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : d i = 0`. Simplify using `[hi]`. Simplify using `[hi]`. Use `conv_lhs => rw [hX]`.

Use `conv_rhs => rw [hX, ← e]`. Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ dQ, Matrix.mul_nonsing_inv_cancel_left _ _ dP]`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_transpose]`. Introduce `v hv`. Establish `e : Xᵀ * (Pᵀ * P) * X = (Q⁻¹)ᵀ * (Matrix.diagonal d * (Matrix.diagonal d * Q⁻¹))`.

Establish `: Xᵀ * (Pᵀ * P) * X = (P * X)ᵀ * (P * X)`. Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`. Rewrite using `[this, hPX, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]`. Rewrite `hv` using `[e]`. Establish `h2` using `congrArg (fun w => Qᵀ *ᵥ w) hv`.

Simplify using `only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2`. Rewrite `h2` using `[← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ dQ, Matrix.transpose_one, Matrix.one_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `h3 : Matrix.diagonal d *ᵥ (Q⁻¹ *ᵥ v) = 0`. Use function extensionality and compare the values at `i`. Use `congrFun h2 i` as an intermediate fact.

Simplify using `only [Matrix.mulVec_diagonal, Pi.zero_apply] at this ⊢`. Break down `mul_eq_zero.mp this with h0 | h0` into its components or cases. Simplify using `[h0]`. Conclude with `h0`. Rewrite using `[hX, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]`.
-/
theorem exists_ginv_form (X : Matrix κ κ F) :
    ∃ G C : Matrix κ κ F, X * G * X = X ∧ Cᵀ = C ∧ ∀ v, (Xᵀ * C * X) *ᵥ v = 0 → X *ᵥ v = 0 := by
  obtain ⟨L, L', d, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal X
  set P := (L.map Matrix.TransvectionStruct.toMatrix).prod with hP
  set Q := (L'.map Matrix.TransvectionStruct.toMatrix).prod with hQ
  have dP : IsUnit P.det := by rw [hP, Matrix.TransvectionStruct.det_toMatrix_prod]; exact isUnit_one
  have dQ : IsUnit Q.det := by rw [hQ, Matrix.TransvectionStruct.det_toMatrix_prod]; exact isUnit_one
  have hX : X = P⁻¹ * Matrix.diagonal d * Q⁻¹ := by
    rw [← h]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ dQ, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ dP]
  have hPX : P * X = Matrix.diagonal d * Q⁻¹ := by
    rw [← h]; simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ dQ, Matrix.mul_one]
  refine ⟨Q * Matrix.diagonal (fun i => (d i)⁻¹) * P, Pᵀ * P, ?_, ?_, ?_⟩
  · have e : Matrix.diagonal d * (Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d) = Matrix.diagonal d := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      by_cases hi : d i = 0
      · simp [hi]
      · simp [hi]
    conv_lhs => rw [hX]
    conv_rhs => rw [hX, ← e]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ dQ,
      Matrix.mul_nonsing_inv_cancel_left _ _ dP]
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  · intro v hv
    have e : Xᵀ * (Pᵀ * P) * X = (Q⁻¹)ᵀ * (Matrix.diagonal d * (Matrix.diagonal d * Q⁻¹)) := by
      have : Xᵀ * (Pᵀ * P) * X = (P * X)ᵀ * (P * X) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [this, hPX, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [e] at hv
    have h2 := congrArg (fun w => Qᵀ *ᵥ w) hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ dQ, Matrix.transpose_one,
      Matrix.one_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h2
    have h3 : Matrix.diagonal d *ᵥ (Q⁻¹ *ᵥ v) = 0 := by
      funext i
      have := congrFun h2 i
      simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at this ⊢
      rcases mul_eq_zero.mp this with h0 | h0
      · simp [h0]
      · exact h0
    rw [hX, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]

/- English proof (translation)
Take `⟨G, C, hG, hC, hv⟩` from `exists_ginv_form X`. Use `⟨C - Gᵀ * (Xᵀ * Y) * G, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.transpose_sub, hC]`. Use `congr 1`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc Yᵀ, ← hs, Matrix.mul_assoc]`. Establish `e : Xᵀ * (Y + (C - Gᵀ * (Xᵀ * Y) * G) * X) = Xᵀ * C * X`. Establish `e1 : Xᵀ * (Gᵀ * (Xᵀ * Y) * G * X) = Xᵀ * Y`. Establish `: Xᵀ * (Gᵀ * (Xᵀ * Y) * G * X) = (X * G * X)ᵀ * Y * G * X`. Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`.

Rewrite using `[this, hG, hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc X, hG]`. Rewrite using `[Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, e1, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`.

Take `⟨v, hv0, hv1⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Establish `hX : X *ᵥ v = 0`. Apply `hv` to reduce the goal to its premises. Rewrite using `[← e, ← Matrix.mulVec_mulVec, hv1, Matrix.mulVec_zero]`. Apply `hv0` to reduce the goal to its premises.

Apply `hi v hX` to reduce the goal to its premises. Rewrite `hv1` using `[Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_zero, add_zero]`. Then use the resulting hypothesis.
-/
theorem exists_symm_isUnit (X Y : Matrix κ κ F) (hs : Xᵀ * Y = Yᵀ * X)
    (hi : ∀ v, X *ᵥ v = 0 → Y *ᵥ v = 0 → v = 0) :
    ∃ C : Matrix κ κ F, Cᵀ = C ∧ IsUnit (Y + C * X).det := by
  obtain ⟨G, C, hG, hC, hv⟩ := exists_ginv_form X
  refine ⟨C - Gᵀ * (Xᵀ * Y) * G, ?_, ?_⟩
  · rw [Matrix.transpose_sub, hC]
    congr 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Yᵀ, ← hs, Matrix.mul_assoc]
  · have e : Xᵀ * (Y + (C - Gᵀ * (Xᵀ * Y) * G) * X) = Xᵀ * C * X := by
      have e1 : Xᵀ * (Gᵀ * (Xᵀ * Y) * G * X) = Xᵀ * Y := by
        have : Xᵀ * (Gᵀ * (Xᵀ * Y) * G * X) = (X * G * X)ᵀ * Y * G * X := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [this, hG, hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc X, hG]
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, e1, Matrix.mul_assoc]
      abel
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv1⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hX : X *ᵥ v = 0 := by
      apply hv
      rw [← e, ← Matrix.mulVec_mulVec, hv1, Matrix.mulVec_zero]
    apply hv0
    apply hi v hX
    rwa [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_zero, add_zero] at hv1

/- English proof (translation)
Establish `hJ : Matrix.fromBlocks (0 : Matrix κ κ F) (1 : Matrix κ κ F) (-1 : Matrix κ κ F) (0 : Matrix κ κ F) ∈ Submonoid.closure (gens F κ)` using `Submonoid.subset_closure (Or.inr rfl)`. Establish `hn : Matrix.fromBlocks (1 : Matrix κ κ F) (0 : Matrix κ κ F) (-S) (1 : Matrix κ κ F) ∈ Submonoid.closure (gens F κ)` using `Submonoid.subset_closure (Or.inl (Or.inr ⟨S, hS, rfl⟩))`. Use `mul_mem (mul_mem (mul_mem (mul_mem hJ hn) hJ) hJ) hJ` as an intermediate fact. Simplify `this` using `[Matrix.fromBlocks_multiply]`.
-/
theorem upper_mem (S : Matrix κ κ F) (hS : Sᵀ = S) :
    Matrix.fromBlocks 1 S 0 1 ∈ Submonoid.closure (gens F κ) := by
  have hJ : Matrix.fromBlocks (0 : Matrix κ κ F) (1 : Matrix κ κ F) (-1 : Matrix κ κ F) (0 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inr rfl)
  have hn : Matrix.fromBlocks (1 : Matrix κ κ F) (0 : Matrix κ κ F) (-S) (1 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inl (Or.inr ⟨S, hS, rfl⟩))
  have := mul_mem (mul_mem (mul_mem (mul_mem hJ hn) hJ) hJ) hJ
  simpa [Matrix.fromBlocks_multiply] using this

/- English proof (translation)
Set `b : Module.Basis κ F L` to `(Module.finBasisOfFinrankEq F L hd).reindex (Fintype.equivFin κ).symm`. Set `X : Matrix κ κ F` to `Matrix.of fun i j => (b j).1.1 i`. Set `Y : Matrix κ κ F` to `Matrix.of fun i j => (b j).1.2 i`. Establish `key : ∀ v : κ → F, (X *ᵥ v, Y *ᵥ v) = ((∑ j, v j • b j : L) : (κ → F) × (κ → F))`. Introduce `v`.

Use extensionality with `i`. Simplify using `[X, Matrix.mulVec, dotProduct, Prod.fst_sum, mul_comm]`. Simplify using `[Y, Matrix.mulVec, dotProduct, Prod.snd_sum, mul_comm]`. Establish `hs : Xᵀ * Y = Yᵀ * X`. Use extensionality with `i j`.

Use `hL _ (b i).2 _ (b j).2` as an intermediate fact. Simplify using `only [dotProduct] at this`. Simplify using `only [Matrix.mul_apply, X, Y, Matrix.transpose_apply, Matrix.of_apply]`. Rewrite using `[this]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`.

Establish `hi : ∀ v, X *ᵥ v = 0 → Y *ᵥ v = 0 → v = 0`. Introduce `v h1 h2`. Establish `h3` using `key v`. Rewrite `h3` using `[h1, h2]`. Establish `h4 : ∑ j, v j • b j = 0` using `Subtype.ext h3.symm`.

Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.mp b.linearIndependent v h4 j`. Take `⟨C, hC, hM⟩` from `exists_symm_isUnit X Y hs hi`. Use `set M := Y + C * X with hMdef`. Establish `hXM : Xᵀ * M = Mᵀ * X`.

Rewrite using `[hMdef, Matrix.transpose_add, Matrix.transpose_mul, hC, Matrix.mul_add, Matrix.add_mul, hs, Matrix.mul_assoc]`. Establish `hS : (X * M⁻¹)ᵀ = X * M⁻¹`. Establish `h1 : (M⁻¹)ᵀ * Mᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, Matrix.transpose_one]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]`. Use `_ = X * M⁻¹ := by rw [hXM, ← Matrix.mul_assoc, h1, Matrix.one_mul]`. Establish `hn : Matrix.fromBlocks (1 : Matrix κ κ F) (0 : Matrix κ κ F) (-C) (1 : Matrix κ κ F) ∈ Submonoid.closure (gens F κ)` using `Submonoid.subset_closure (Or.inl (Or.inr ⟨C, hC, rfl⟩))`. Use `⟨_, mul_mem hn (upper_mem _ hS), fun y => ?_⟩` and prove the remaining obligations. Establish `hy : Y *ᵥ (M⁻¹ *ᵥ y) = -(C *ᵥ (X *ᵥ (M⁻¹ *ᵥ y))) + y`.

Establish `: M *ᵥ (M⁻¹ *ᵥ y) = y`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]`. Generalize the expression as in `M⁻¹ *ᵥ y = v at this ⊢`. Rewrite using `[← this, hMdef, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]`. Normalize the expressions using the abelian group laws.

Establish `hmem : (X *ᵥ (M⁻¹ *ᵥ y), Y *ᵥ (M⁻¹ *ᵥ y)) ∈ L` using `by rw [key]; exact Subtype.property _`. Rewrite `hmem` using `[hy]`. Simplify `hmem` using `[← Matrix.mulVec_mulVec, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec]`.
-/
theorem exists_mem_closure (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (L : Submodule F ((κ → F) × (κ → F)))
    (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (hd : Module.finrank F L = Fintype.card κ) :
    ∃ g ∈ Submonoid.closure (gens F κ), ∀ y : κ → F,
      ((g *ᵥ Sum.elim 0 y) ∘ Sum.inl, (g *ᵥ Sum.elim 0 y) ∘ Sum.inr) ∈ L := by
  let b : Module.Basis κ F L := (Module.finBasisOfFinrankEq F L hd).reindex (Fintype.equivFin κ).symm
  let X : Matrix κ κ F := Matrix.of fun i j => (b j).1.1 i
  let Y : Matrix κ κ F := Matrix.of fun i j => (b j).1.2 i
  have key : ∀ v : κ → F, (X *ᵥ v, Y *ᵥ v) = ((∑ j, v j • b j : L) : (κ → F) × (κ → F)) := by
    intro v
    ext i
    · simp [X, Matrix.mulVec, dotProduct, Prod.fst_sum, mul_comm]
    · simp [Y, Matrix.mulVec, dotProduct, Prod.snd_sum, mul_comm]
  have hs : Xᵀ * Y = Yᵀ * X := by
    ext i j
    have := hL _ (b i).2 _ (b j).2
    simp only [dotProduct] at this
    simp only [Matrix.mul_apply, X, Y, Matrix.transpose_apply, Matrix.of_apply]
    rw [this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hi : ∀ v, X *ᵥ v = 0 → Y *ᵥ v = 0 → v = 0 := by
    intro v h1 h2
    have h3 := key v
    rw [h1, h2] at h3
    have h4 : ∑ j, v j • b j = 0 := Subtype.ext h3.symm
    funext j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v h4 j
  obtain ⟨C, hC, hM⟩ := exists_symm_isUnit X Y hs hi
  set M := Y + C * X with hMdef
  have hXM : Xᵀ * M = Mᵀ * X := by
    rw [hMdef, Matrix.transpose_add, Matrix.transpose_mul, hC, Matrix.mul_add, Matrix.add_mul, hs,
      Matrix.mul_assoc]
  have hS : (X * M⁻¹)ᵀ = X * M⁻¹ := by
    have h1 : (M⁻¹)ᵀ * Mᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, Matrix.transpose_one]
    calc (X * M⁻¹)ᵀ = (M⁻¹)ᵀ * (Xᵀ * M) * M⁻¹ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]
      _ = X * M⁻¹ := by rw [hXM, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hn : Matrix.fromBlocks (1 : Matrix κ κ F) (0 : Matrix κ κ F) (-C) (1 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inl (Or.inr ⟨C, hC, rfl⟩))
  refine ⟨_, mul_mem hn (upper_mem _ hS), fun y => ?_⟩
  have hy : Y *ᵥ (M⁻¹ *ᵥ y) = -(C *ᵥ (X *ᵥ (M⁻¹ *ᵥ y))) + y := by
    have : M *ᵥ (M⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
    generalize M⁻¹ *ᵥ y = v at this ⊢
    rw [← this, hMdef, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    abel
  have hmem : (X *ᵥ (M⁻¹ *ᵥ y), Y *ᵥ (M⁻¹ *ᵥ y)) ∈ L := by rw [key]; exact Subtype.property _
  rw [hy] at hmem
  simpa [← Matrix.mulVec_mulVec, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using hmem

end GlobalTheory.AdelicSvN.LagrangianNormalForm

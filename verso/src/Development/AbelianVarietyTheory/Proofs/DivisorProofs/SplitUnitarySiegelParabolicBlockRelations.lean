import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

open MeasureTheory Matrix in

/- English proof (translation)
Introduce `F _ _ E _ _ c δ hE ν _ _ p hp`. Rewrite `hp` using `[_root_.GlobalTheory.KSp.mem_sieg]`. Establish `hc` using `hE.invol`. Establish `hu` using `(_root_.GlobalTheory.SplitUnitary.mem_UG_iff c (p : GL (ν ⊕ ν) E)).mp p.2`. Establish `hM : ((p : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = _root_.GlobalTheory.KSp.mat c p` using `rfl`.

Use `set M := _root_.GlobalTheory.KSp.mat c p`. Rewrite `hu` using `[hM, ← fromBlocks_toBlocks M, hp]`. Unfold `_root_.GlobalTheory.SplitUnitary.stdJ at hu`. Simplify using `only [fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj] at hu`. Simplify using `at hu`.

Take `⟨h1, h2, h3⟩` from `hu`. Establish `h2'` using `mul_eq_one_comm.mp h2`. Establish `h3'` using `mul_eq_one_comm.mp h3`. Establish `hcc : ∀ X : Matrix ν ν E, (X.map c).map c = X` using `fun X => by ext i j; simp [hc]`. Establish `hAB : M.toBlocks₁₁ * (M.toBlocks₁₂.map c)ᵀ = M.toBlocks₁₂ * (M.toBlocks₁₁.map c)ᵀ` using `sub_eq_zero.mp (by rw [← neg_add_eq_sub]; exact h1)`.

Use `⟨h2, hAB, ?_⟩` and prove the remaining obligations. Use `set A := M.toBlocks₁₁`. Use `set B := M.toBlocks₁₂`. Use `set D := M.toBlocks₂₂`. Set `a : GL ν E` to `⟨A, (D.map c)ᵀ, h2, h2'⟩`.

Establish `hb : (((D.map c)ᵀ * B).map c)ᵀ = (D.map c)ᵀ * B`. Rewrite using `[Matrix.map_mul, transpose_mul, transpose_map, hcc, transpose_transpose]`. Establish `hB : B * (A.map c)ᵀ = A * (B.map c)ᵀ` using `hAB.symm`. Combine the equalities or inequalities in the displayed calculation. Use `⟨a, (D.map c)ᵀ * B, hb, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Subgroup.coe_mul, Units.val_mul, _root_.GlobalTheory.SplitUnitary.levi_val, hM]`. Unfold `_root_.GlobalTheory.KSp.unip`. Simplify using `only [fromBlocks_multiply]`.

Establish `ha : ((a⁻¹ : GL ν E) : Matrix ν ν E) = (D.map c)ᵀ` using `rfl`. Rewrite using `[ha, transpose_map, hcc, transpose_transpose, ← Matrix.mul_assoc, h2]`. Use `conv_lhs => rw [← fromBlocks_toBlocks M, hp]`. Simplify using `[A, B, D]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.KSp.sieg_blocks : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E)
    (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (p : _root_.GlobalTheory.WeilM.UG c (_root_.GlobalTheory.SplitUnitary.stdJ ν E)), p ∈ _root_.GlobalTheory.KSp.sieg c ν →
    (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₂₂).map c)ᵀ = 1 ∧
    (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₁₂).map c)ᵀ = (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₂ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁).map c)ᵀ ∧
    ∃ (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b), p = _root_.GlobalTheory.SplitUnitary.levi c hE.invol a * _root_.GlobalTheory.KSp.unip c b hb := by
  intro F _ _ E _ _ c δ hE ν _ _ p hp
  rw [_root_.GlobalTheory.KSp.mem_sieg] at hp
  have hc := hE.invol
  have hu := (_root_.GlobalTheory.SplitUnitary.mem_UG_iff c (p : GL (ν ⊕ ν) E)).mp p.2
  have hM : ((p : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = _root_.GlobalTheory.KSp.mat c p := rfl
  set M := _root_.GlobalTheory.KSp.mat c p
  rw [hM, ← fromBlocks_toBlocks M, hp] at hu
  unfold _root_.GlobalTheory.SplitUnitary.stdJ at hu
  simp only [fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj] at hu
  simp at hu
  obtain ⟨h1, h2, h3⟩ := hu
  have h2' := mul_eq_one_comm.mp h2
  have h3' := mul_eq_one_comm.mp h3
  have hcc : ∀ X : Matrix ν ν E, (X.map c).map c = X := fun X => by ext i j; simp [hc]
  have hAB : M.toBlocks₁₁ * (M.toBlocks₁₂.map c)ᵀ = M.toBlocks₁₂ * (M.toBlocks₁₁.map c)ᵀ :=
    sub_eq_zero.mp (by rw [← neg_add_eq_sub]; exact h1)
  refine ⟨h2, hAB, ?_⟩
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set D := M.toBlocks₂₂
  let a : GL ν E := ⟨A, (D.map c)ᵀ, h2, h2'⟩
  have hb : (((D.map c)ᵀ * B).map c)ᵀ = (D.map c)ᵀ * B := by
    rw [Matrix.map_mul, transpose_mul, transpose_map, hcc, transpose_transpose]
    have hB : B * (A.map c)ᵀ = A * (B.map c)ᵀ := hAB.symm
    calc (B.map c)ᵀ * D = (D.map c)ᵀ * A * (B.map c)ᵀ * D := by rw [h2', Matrix.one_mul]
      _ = (D.map c)ᵀ * (B * (A.map c)ᵀ) * D := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = (D.map c)ᵀ * B * ((A.map c)ᵀ * D) := by simp only [Matrix.mul_assoc]
      _ = (D.map c)ᵀ * B := by rw [h3', Matrix.mul_one]
  refine ⟨a, (D.map c)ᵀ * B, hb, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, _root_.GlobalTheory.SplitUnitary.levi_val, hM]
  unfold _root_.GlobalTheory.KSp.unip
  simp only [fromBlocks_multiply]
  have ha : ((a⁻¹ : GL ν E) : Matrix ν ν E) = (D.map c)ᵀ := rfl
  rw [ha, transpose_map, hcc, transpose_transpose, ← Matrix.mul_assoc, h2]
  conv_lhs => rw [← fromBlocks_toBlocks M, hp]
  simp [A, B, D]
  rfl

end GlobalTheory.KSp

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

/- English proof (translation)
Introduce `N l d _ hNl hdN`. Take `⟨d', hd'N, hd'l⟩` from `Nat.chineseRemainder hNl d 1`. Establish `h1 : Nat.Coprime d' N`. Unfold `Nat.Coprime`. Rewrite using `[Nat.ModEq.gcd_eq hd'N]`.

Conclude with `hdN`. Establish `h2 : Nat.Coprime d' l`. Unfold `Nat.Coprime`. Rewrite using `[Nat.ModEq.gcd_eq hd'l]`. Simplify using the standard rewrite rules.

Establish `h3 : Nat.Coprime d' (N * l)` using `Nat.Coprime.mul_right h1 h2`. Establish `hg : Int.gcd (d' : ℤ) ((N * l : ℕ) : ℤ) = 1` using `by rw [Int.gcd_natCast_natCast]; exact h3`. Establish `hb` using `Int.gcd_eq_gcd_ab (d' : ℤ) ((N * l : ℕ) : ℤ)`. Rewrite `hb` using `[hg]`. Use `set a := Int.gcdA (d' : ℤ) ((N * l : ℕ) : ℤ)`.

Use `set b := Int.gcdB (d' : ℤ) ((N * l : ℕ) : ℤ)`. Set `M : Matrix (Fin 2) (Fin 2) ℤ` to `!![a, -b; ((N * l : ℕ) : ℤ), (d' : ℤ)]`. Establish `hdet : M.det = 1`. Simplify using `only [M, Matrix.det_fin_two_of]`. Move the coercions through the operations in `at hb ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Set `γ : SL(2, ℤ)` to `⟨M, hdet⟩`. Establish `hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = M` using `rfl`. Use `⟨γ, Subgroup.mem_inf.2 ⟨CongruenceSubgroup.Gamma0_mem.2 ?_, CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hγ]`.

Simplify using `[M]`. Rewrite using `[hγ]`. Simplify using `[M]`. Simplify using `only [en, hγ, M]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero]`.

Use `push_cast`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).2 hd'N`.
-/
theorem diam_exists : ∀ (N l d : ℕ), 0 < N → Nat.Coprime N l → Nat.Coprime d N → ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  intro N l d _ hNl hdN

  obtain ⟨d', hd'N, hd'l⟩ := Nat.chineseRemainder hNl d 1
  have h1 : Nat.Coprime d' N := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'N]; exact hdN
  have h2 : Nat.Coprime d' l := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'l]; simp
  have h3 : Nat.Coprime d' (N * l) := Nat.Coprime.mul_right h1 h2
  have hg : Int.gcd (d' : ℤ) ((N * l : ℕ) : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact h3
  have hb := Int.gcd_eq_gcd_ab (d' : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  set a := Int.gcdA (d' : ℤ) ((N * l : ℕ) : ℤ)
  set b := Int.gcdB (d' : ℤ) ((N * l : ℕ) : ℤ)
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a, -b; ((N * l : ℕ) : ℤ), (d' : ℤ)]
  have hdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  let γ : SL(2, ℤ) := ⟨M, hdet⟩
  have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = M := rfl
  refine ⟨γ, Subgroup.mem_inf.2 ⟨CongruenceSubgroup.Gamma0_mem.2 ?_, CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ?_⟩
  · rw [hγ]; simp [M]
  · rw [hγ]; simp [M]
  · simp only [en, hγ, M]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    push_cast
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hd'N

end GlobalTheory

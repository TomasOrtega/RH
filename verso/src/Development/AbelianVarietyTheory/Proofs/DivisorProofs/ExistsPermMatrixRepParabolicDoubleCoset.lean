import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.FinGL.Bruhat

/- English proof (translation)
Introduce `F _ r b b' hb hb' g`. Establish `hle : ∀ (c : Fin r → ℕ), Monotone c → ∀ u ∈ unip F r, u ∈ blockTri (κ` using `F) c := by`. Introduce `c hc u hu`. Rewrite using `[mem_blockTri]`. Introduce `i j hij`.

Conclude with `unip_lower hu (lt_of_not_ge fun h => absurd (hc h) (not_le.2 hij))`. Take `⟨m, u, hu, u', hu', h⟩` from `exists_decomp g`. Establish `hdet : (Matrix.diagonal fun c => (m.2 c : F)).det ≠ 0`. Rewrite using `[Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.2 fun c _ => (m.2 c).ne_zero`.

Set `d : GL (Fin r) F` to `Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet`. Establish `hdv : (d : Matrix (Fin r) (Fin r) F) = Matrix.diagonal fun c => (m.2 c : F)` using `rfl`. Establish `hd : d ∈ blockTri (κ` using `F) b := by`. Rewrite using `[mem_blockTri]`. Introduce `i j hij`.

Rewrite using `[hdv]`. Conclude with `Matrix.diagonal_apply_ne _ (fun e => by rw [e] at hij; exact lt_irrefl _ hij)`. Establish `hm : mono m = (permGL F m.1 : Matrix (Fin r) (Fin r) F) * (d : Matrix (Fin r) (Fin r) F)`. Use extensionality with `a c`. Rewrite using `[hdv, Matrix.mul_diagonal, permGL_apply]`.

Apply the tactic sequence `by_cases e : a = m.1 c <;> simp [mono, e]`. Use `⟨m.1, ⟨u, hle b' hb' u hu⟩, ⟨d * u', Subgroup.mul_mem _ hd (hle b hb u' hu')⟩, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[h, hm]`. Simplify using `only [Units.val_mul, Matrix.mul_assoc]`.
-/
theorem exists_perm_rep_blockTri : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ), Monotone b → Monotone b' → ∀ g : GL (Fin r) F, ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b), g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) := by
  intro F _ r b b' hb hb' g
  have hle : ∀ (c : Fin r → ℕ), Monotone c → ∀ u ∈ unip F r, u ∈ blockTri (κ := F) c := by
    intro c hc u hu
    rw [mem_blockTri]
    intro i j hij
    exact unip_lower hu (lt_of_not_ge fun h => absurd (hc h) (not_le.2 hij))
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  have hdet : (Matrix.diagonal fun c => (m.2 c : F)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun c _ => (m.2 c).ne_zero
  let d : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hdv : (d : Matrix (Fin r) (Fin r) F) = Matrix.diagonal fun c => (m.2 c : F) := rfl
  have hd : d ∈ blockTri (κ := F) b := by
    rw [mem_blockTri]
    intro i j hij
    rw [hdv]
    exact Matrix.diagonal_apply_ne _ (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
  have hm : mono m = (permGL F m.1 : Matrix (Fin r) (Fin r) F) * (d : Matrix (Fin r) (Fin r) F) := by
    ext a c
    rw [hdv, Matrix.mul_diagonal, permGL_apply]
    by_cases e : a = m.1 c <;> simp [mono, e]
  refine ⟨m.1, ⟨u, hle b' hb' u hu⟩, ⟨d * u', Subgroup.mul_mem _ hd (hle b hb u' hu')⟩, Units.ext ?_⟩
  rw [h, hm]
  simp only [Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FinGL.Bruhat

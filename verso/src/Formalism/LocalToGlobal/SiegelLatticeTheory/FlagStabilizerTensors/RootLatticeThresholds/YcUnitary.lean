import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RankUpdateMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LastDiagMulVec
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVFix

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ)

def Wfg : Matrix (Fin N) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ := Matrix.of fun p k => Sum.elim F G k p

/- English proof (translation)
Use extensionality with `k l`. Rewrite using `[Matrix.mul_assoc]`. Apply the tactic sequence `rcases k with a | a <;> rcases l with b | b <;>`. Simplify using `[hJ, Matrix.mul_apply, mulVec, dotProduct, Wfg, conjTranspose_apply]`.
-/
theorem gram_Wfg : (Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G =
    Matrix.fromBlocks (Matrix.of fun a b => hJ ε (F a) (F b)) (Matrix.of fun a b => hJ ε (F a) (G b))
      (Matrix.of fun a b => hJ ε (G a) (F b)) (Matrix.of fun a b => hJ ε (G a) (G b)) := by
  ext k l
  rw [Matrix.mul_assoc]
  rcases k with a | a <;> rcases l with b | b <;>
    simp [hJ, Matrix.mul_apply, mulVec, dotProduct, Wfg, conjTranspose_apply]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[← mulVec_mulVec]`. Apply the tactic sequence `rcases k with a | b <;> simp [hJ, mulVec, dotProduct, Wfg, conjTranspose_apply]`.
-/
theorem wjx (x : Fin N → ℂ) : ((Wfg F G)ᴴ * Formalism.REAL.Jm ε) *ᵥ x = Sum.elim (fun a => hJ ε (F a) x) (fun b => hJ ε (G b) x) := by
  funext k
  rw [← mulVec_mulVec]
  rcases k with a | b <;> simp [hJ, mulVec, dotProduct, Wfg, conjTranspose_apply]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `[mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Finset.sum_apply, mul_comm]`.
-/
theorem Wfg_mulVec (v : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    Wfg F G *ᵥ v = ∑ a, v (Sum.inl a) • F a + ∑ b, v (Sum.inr b) • G b := by
  funext p
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Finset.sum_apply, mul_comm]

section Main

variable (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1)) (blk : Fin (r + 1) → ℕ)

def Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun a b => hJ ε (F a) (G b)

def Am (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  (Zm ε F G * C⁻¹ * (Zm ε F G)⁻¹)ᴴ

def Mm (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.fromBlocks (Am ε F G C - 1) 0 0 (C - 1)

def Yc (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Ymat (Formalism.REAL.Jm ε) (Wfg F G) (Mm ε F G C)

variable (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases h : ε a = true <;> simp [h]`.
-/
theorem Jm_herm : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

include hFF hGG hπ hZ in
/- English proof (translation)
Rewrite using `[gram_Wfg]`. Use `fromBlocks_inj.2 ⟨?_, rfl, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Simplify using `[hFF]`. Use extensionality with `a b`.

Simplify using `only [of_apply, conjTranspose_apply, Zm]`. Unfold `hJ Formalism.REAL.Jm`. Simplify using `only [mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp <;> ring`.

Use extensionality with `a b`. Simplify using `[hGG]`.
-/
theorem gram_eq : (Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G =
    Matrix.fromBlocks (lastDiag (-(T : ℂ))) (Zm ε F G) (Zm ε F G)ᴴ (lastDiag (-(T' : ℂ))) := by
  rw [gram_Wfg]
  refine fromBlocks_inj.2 ⟨?_, rfl, ?_, ?_⟩
  · ext a b
    simp [hFF]
  · ext a b
    simp only [of_apply, conjTranspose_apply, Zm]
    unfold hJ Formalism.REAL.Jm
    simp only [mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp <;> ring
  · ext a b
    simp [hGG]

include hFF hGG hπ hZ hgap in
/- English proof (translation)
Rewrite using `[gram_eq ε F G T T' π hFF hGG hπ hZ]`. Conclude with `gram_isUnit _ (isUnit_Z π hπ _ hZ) T T' hgap`.
-/
theorem gram_unit : IsUnit ((Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G).det := by
  rw [gram_eq ε F G T T' π hFF hGG hπ hZ]
  exact gram_isUnit _ (isUnit_Z π hπ _ hZ) T T' hgap

include hFF hGG hπ hblk hanti hZ hgap in
/- English proof (translation)
Establish `hA` using `isUB_A π hπ hblk hanti (Zm ε F G) hZ hC`. Establish `hAZC : (Am ε F G C)ᴴ * Zm ε F G * C = Zm ε F G` using `A_Z_C π hπ hblk hanti _ hZ hC`. Establish `hL : ∀ t : ℂ, ∀ i j : Fin (r + 1), i ≠ Fin.last r ∨ j ≠ Fin.last r → lastDiag t i j = 0`. Introduce `t i j h`. Simplify using `only [lastDiag, of_apply]`.

Rewrite using `[if_neg]`. The claim follows by propositional logic. Unfold `Yc`. Use `Ymat_unitary _ (Jm_herm ε) _ _ (gram_unit ε F G T T' π hFF hGG hπ hZ hgap) ?_` and prove the remaining obligations. Rewrite using `[gram_eq ε F G T T' π hFF hGG hπ hZ]`.

Establish `h1 : (1 : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) + Mm ε F G C = fromBlocks (Am ε F G C) 0 0 C`. Rewrite using `[Mm, ← fromBlocks_one, fromBlocks_add]`. Simplify using the standard rewrite rules. Rewrite using `[h1, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `only [conjTranspose_zero, zero_mul, mul_zero, add_zero, zero_add]`.

Use `fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `gram_last hA _ (hL _)`. Conclude with `hAZC`. Establish `h2` using `congrArg conjTranspose hAZC`. Simplify `h2` using `[conjTranspose_mul, Matrix.mul_assoc]`.

Conclude with `gram_last hC _ (hL _)`.
-/
theorem Yc_unitary {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) :
    (Yc ε F G C)ᴴ * Formalism.REAL.Jm ε * Yc ε F G C = Formalism.REAL.Jm ε := by
  have hA := isUB_A π hπ hblk hanti (Zm ε F G) hZ hC
  have hAZC : (Am ε F G C)ᴴ * Zm ε F G * C = Zm ε F G := A_Z_C π hπ hblk hanti _ hZ hC
  have hL : ∀ t : ℂ, ∀ i j : Fin (r + 1), i ≠ Fin.last r ∨ j ≠ Fin.last r → lastDiag t i j = 0 := by
    intro t i j h
    simp only [lastDiag, of_apply]
    rw [if_neg]
    tauto
  unfold Yc
  refine Ymat_unitary _ (Jm_herm ε) _ _ (gram_unit ε F G T T' π hFF hGG hπ hZ hgap) ?_
  rw [gram_eq ε F G T T' π hFF hGG hπ hZ]
  have h1 : (1 : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) + Mm ε F G C =
      fromBlocks (Am ε F G C) 0 0 C := by
    rw [Mm, ← fromBlocks_one, fromBlocks_add]
    simp
  rw [h1, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, zero_mul, mul_zero, add_zero, zero_add]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
  · exact gram_last hA _ (hL _)
  · exact hAZC
  · have h2 := congrArg conjTranspose hAZC
    simpa [conjTranspose_mul, Matrix.mul_assoc] using h2
  · exact gram_last hC _ (hL _)

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors

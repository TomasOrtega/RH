import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC

noncomputable section
namespace GlobalTheory.FockAdj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.FockDeg MvPolynomial Matrix

variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Rewrite using `[← inner_conj_symm, ← inner_X_mul hι, inner_conj_symm]`.
-/
theorem inner_pderiv {σ : Type} [DecidableEq σ] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι)
    (i : σ) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (pderiv i P)) (ι Q) = inner ℂ (ι P) (ι (X i * Q)) := by
  rw [← inner_conj_symm, ← inner_X_mul hι, inner_conj_symm]

/- English proof (translation)
Consider the cases of `hl : linePos l`. Simplify using `only [raiB, lowB, hl, Bool.false_eq_true, if_false] show inner ℂ (ι (-pderiv l P)) (ι Q) = -1 * inner ℂ (ι P) (ι (X l * Q))`. Rewrite using `[map_neg, inner_neg_left, inner_pderiv hι, neg_one_mul]`. Simplify using `only [raiB, lowB, hl, if_true] show inner ℂ (ι (X l * P)) (ι Q) = 1 * inner ℂ (ι P) (ι (pderiv l Q))`. Rewrite using `[inner_X_mul hι, one_mul]`.
-/
theorem inner_raiB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (raiB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (lowB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (-pderiv l P)) (ι Q) = -1 * inner ℂ (ι P) (ι (X l * Q))
    rw [map_neg, inner_neg_left, inner_pderiv hι, neg_one_mul]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (X l * P)) (ι Q) = 1 * inner ℂ (ι P) (ι (pderiv l Q))
    rw [inner_X_mul hι, one_mul]

/- English proof (translation)
Consider the cases of `hl : linePos l`. Simplify using `only [raiB, lowB, hl, Bool.false_eq_true, if_false] show inner ℂ (ι (X l * P)) (ι Q) = -1 * inner ℂ (ι P) (ι (-pderiv l Q))`. Rewrite using `[map_neg, inner_neg_right, inner_X_mul hι, neg_one_mul, neg_neg]`. Simplify using `only [raiB, lowB, hl, if_true] show inner ℂ (ι (pderiv l P)) (ι Q) = 1 * inner ℂ (ι P) (ι (X l * Q))`. Rewrite using `[inner_pderiv hι, one_mul]`.
-/
theorem inner_lowB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (lowB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (raiB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (X l * P)) (ι Q) = -1 * inner ℂ (ι P) (ι (-pderiv l Q))
    rw [map_neg, inner_neg_right, inner_X_mul hι, neg_one_mul, neg_neg]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (pderiv l P)) (ι Q) = 1 * inner ℂ (ι P) (ι (X l * Q))
    rw [inner_pderiv hι, one_mul]

/- English proof (translation)
Establish `h1 : inner ℂ (ι (raiB l (lowB l' P))) (ι Q) = (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (raiB l' (lowB l Q)))`. Rewrite using `[inner_raiB hι, inner_lowB hι, ← mul_assoc]`. Use `congr 1`. Apply the tactic sequence `cases linePos l <;> cases linePos l' <;> simp`. Unfold `omE`.

Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, map_add, inner_add_left, inner_add_right, mul_add, h1]`. Use `congr 1`. Distinguish the cases in `h : l = l'`. Substitute `h` using the available equality. Simplify using `[inner_smul_left, inner_smul_right, map_ofNat]`.

Simplify using `[h, Ne.symm h]`.
-/
theorem inner_omE {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l l' : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q)) := by
  have h1 : inner ℂ (ι (raiB l (lowB l' P))) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (raiB l' (lowB l Q))) := by
    rw [inner_raiB hι, inner_lowB hι, ← mul_assoc]
    congr 1
    cases linePos l <;> cases linePos l' <;> simp
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add, inner_add_left, inner_add_right,
    mul_add, h1]
  congr 1
  by_cases h : l = l'
  · subst h
    simp [inner_smul_left, inner_smul_right, map_ofNat]
  · simp [h, Ne.symm h]

/- English proof (translation)
Simplify using `only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[inner_omE hι, h, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_omAct {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι)
    (M N : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (h : ∀ l l', N l' l = (if linePos l = linePos l' then 1 else -1) * star (M l l'))
    (P Q : Pol p q r s) :
    inner ℂ (ι (omAct p q r s M P)) (ι Q) = inner ℂ (ι P) (ι (omAct p q r s N Q)) := by
  simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [inner_omE hι, h, starRingEnd_apply]
  ring

/- English proof (translation)
Establish `hJ : Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`. Simplify using `[Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[adjZ, hJ, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]`.
-/
theorem adjZ_apply (Z : Mat p q) (a b : Ix p q) :
    adjZ Z a b = (if sameBlock b a then 1 else -1) * star (Z b a) := by
  have hJ : Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [adjZ, hJ, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]

/- English proof (translation)
Introduce `p q r s H _ _ ι hι`. Use `⟨inner_omE hι, fun Z P Q => ?_, fun Z P Q => ?_⟩` and prove the remaining obligations. Rewrite using `[fockAct1_eq, fockAct1_eq]`. Use `inner_omAct hι _ _ ?_ P Q` and prove the remaining obligations. Introduce and unpack `⟨a, c⟩ ⟨b, d⟩`.

Distinguish the cases in `e : c = d`. Substitute `e` using the available equality. Simplify using `[kr1, adjZ_apply, linePos_eq_iff_fst]`. Simplify using `[kr1, e, Ne.symm e]`. Rewrite using `[fockAct2_eq, fockAct2_eq]`.

Use `inner_omAct hι _ _ ?_ P Q` and prove the remaining obligations. Introduce and unpack `⟨a, c⟩ ⟨b, d⟩`. Distinguish the cases in `e : a = b`. Substitute `e` using the available equality. Simplify using `[kr2, adjZ_apply, linePos_eq_iff_snd]`.

Simplify using `[kr2, e, Ne.symm e]`.
-/
theorem fock_adjoints : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι →
    (∀ (l l' : Ln p q r s) (P Q : Pol p q r s), inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q))) ∧
    (∀ (Z : Mat p q) (P Q : Pol p q r s), inner ℂ (ι (fockAct1 p q r s Z P)) (ι Q) =
      inner ℂ (ι P) (ι (fockAct1 p q r s (adjZ Z) Q))) ∧
    (∀ (Z : Mat r s) (P Q : Pol p q r s), inner ℂ (ι (fockAct2 p q r s Z P)) (ι Q) =
      inner ℂ (ι P) (ι (fockAct2 p q r s (adjZ Z) Q))) := by
  intro p q r s H _ _ ι hι
  refine ⟨inner_omE hι, fun Z P Q => ?_, fun Z P Q => ?_⟩
  · rw [fockAct1_eq, fockAct1_eq]
    refine inner_omAct hι _ _ ?_ P Q
    rintro ⟨a, c⟩ ⟨b, d⟩
    by_cases e : c = d
    · subst e
      simp [kr1, adjZ_apply, linePos_eq_iff_fst]
    · simp [kr1, e, Ne.symm e]
  · rw [fockAct2_eq, fockAct2_eq]
    refine inner_omAct hι _ _ ?_ P Q
    rintro ⟨a, c⟩ ⟨b, d⟩
    by_cases e : a = b
    · subst e
      simp [kr2, adjZ_apply, linePos_eq_iff_snd]
    · simp [kr2, e, Ne.symm e]

end GlobalTheory.FockAdj

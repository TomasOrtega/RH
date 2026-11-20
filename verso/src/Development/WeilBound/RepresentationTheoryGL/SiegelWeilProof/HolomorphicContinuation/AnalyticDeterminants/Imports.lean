import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul

noncomputable section

open Filter Topology Set Metric Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolB

variable {n : ℕ}

/- English proof (translation)
Establish `dec : ∀ B : Matrix (Fin n) (Fin n) ℂ, ∃ b₁ b₂ : Matrix (Fin n) (Fin n) ℂ, b₁ᴴ = b₁ ∧ b₂ᴴ = b₂ ∧ B = b₁ + Complex.I • b₂`. Introduce `B`. Establish `hI : Complex.I * -(Complex.I / 2) = 1 / 2`. Rewrite using `[mul_neg, mul_div_assoc', Complex.I_mul_I]`. Evaluate the numerical expressions.

Use `⟨(1 / 2 : ℂ) • (B + Bᴴ), (-(Complex.I / 2)) • (B - Bᴴ), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]`. Use `congr 1`. Simplify using `[Complex.ext_iff]`. Rewrite using `[conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]`.

Rewrite using `[show (Bᴴ - B) = -(B - Bᴴ) by abel, smul_neg, ← neg_smul]`. Use `congr 1`. Simplify using `[Complex.ext_iff]`. Evaluate the numerical expressions. Rewrite using `[smul_smul, hI] module`.

Establish `hU : ∀ B, (fromBlocks 0 B 0 0 : M2 n) ∈ W`. Introduce `B`. Take `⟨b₁, b₂, h₁, h₂, rfl⟩` from `dec B`. Establish `: (fromBlocks 0 (b₁ + Complex.I • b₂) 0 0 : M2 n) = fromBlocks 0 b₁ 0 0 + Complex.I • fromBlocks 0 b₂ 0 0`. Simplify using `[fromBlocks_smul, fromBlocks_add]`.

Rewrite using `[this]`. Conclude with `W.add_mem (hu b₁ h₁) (W.smul_mem _ (hu b₂ h₂))`. Establish `hL : ∀ C, (fromBlocks 0 0 C 0 : M2 n) ∈ W`. Introduce `C`. Take `⟨c₁, c₂, h₁, h₂, rfl⟩` from `dec C`.

Establish `: (fromBlocks 0 0 (c₁ + Complex.I • c₂) 0 : M2 n) = fromBlocks 0 0 c₁ 0 + Complex.I • fromBlocks 0 0 c₂ 0`. Simplify using `[fromBlocks_smul, fromBlocks_add]`. Rewrite using `[this]`. Conclude with `W.add_mem (hl c₁ h₁) (W.smul_mem _ (hl c₂ h₂))`. Establish `hBr : ∀ B C : Matrix (Fin n) (Fin n) ℂ, (fromBlocks (-(B * C)) 0 0 (C * B) : M2 n) ∈ W`.

Introduce `B C`. Take `⟨b₁, b₂, hb₁, hb₂, rfl⟩` from `dec B`. Take `⟨c₁, c₂, hc₁, hc₂, rfl⟩` from `dec C`. Establish `e : (fromBlocks (-((b₁ + Complex.I • b₂) * (c₁ + Complex.I • c₂))) 0 0 ((c₁ + Complex.I • c₂) * (b₁ + Complex.I • b₂)) : M2 n) = fromBlocks (-(b₁ * c₁)) 0 0 (c₁ * b₁) + Complex.I • fromBlocks (-(b₁ * c₂)) 0 0 (c₂ * b₁) + Complex.I • fromBlocks (-(b₂ * c₁)) 0 0 (c₁ * b₂) + (-1 : ℂ …`. Simplify using `only [fromBlocks_smul, fromBlocks_add, smul_zero, add_zero]`.

Use `congr 1`. Apply the tactic sequence `simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul] match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq`. Apply the tactic sequence `simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul] match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq`. Rewrite using `[e]`. Conclude with `W.add_mem (W.add_mem (W.add_mem (hbr _ _ hb₁ hc₁) (W.smul_mem _ (hbr _ _ hb₁ hc₂))) (W.smul_mem _ (hbr _ _ hb₂ hc₁))) (W.smul_mem _ (hbr _ _ hb₂ hc₂))`.

Set `ιA : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n` to `{ toFun := fun A => fromBlocks A 0 0 0 map_add' := fun A B => by simp [fromBlocks_add] map_smul' := fun c A => by simp [fromBlocks_smul] }`. Set `ιD : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n` to `{ toFun := fun D => fromBlocks 0 0 0 D map_add' := fun A B => by simp [fromBlocks_add] map_smul' := fun c A => by simp [fromBlocks_smul] }`. Establish `sgl : ∀ (a b : Fin n) (c : ℂ), Matrix.single a b c = c • Matrix.single a b (1 : ℂ)`. Introduce `a b c`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`.

Establish `offA : ∀ a b : Fin n, a ≠ b → ιA (Matrix.single a b 1) ∈ W`. Introduce `a b hab`. Establish `h` using `hBr (Matrix.single a b 1) (Matrix.single b b 1)`. Rewrite `h` using `[Matrix.single_mul_single_of_ne (h := Ne.symm hab), Matrix.single_mul_single_same, mul_one]`. Establish `: ιA (Matrix.single a b 1) = -(fromBlocks (-(Matrix.single a b (1 : ℂ))) 0 0 0 : M2 n)`.

Simplify using `[ιA, fromBlocks_neg]`. Rewrite using `[this]`. Conclude with `W.neg_mem h`. Establish `offD : ∀ a b : Fin n, a ≠ b → ιD (Matrix.single a b 1) ∈ W`. Introduce `a b hab`.

Establish `h` using `hBr (Matrix.single b b 1) (Matrix.single a b 1)`. Rewrite `h` using `[Matrix.single_mul_single_of_ne (h := Ne.symm hab), Matrix.single_mul_single_same, mul_one]`. Simplify `h` using `[ιD]`. Establish `dif : ∀ a k : Fin n, ιD (Matrix.single k k 1) - ιA (Matrix.single a a 1) ∈ W`. Introduce `a k`.

Establish `h` using `hBr (Matrix.single a k 1) (Matrix.single k a 1)`. Rewrite `h` using `[Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one]`. Establish `: ιD (Matrix.single k k 1) - ιA (Matrix.single a a 1) = (fromBlocks (-(Matrix.single a a (1 : ℂ))) 0 0 (Matrix.single k k 1) : M2 n)`. Simplify using `[ιA, ιD, sub_eq_add_neg, fromBlocks_add, fromBlocks_neg]`. Rewrite using `[this]`.

Conclude with `h`. Establish `one_sum : (∑ a : Fin n, Matrix.single a a (1 : ℂ)) = 1`. Use extensionality with `i j`. Rewrite using `[Matrix.sum_apply]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[Matrix.single_apply]`. Simplify using `[Matrix.single_apply, Matrix.one_apply, h]`. Establish `hST : ∑ a, ιA (Matrix.single a a 1) + ∑ k, ιD (Matrix.single k k 1) ∈ W`. Rewrite using `[← map_sum, ← map_sum, one_sum]`.

Establish `: ιA 1 + ιD 1 = (1 : M2 n)` using `by simp [ιA, ιD, fromBlocks_add, ← fromBlocks_one]`. Rewrite using `[this]`. Conclude with `h1`. Establish `hTS : ∑ k, ιD (Matrix.single k k 1) - ∑ a, ιA (Matrix.single a a 1) ∈ W`. Rewrite using `[← Finset.sum_sub_distrib]`.

Conclude with `W.sum_mem fun k _ => dif k k`. Establish `hT : ∑ k, ιD (Matrix.single k k 1) ∈ W`. Establish `h2` using `W.add_mem hST hTS`. Establish `: ∑ k, ιD (Matrix.single k k 1) = (1 / 2 : ℂ) • ((∑ a, ιA (Matrix.single a a 1) + ∑ k, ιD (Matrix.single k k 1)) + (∑ k, ιD (Matrix.single k k 1) - ∑ a, ιA (Matrix.single a a 1)))` using `by module`. Rewrite using `[this]`.

Conclude with `W.smul_mem _ h2`. Establish `hS : ∑ a, ιA (Matrix.single a a 1) ∈ W`. Use `W.sub_mem hST hT` as an intermediate fact. Simplify using `using this`. Establish `diagA : ∀ a : Fin n, ιA (Matrix.single a a 1) ∈ W`.

Introduce `a`. Establish `hn : (Fintype.card (Fin n) : ℂ) ≠ 0`. Simplify using `only [Fintype.card_fin, ne_eq, Nat.cast_eq_zero]`. Conclude with `Fin.pos a |>.ne'`. Establish `hdiff : ∀ b : Fin n, ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1) ∈ W`.

Introduce `b`. Use `W.sub_mem (dif b a) (dif a a)` as an intermediate fact. Establish `e : ιD (Matrix.single a a 1) - ιA (Matrix.single b b 1) - (ιD (Matrix.single a a 1) - ιA (Matrix.single a a 1)) = ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1)` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hsum` using `W.add_mem (W.sum_mem fun b (_ : b ∈ Finset.univ) => hdiff b) hS`.

Establish `e : ∑ b, (ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1)) + ∑ a, ιA (Matrix.single a a 1) = (Fintype.card (Fin n) : ℂ) • ιA (Matrix.single a a 1)`. Rewrite using `[Finset.sum_sub_distrib, sub_add_cancel, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]`. Rewrite `hsum` using `[e]`. Use `W.smul_mem ((Fintype.card (Fin n) : ℂ)⁻¹) hsum` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hn, one_smul]`. Then use the resulting hypothesis.

Establish `diagD : ∀ k : Fin n, ιD (Matrix.single k k 1) ∈ W`. Introduce `k`. Use `W.add_mem (dif k k) (diagA k)` as an intermediate fact. Simplify using `using this`. Establish `allA : ∀ A : Matrix (Fin n) (Fin n) ℂ, ιA A ∈ W`.

Introduce `A`. Rewrite using `[Matrix.matrix_eq_sum_single A, map_sum]`. Use `W.sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `W.sum_mem fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[sgl, map_smul]`. Use `W.smul_mem _ ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Conclude with `diagA i`.

Conclude with `offA i j hij`. Establish `allD : ∀ D : Matrix (Fin n) (Fin n) ℂ, ιD D ∈ W`. Introduce `D`. Rewrite using `[Matrix.matrix_eq_sum_single D, map_sum]`. Use `W.sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `W.sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[sgl, map_smul]`. Use `W.smul_mem _ ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Conclude with `diagD i`. Conclude with `offD i j hij`. Rewrite using `[eq_top_iff]`. Introduce `M _`.

Rewrite using `[← Matrix.fromBlocks_toBlocks M]`. Establish `e : (fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ : M2 n) = ιA M.toBlocks₁₁ + fromBlocks 0 M.toBlocks₁₂ 0 0 + fromBlocks 0 0 M.toBlocks₂₁ 0 + ιD M.toBlocks₂₂`. Simplify using `[ιA, ιD, fromBlocks_add]`. Rewrite using `[e]`. Conclude with `W.add_mem (W.add_mem (W.add_mem (allA _) (hU _)) (hL _)) (allD _)`.
-/
theorem span_top (W : Submodule ℂ (M2 n))
    (hu : ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → (fromBlocks 0 b 0 0 : M2 n) ∈ W)
    (hl : ∀ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c → (fromBlocks 0 0 c 0 : M2 n) ∈ W)
    (hbr : ∀ b c : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → cᴴ = c → (fromBlocks (-(b * c)) 0 0 (c * b) : M2 n) ∈ W)
    (h1 : (1 : M2 n) ∈ W) : W = ⊤ := by

  have dec : ∀ B : Matrix (Fin n) (Fin n) ℂ, ∃ b₁ b₂ : Matrix (Fin n) (Fin n) ℂ, b₁ᴴ = b₁ ∧ b₂ᴴ = b₂ ∧
      B = b₁ + Complex.I • b₂ := by
    intro B
    have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]; norm_num
    refine ⟨(1 / 2 : ℂ) • (B + Bᴴ), (-(Complex.I / 2)) • (B - Bᴴ), ?_, ?_, ?_⟩
    · rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
      congr 1
      simp [Complex.ext_iff]
    · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      rw [show (Bᴴ - B) = -(B - Bᴴ) by abel, smul_neg, ← neg_smul]
      congr 1
      simp [Complex.ext_iff]
      norm_num
    · rw [smul_smul, hI]
      module
  have hU : ∀ B, (fromBlocks 0 B 0 0 : M2 n) ∈ W := by
    intro B
    obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := dec B
    have : (fromBlocks 0 (b₁ + Complex.I • b₂) 0 0 : M2 n) =
        fromBlocks 0 b₁ 0 0 + Complex.I • fromBlocks 0 b₂ 0 0 := by
      simp [fromBlocks_smul, fromBlocks_add]
    rw [this]
    exact W.add_mem (hu b₁ h₁) (W.smul_mem _ (hu b₂ h₂))
  have hL : ∀ C, (fromBlocks 0 0 C 0 : M2 n) ∈ W := by
    intro C
    obtain ⟨c₁, c₂, h₁, h₂, rfl⟩ := dec C
    have : (fromBlocks 0 0 (c₁ + Complex.I • c₂) 0 : M2 n) =
        fromBlocks 0 0 c₁ 0 + Complex.I • fromBlocks 0 0 c₂ 0 := by
      simp [fromBlocks_smul, fromBlocks_add]
    rw [this]
    exact W.add_mem (hl c₁ h₁) (W.smul_mem _ (hl c₂ h₂))
  have hBr : ∀ B C : Matrix (Fin n) (Fin n) ℂ, (fromBlocks (-(B * C)) 0 0 (C * B) : M2 n) ∈ W := by
    intro B C
    obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := dec B
    obtain ⟨c₁, c₂, hc₁, hc₂, rfl⟩ := dec C
    have e : (fromBlocks (-((b₁ + Complex.I • b₂) * (c₁ + Complex.I • c₂))) 0 0
        ((c₁ + Complex.I • c₂) * (b₁ + Complex.I • b₂)) : M2 n) =
        fromBlocks (-(b₁ * c₁)) 0 0 (c₁ * b₁) + Complex.I • fromBlocks (-(b₁ * c₂)) 0 0 (c₂ * b₁) +
          Complex.I • fromBlocks (-(b₂ * c₁)) 0 0 (c₁ * b₂) + (-1 : ℂ) • fromBlocks (-(b₂ * c₂)) 0 0 (c₂ * b₂) := by
      simp only [fromBlocks_smul, fromBlocks_add, smul_zero, add_zero]
      congr 1
      · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
        match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
      · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
        match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
    rw [e]
    exact W.add_mem (W.add_mem (W.add_mem (hbr _ _ hb₁ hc₁) (W.smul_mem _ (hbr _ _ hb₁ hc₂)))
      (W.smul_mem _ (hbr _ _ hb₂ hc₁))) (W.smul_mem _ (hbr _ _ hb₂ hc₂))

  let ιA : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun A => fromBlocks A 0 0 0
      map_add' := fun A B => by simp [fromBlocks_add]
      map_smul' := fun c A => by simp [fromBlocks_smul] }
  let ιD : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun D => fromBlocks 0 0 0 D
      map_add' := fun A B => by simp [fromBlocks_add]
      map_smul' := fun c A => by simp [fromBlocks_smul] }
  have sgl : ∀ (a b : Fin n) (c : ℂ), Matrix.single a b c = c • Matrix.single a b (1 : ℂ) := by
    intro a b c; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have offA : ∀ a b : Fin n, a ≠ b → ιA (Matrix.single a b 1) ∈ W := by
    intro a b hab
    have h := hBr (Matrix.single a b 1) (Matrix.single b b 1)
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hab), Matrix.single_mul_single_same, mul_one] at h
    have : ιA (Matrix.single a b 1) = -(fromBlocks (-(Matrix.single a b (1 : ℂ))) 0 0 0 : M2 n) := by
      simp [ιA, fromBlocks_neg]
    rw [this]; exact W.neg_mem h
  have offD : ∀ a b : Fin n, a ≠ b → ιD (Matrix.single a b 1) ∈ W := by
    intro a b hab
    have h := hBr (Matrix.single b b 1) (Matrix.single a b 1)
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hab), Matrix.single_mul_single_same, mul_one] at h
    simpa [ιD] using h
  have dif : ∀ a k : Fin n, ιD (Matrix.single k k 1) - ιA (Matrix.single a a 1) ∈ W := by
    intro a k
    have h := hBr (Matrix.single a k 1) (Matrix.single k a 1)
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one] at h
    have : ιD (Matrix.single k k 1) - ιA (Matrix.single a a 1) =
        (fromBlocks (-(Matrix.single a a (1 : ℂ))) 0 0 (Matrix.single k k 1) : M2 n) := by
      simp [ιA, ιD, sub_eq_add_neg, fromBlocks_add, fromBlocks_neg]
    rw [this]; exact h
  have one_sum : (∑ a : Fin n, Matrix.single a a (1 : ℂ)) = 1 := by
    ext i j
    rw [Matrix.sum_apply]
    by_cases h : i = j
    · subst h; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, Matrix.one_apply, h]
  have hST : ∑ a, ιA (Matrix.single a a 1) + ∑ k, ιD (Matrix.single k k 1) ∈ W := by
    rw [← map_sum, ← map_sum, one_sum]
    have : ιA 1 + ιD 1 = (1 : M2 n) := by simp [ιA, ιD, fromBlocks_add, ← fromBlocks_one]
    rw [this]; exact h1
  have hTS : ∑ k, ιD (Matrix.single k k 1) - ∑ a, ιA (Matrix.single a a 1) ∈ W := by
    rw [← Finset.sum_sub_distrib]
    exact W.sum_mem fun k _ => dif k k
  have hT : ∑ k, ιD (Matrix.single k k 1) ∈ W := by
    have h2 := W.add_mem hST hTS
    have : ∑ k, ιD (Matrix.single k k 1) = (1 / 2 : ℂ) • ((∑ a, ιA (Matrix.single a a 1) +
        ∑ k, ιD (Matrix.single k k 1)) + (∑ k, ιD (Matrix.single k k 1) - ∑ a, ιA (Matrix.single a a 1))) := by
      module
    rw [this]; exact W.smul_mem _ h2
  have hS : ∑ a, ιA (Matrix.single a a 1) ∈ W := by
    have := W.sub_mem hST hT
    simpa using this
  have diagA : ∀ a : Fin n, ιA (Matrix.single a a 1) ∈ W := by
    intro a
    have hn : (Fintype.card (Fin n) : ℂ) ≠ 0 := by
      simp only [Fintype.card_fin, ne_eq, Nat.cast_eq_zero]; exact Fin.pos a |>.ne'
    have hdiff : ∀ b : Fin n, ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1) ∈ W := by
      intro b
      have := W.sub_mem (dif b a) (dif a a)
      have e : ιD (Matrix.single a a 1) - ιA (Matrix.single b b 1) - (ιD (Matrix.single a a 1) -
          ιA (Matrix.single a a 1)) = ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1) := by abel
      rwa [e] at this
    have hsum := W.add_mem (W.sum_mem fun b (_ : b ∈ Finset.univ) => hdiff b) hS
    have e : ∑ b, (ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1)) + ∑ a, ιA (Matrix.single a a 1) =
        (Fintype.card (Fin n) : ℂ) • ιA (Matrix.single a a 1) := by
      rw [Finset.sum_sub_distrib, sub_add_cancel, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [e] at hsum
    have := W.smul_mem ((Fintype.card (Fin n) : ℂ)⁻¹) hsum
    rwa [smul_smul, inv_mul_cancel₀ hn, one_smul] at this
  have diagD : ∀ k : Fin n, ιD (Matrix.single k k 1) ∈ W := by
    intro k
    have := W.add_mem (dif k k) (diagA k)
    simpa using this
  have allA : ∀ A : Matrix (Fin n) (Fin n) ℂ, ιA A ∈ W := by
    intro A
    rw [Matrix.matrix_eq_sum_single A, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [map_sum]
    refine W.sum_mem fun j _ => ?_
    rw [sgl, map_smul]
    refine W.smul_mem _ ?_
    by_cases hij : i = j
    · subst hij; exact diagA i
    · exact offA i j hij
  have allD : ∀ D : Matrix (Fin n) (Fin n) ℂ, ιD D ∈ W := by
    intro D
    rw [Matrix.matrix_eq_sum_single D, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [map_sum]
    refine W.sum_mem fun j _ => ?_
    rw [sgl, map_smul]
    refine W.smul_mem _ ?_
    by_cases hij : i = j
    · subst hij; exact diagD i
    · exact offD i j hij
  rw [eq_top_iff]
  intro M _
  rw [← Matrix.fromBlocks_toBlocks M]
  have e : (fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ : M2 n) =
      ιA M.toBlocks₁₁ + fromBlocks 0 M.toBlocks₁₂ 0 0 + fromBlocks 0 0 M.toBlocks₂₁ 0 + ιD M.toBlocks₂₂ := by
    simp [ιA, ιD, fromBlocks_add]
  rw [e]
  exact W.add_mem (W.add_mem (W.add_mem (allA _) (hU _)) (hL _)) (allD _)

end PositivityTheory.Rg.Sw.LVs.HolC

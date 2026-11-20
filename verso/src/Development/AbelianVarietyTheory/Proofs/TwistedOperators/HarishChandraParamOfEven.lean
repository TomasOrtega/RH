import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
open Formalism.L2.Theta

namespace GlobalTheory.HCEnum

open GlobalTheory.SignedHC GlobalTheory.SignedHC.GridData

/- English proof (translation)
Introduce `G n lam ε mu ε' hk hm hn hl hmu`. Take `⟨k', hk'⟩` from `hk`. Take `⟨m', hm'⟩` from `hm`. Establish `hkR : (G.k : ℝ) = k' + k'` using `by rw [hk']; push_cast; ring`. Establish `hmR : (G.m : ℝ) = m' + m'` using `by rw [hm']; push_cast; ring`.

Establish `hnR : (n : ℝ) = (G.k : ℝ) + G.m - 1`. Establish `: ((n + 1 : ℕ) : ℝ) = ((G.k + G.m : ℕ) : ℝ)` using `by rw [hn]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨⟨hl.1, fun a => ?_⟩, ⟨hmu.1, fun a => ?_⟩⟩` and prove the remaining obligations.

Take `⟨-, q, hq, hS⟩` from `hl`. Establish `hmem : (q a, ε a) ∈ G.parPi 0`. Rewrite using `[hS]`. Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ a)`. Rewrite `hmem` using `[parPi_zero, mem_lam]`.

Rewrite using `[hq a]`. Break down `hmem with ⟨i, -, he⟩ | ⟨hc, -⟩` into its components or cases. Establish `e : q a = G.a i` using `congrArg Prod.fst he`. Use `⟨G.v 2 + ((G.m : ℤ) + 1 - i) * G.ga + 1 - (k' + m'), ?_⟩` and prove the remaining obligations. Rewrite using `[e]`.

Simplify using `only [GridData.a]`. Use `push_cast`. Rewrite using `[hnR, hkR, hmR]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨i, -, -, hx⟩` from `mem_cloudHalf.1 hc`.

Simplify using `only at hx`. Use `⟨G.v i - (k' + m'), ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`. Simplify using `only [vHalf]`. Use `push_cast`.

Rewrite using `[hnR, hkR, hmR]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨-, q, hq, hS⟩` from `hmu`. Establish `hmem : (q a, ε' a) ∈ G.parD0`. Rewrite using `[hS]`.

Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ a)`. Rewrite `hmem` using `[mem_discrete_parameter_iff]`. Rewrite using `[hq a]`. Break down `hmem with ⟨hc, -⟩ | ⟨l, -, -, he⟩` into its components or cases. Take `⟨i, -, -, hx⟩` from `mem_cloud.1 hc`.

Simplify using `only at hx`. Use `⟨G.v i - (k' + m' - 1), ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`. Use `push_cast`. Rewrite using `[hnR, hkR, hmR]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e : q a = -(G.b l : ℚ)` using `congrArg Prod.fst he`. Use `⟨-G.b l - (k' + m' - 1), ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Use `push_cast`.

Rewrite using `[hnR, hkR, hmR]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isHCParam_parPi_zero_parD0 : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ}
    {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.k → Even G.m → n + 1 = G.k + G.m →
    IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.IsHCParam mu := by
  intro G n lam ε mu ε' hk hm hn hl hmu
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  have hkR : (G.k : ℝ) = k' + k' := by rw [hk']; push_cast; ring
  have hmR : (G.m : ℝ) = m' + m' := by rw [hm']; push_cast; ring
  have hnR : (n : ℝ) = (G.k : ℝ) + G.m - 1 := by
    have : ((n + 1 : ℕ) : ℝ) = ((G.k + G.m : ℕ) : ℝ) := by rw [hn]
    push_cast at this; linarith
  refine ⟨⟨hl.1, fun a => ?_⟩, ⟨hmu.1, fun a => ?_⟩⟩
  · obtain ⟨-, q, hq, hS⟩ := hl
    have hmem : (q a, ε a) ∈ G.parPi 0 := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [parPi_zero, mem_lam] at hmem
    rw [hq a]
    rcases hmem with ⟨i, -, he⟩ | ⟨hc, -⟩
    · have e : q a = G.a i := congrArg Prod.fst he
      refine ⟨G.v 2 + ((G.m : ℤ) + 1 - i) * G.ga + 1 - (k' + m'), ?_⟩
      rw [e]; simp only [GridData.a]; push_cast; rw [hnR, hkR, hmR]; ring
    · obtain ⟨i, -, -, hx⟩ := mem_cloudHalf.1 hc
      simp only at hx
      refine ⟨G.v i - (k' + m'), ?_⟩
      rw [hx]; simp only [vHalf]; push_cast; rw [hnR, hkR, hmR]; ring
  · obtain ⟨-, q, hq, hS⟩ := hmu
    have hmem : (q a, ε' a) ∈ G.parD0 := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [mem_discrete_parameter_iff] at hmem
    rw [hq a]
    rcases hmem with ⟨hc, -⟩ | ⟨l, -, -, he⟩
    · obtain ⟨i, -, -, hx⟩ := mem_cloud.1 hc
      simp only at hx
      refine ⟨G.v i - (k' + m' - 1), ?_⟩
      rw [hx]; push_cast; rw [hnR, hkR, hmR]; ring
    · have e : q a = -(G.b l : ℚ) := congrArg Prod.fst he
      refine ⟨-G.b l - (k' + m' - 1), ?_⟩
      rw [e]; push_cast; rw [hnR, hkR, hmR]; ring

end GlobalTheory.HCEnum

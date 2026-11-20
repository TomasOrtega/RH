import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIsGaloisTwistedNormGLMulCardGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjOfIsConjGlFieldExtensionInclusionStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `F F' _ _ _ _ s hs n δ₀`. Use `haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective`. Use `haveI : Finite (GL (Fin n) F) := inferInstance`. Use `haveI : Finite (GL (Fin n) F') := inferInstance`. Use `letI := Fintype.ofFinite (GL (Fin n) F)`.

Use `letI := Fintype.ofFinite (GL (Fin n) F')`. Establish `hfib` using `GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL F F' s hs n`. Establish `hnd` using `GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion F F' n`. Set `cl : GL (Fin n) F → ℕ` to `fun γ => Nat.card {γ' : GL (Fin n) F // IsConj γ γ'}`. Establish `hcl_pos : ∀ γ, 0 < cl γ` using `fun γ => Nat.card_pos_iff.2 ⟨⟨⟨γ, IsConj.refl γ⟩⟩, inferInstance⟩`.

Establish `hcl_eq : ∀ γ, (cl γ : ℚ) = ((Finset.univ.filter fun γ' => IsConj γ γ').card : ℚ)`. Introduce `γ`. Simplify using `only [cl, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Establish `hcard : ∀ γ, Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} = (Finset.univ.filter fun δ => IsNorm s δ γ).card`. Introduce `γ`.

Simplify using `only [Nat.card_eq_fintype_card, Fintype.card_subtype]`. Set `f : GL (Fin n) F' → GL (Fin n) F → ℚ` to `fun δ γ => if IsNorm s δ γ then ((cl γ : ℚ))⁻¹ else 0`. Establish `h1 : ∀ δ, ∑ γ, f δ γ = if ∃ γ, IsNorm s δ γ then 1 else 0`. Introduce `δ`. Distinguish the cases in `h : ∃ γ, IsNorm s δ γ`.

Take `⟨γ₀, h₀⟩` from `h`. Rewrite using `[if_pos ⟨γ₀, h₀⟩]`. Establish `hiff : ∀ γ, IsNorm s δ γ ↔ IsConj γ₀ γ`. Introduce `γ`. Prove the components needed by the constructor for the conclusion.

Introduce `hγ`. Conclude with `hnd γ₀ γ (h₀.trans hγ.symm)`. Introduce `hγ`. Conclude with `(isConj_iff.2 (by`. Take `⟨c, hc⟩` from `isConj_iff.1 hγ`.

Conclude with `⟨incl F F' n c, by rw [← hc]; simp [map_mul, map_inv]⟩)).symm.trans h₀`. Establish `hcl' : ∀ γ, IsConj γ₀ γ → cl γ = cl γ₀`. Introduce `γ hγ`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun γ' => ⟨fun h => hγ.trans h, fun h => hγ.symm.trans h⟩)`. Establish `: ∀ γ, f δ γ = if IsConj γ₀ γ then ((cl γ₀ : ℚ))⁻¹ else 0`.

Introduce `γ`. Simplify using `only [f, hiff γ]`. Use `split_ifs with hh`. Rewrite using `[hcl' γ hh]`. Both sides reduce to the same expression.

Simplify using `only [this]`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcl_eq]`. Conclude with `mul_inv_cancel₀ (by exact_mod_cast (hcl_pos γ₀).ne')`. Rewrite using `[if_neg h]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `γ _`. Simplify using `only [f]`. Rewrite using `[if_neg (fun hh => h ⟨γ, hh⟩)]`. Establish `h2 : ∀ γ, ∑ δ, f δ γ = (Nat.card (GL (Fin n) F') : ℚ) / Nat.card (GL (Fin n) F)`. Introduce `γ`.

Simplify using `only [f]`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcard]`. Establish `hG : (0 : ℚ) < Nat.card (GL (Fin n) F)` using `by exact_mod_cast Nat.card_pos`. Establish `hc : (0 : ℚ) < cl γ` using `by exact_mod_cast hcl_pos γ`. Establish `hq : (Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} : ℚ) * Nat.card (GL (Fin n) F) = cl γ * Nat.card (GL (Fin n) F')` using `by exact_mod_cast hfib γ`.

Clear the denominators using the available nonvanishing facts. Combine the linear relations using `[hq]`. Establish `hsum : ∑ δ : GL (Fin n) F', (if ∃ γ, IsNorm s δ γ then (1 : ℚ) else 0) = ∑ δ : GL (Fin n) F', (1 : ℚ)`. Simplify using `only [← h1]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [h2]`. Rewrite using `[Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]`. Establish `hG : (0 : ℚ) < Nat.card (GL (Fin n) F)` using `by exact_mod_cast Nat.card_pos`. Clear the denominators using the available nonvanishing facts. Establish `hle : ∀ δ ∈ (Finset.univ : Finset (GL (Fin n) F')), (if ∃ γ, IsNorm s δ γ then (1 : ℚ) else 0) ≤ 1`.

Introduce `δ _`. Apply the tactic sequence `split_ifs <;> norm_num`. Use `(Finset.sum_eq_sum_iff_of_le hle).1 hsum δ₀ (Finset.mem_univ _)` as an intermediate fact. Assume the negation of the conclusion as `hno`. Rewrite `this` using `[if_neg hno]`.

Evaluate the numerical expressions using `at this`.
-/
theorem exists_isNorm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F'), ∃ γ : GL (Fin n) F, IsNorm s δ γ := by
  intro F F' _ _ _ _ s hs n δ₀
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Finite (GL (Fin n) F) := inferInstance
  haveI : Finite (GL (Fin n) F') := inferInstance
  letI := Fintype.ofFinite (GL (Fin n) F)
  letI := Fintype.ofFinite (GL (Fin n) F')
  have hfib := GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL F F' s hs n
  have hnd := GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion F F' n
  let cl : GL (Fin n) F → ℕ := fun γ => Nat.card {γ' : GL (Fin n) F // IsConj γ γ'}
  have hcl_pos : ∀ γ, 0 < cl γ := fun γ => Nat.card_pos_iff.2 ⟨⟨⟨γ, IsConj.refl γ⟩⟩, inferInstance⟩
  have hcl_eq : ∀ γ, (cl γ : ℚ) = ((Finset.univ.filter fun γ' => IsConj γ γ').card : ℚ) := by
    intro γ
    simp only [cl, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard : ∀ γ, Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ}
      = (Finset.univ.filter fun δ => IsNorm s δ γ).card := by
    intro γ
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let f : GL (Fin n) F' → GL (Fin n) F → ℚ := fun δ γ => if IsNorm s δ γ then ((cl γ : ℚ))⁻¹ else 0
  have h1 : ∀ δ, ∑ γ, f δ γ = if ∃ γ, IsNorm s δ γ then 1 else 0 := by
    intro δ
    by_cases h : ∃ γ, IsNorm s δ γ
    · obtain ⟨γ₀, h₀⟩ := h
      rw [if_pos ⟨γ₀, h₀⟩]
      have hiff : ∀ γ, IsNorm s δ γ ↔ IsConj γ₀ γ := by
        intro γ
        constructor
        · intro hγ
          exact hnd γ₀ γ (h₀.trans hγ.symm)
        · intro hγ
          exact (isConj_iff.2 (by
            obtain ⟨c, hc⟩ := isConj_iff.1 hγ
            exact ⟨incl F F' n c, by rw [← hc]; simp [map_mul, map_inv]⟩)).symm.trans h₀
      have hcl' : ∀ γ, IsConj γ₀ γ → cl γ = cl γ₀ := by
        intro γ hγ
        exact Nat.card_congr (Equiv.subtypeEquivRight fun γ' => ⟨fun h => hγ.trans h, fun h => hγ.symm.trans h⟩)
      have : ∀ γ, f δ γ = if IsConj γ₀ γ then ((cl γ₀ : ℚ))⁻¹ else 0 := by
        intro γ
        simp only [f, hiff γ]
        split_ifs with hh
        · rw [hcl' γ hh]
        · rfl
      simp only [this]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcl_eq]
      exact mul_inv_cancel₀ (by exact_mod_cast (hcl_pos γ₀).ne')
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro γ _
      simp only [f]
      rw [if_neg (fun hh => h ⟨γ, hh⟩)]
  have h2 : ∀ γ, ∑ δ, f δ γ = (Nat.card (GL (Fin n) F') : ℚ) / Nat.card (GL (Fin n) F) := by
    intro γ
    simp only [f]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcard]
    have hG : (0 : ℚ) < Nat.card (GL (Fin n) F) := by exact_mod_cast Nat.card_pos
    have hc : (0 : ℚ) < cl γ := by exact_mod_cast hcl_pos γ
    have hq : (Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} : ℚ) * Nat.card (GL (Fin n) F)
        = cl γ * Nat.card (GL (Fin n) F') := by exact_mod_cast hfib γ
    field_simp
    linarith [hq]
  have hsum : ∑ δ : GL (Fin n) F', (if ∃ γ, IsNorm s δ γ then (1 : ℚ) else 0) = ∑ δ : GL (Fin n) F', (1 : ℚ) := by
    simp only [← h1]
    rw [Finset.sum_comm]
    simp only [h2]
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have hG : (0 : ℚ) < Nat.card (GL (Fin n) F) := by exact_mod_cast Nat.card_pos
    field_simp
  have hle : ∀ δ ∈ (Finset.univ : Finset (GL (Fin n) F')),
      (if ∃ γ, IsNorm s δ γ then (1 : ℚ) else 0) ≤ 1 := by
    intro δ _
    split_ifs <;> norm_num
  have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum δ₀ (Finset.mem_univ _)
  by_contra hno
  rw [if_neg hno] at this
  norm_num at this

end GlobalTheory.Shin

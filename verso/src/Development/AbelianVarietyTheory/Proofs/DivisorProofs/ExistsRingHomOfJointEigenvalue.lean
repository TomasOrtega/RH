import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

open Matrix

/- English proof (translation)
Take `⟨x, hxmem, hx0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Use `set ψ : Λ →+* Matrix (Fin h) (Fin h) C := (algebraMap O C).mapMatrix.comp ρ with hψ`. Establish `hψa : ∀ a, (ρ a).map (algebraMap O C) = ψ a` using `fun a => rfl`. Establish `hE : ∀ a, ψ a *ᵥ x = χ a • x`. Introduce `a`.

Use `(Submodule.mem_iInf _).1 hxmem a` as an intermediate fact. Rewrite `this` using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hψa]`. Conclude with `this`. Establish `canc : ∀ c d : C, c • x = d • x → c = d` using `fun c d hcd => smul_left_injective C hx0 hcd`. Establish `h1 : χ 1 = 1` using `canc _ _ (by rw [← hE, map_one, Matrix.one_mulVec, one_smul])`.

Establish `hadd : ∀ a b, χ (a + b) = χ a + χ b` using `fun a b => canc _ _ (by rw [← hE, map_add, Matrix.add_mulVec, hE, hE, add_smul])`. Establish `hmul : ∀ a b, χ (a * b) = χ a * χ b` using `fun a b => canc _ _ (by rw [← hE, map_mul, ← Matrix.mulVec_mulVec, hE, Matrix.mulVec_smul, hE, smul_smul, mul_comm])`. Establish `h0 : χ 0 = 0` using `canc _ _ (by rw [← hE, map_zero, Matrix.zero_mulVec, zero_smul])`. Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hx0 (funext hcon)`. Take `⟨i, -, hi⟩` from `Finset.exists_max_image Finset.univ (fun j => v (x j)) ⟨i0, Finset.mem_univ _⟩`. Establish `hvi : v (x i) ≠ 0`. Introduce `h'`.

Use `hi i0 (Finset.mem_univ _)` as an intermediate fact. Rewrite `this` using `[h']`. Conclude with `hi0 ((Valuation.zero_iff v).1 (le_antisymm this (zero_le')))`. Establish `hint : ∀ a, v (χ a) ≤ 1`. Introduce `a`.

Establish `hrow : χ a * x i = ∑ j, ψ a i j * x j`. Use `congrFun (hE a) i` as an intermediate fact. Rewrite `this` using `[Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← this]`. Both sides reduce to the same expression.

Establish `hle : v (χ a * x i) ≤ v (x i)`. Rewrite using `[hrow]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul' _ (hi j (Finset.mem_univ _))` to reduce the goal to its premises. Conclude with `hv.map_le_one _`. Use `_ = v (x i) := one_mul _`. Rewrite `hle` using `[map_mul]`.

Establish `hpos : 0 < v (x i)` using `lt_of_le_of_ne (zero_le') (Ne.symm hvi)`. Conclude with `le_of_mul_le_mul_right (by rwa [one_mul]) hpos`. Use `choose σf hσf using fun a => hv.exists_of_le_one (hint a)`. Use `⟨{ toFun := σf, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hσf⟩` and prove the remaining obligations. Conclude with `hv.hom_inj (by rw [hσf, h1, map_one])`.

Introduce `a b; exact hv.hom_inj (by rw [hσf, map_mul, hσf, hσf, hmul])`. Conclude with `hv.hom_inj (by rw [hσf, h0, map_zero])`. Introduce `a b; exact hv.hom_inj (by rw [hσf, map_add, hσf, hσf, hadd])`.
-/
theorem jointEigen_ringHom_toIntegers (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (hv : v.Integers O)
    (ρ : Λ →+* Matrix (Fin h) (Fin h) O) (χ : Λ → C)
    (hne : (⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C))) (χ a)) ≠ ⊥) :
    ∃ σ : Λ →+* O, ∀ a, algebraMap O C (σ a) = χ a := by
  obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  set ψ : Λ →+* Matrix (Fin h) (Fin h) C := (algebraMap O C).mapMatrix.comp ρ with hψ
  have hψa : ∀ a, (ρ a).map (algebraMap O C) = ψ a := fun a => rfl
  have hE : ∀ a, ψ a *ᵥ x = χ a • x := by
    intro a
    have := (Submodule.mem_iInf _).1 hxmem a
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hψa] at this
    exact this
  have canc : ∀ c d : C, c • x = d • x → c = d := fun c d hcd => smul_left_injective C hx0 hcd
  have h1 : χ 1 = 1 := canc _ _ (by rw [← hE, map_one, Matrix.one_mulVec, one_smul])
  have hadd : ∀ a b, χ (a + b) = χ a + χ b := fun a b =>
    canc _ _ (by rw [← hE, map_add, Matrix.add_mulVec, hE, hE, add_smul])
  have hmul : ∀ a b, χ (a * b) = χ a * χ b := fun a b =>
    canc _ _ (by rw [← hE, map_mul, ← Matrix.mulVec_mulVec, hE, Matrix.mulVec_smul, hE, smul_smul, mul_comm])
  have h0 : χ 0 = 0 := canc _ _ (by rw [← hE, map_zero, Matrix.zero_mulVec, zero_smul])

  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx0 (funext hcon)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => v (x j)) ⟨i0, Finset.mem_univ _⟩
  have hvi : v (x i) ≠ 0 := by
    intro h'
    have := hi i0 (Finset.mem_univ _)
    rw [h'] at this
    exact hi0 ((Valuation.zero_iff v).1 (le_antisymm this (zero_le')))
  have hint : ∀ a, v (χ a) ≤ 1 := by
    intro a
    have hrow : χ a * x i = ∑ j, ψ a i j * x j := by
      have := congrFun (hE a) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]; rfl
    have hle : v (χ a * x i) ≤ v (x i) := by
      rw [hrow]
      apply Valuation.map_sum_le
      intro j _
      rw [map_mul]
      calc v (ψ a i j) * v (x j) ≤ 1 * v (x i) := by
            apply mul_le_mul' _ (hi j (Finset.mem_univ _))
            exact hv.map_le_one _
        _ = v (x i) := one_mul _
    rw [map_mul] at hle
    have hpos : 0 < v (x i) := lt_of_le_of_ne (zero_le') (Ne.symm hvi)
    exact le_of_mul_le_mul_right (by rwa [one_mul]) hpos
  choose σf hσf using fun a => hv.exists_of_le_one (hint a)
  refine ⟨{ toFun := σf, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hσf⟩
  · exact hv.hom_inj (by rw [hσf, h1, map_one])
  · intro a b; exact hv.hom_inj (by rw [hσf, map_mul, hσf, hσf, hmul])
  · exact hv.hom_inj (by rw [hσf, h0, map_zero])
  · intro a b; exact hv.hom_inj (by rw [hσf, map_add, hσf, hσf, hadd])

end GlobalTheory

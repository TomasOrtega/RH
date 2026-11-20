import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.Proof.BlockConj

/- English proof (translation)
Establish `h1 : Set.range (blockEnum b c h) = (block b c : Set (Fin r))` using `Finset.range_orderEmbOfFin (block b c) h`. Rewrite using `[h1]`. Simplify using `[block]`.
-/
theorem range_blockEnum {r d : ℕ} (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (k : Fin r) :
    k ∈ Set.range (blockEnum b c h) ↔ b k = c := by
  have h1 : Set.range (blockEnum b c h) = (block b c : Set (Fin r)) :=
    Finset.range_orderEmbOfFin (block b c) h
  rw [h1]
  simp [block]

/- English proof (translation)
Use `⟨?_, fun d h h' => ?_⟩` and prove the remaining obligations. Use `Finset.card_equiv w fun k => ?_` and prove the remaining obligations. Simplify using `[block, hw k i]`. Use `set e := blockEnum b (b i) h with he set e' := blockEnum b' (b' (w i)) h' with he'`. Establish `hr : ∀ k, k ∈ Set.range e ↔ w k ∈ Set.range e'` using `fun k => by`.

Rewrite using `[he, he', range_blockEnum, range_blockEnum, hw k i]`. Establish `hex : ∀ a, ∃ a', e' a' = w (e a)` using `fun a => (hr (e a)).1 ⟨a, rfl⟩`. Use `choose p hp using hex`. Establish `hinj : Function.Injective p` using `fun a a' haa => by`. Apply `e.injective` to reduce the goal to its premises.

Apply `w.injective` to reduce the goal to its premises. Rewrite using `[← hp, ← hp, haa]`. Set `π₀ : Equiv.Perm (Fin d)` to `Equiv.ofBijective p (Finite.injective_iff_bijective.1 hinj)`. Establish `hπ : ∀ a, e' (π₀ a) = w (e a)` using `hp`. Use `⟨permGL F π₀, fun g => ?_⟩` and prove the remaining obligations.

Use `eq_mul_inv_iff_mul_eq.1 ?_` and prove the remaining obligations. Use extensionality with `k l`. Take `⟨k, rfl⟩` from `w.surjective k`. Take `⟨l, rfl⟩` from `w.surjective l`. Rewrite using `[conj_permGL_apply]`.

Use `show extendMat e' ((permGL F π₀ * g * (permGL F π₀)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) (w k) (w l) = extendMat e (g : Matrix (Fin d) (Fin d) F) k l`. Distinguish the cases in `hkl : k ∈ Set.range e ∧ l ∈ Set.range e`. Take `⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩` from `hkl`. Rewrite using `[← hπ, ← hπ, extendMat_in, extendMat_in, conj_permGL_apply]`. Rewrite `hkl` using `[not_and_or]`.

Rewrite using `[extendMat_out _ _ _ _ hkl, extendMat_out _ _ _ _ (by rwa [← hr, ← hr])]`. Simplify using `[Matrix.one_apply]`.
-/
theorem blockHom_conj_permGL (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ) (w : Equiv.Perm (Fin r))
    (hw : ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j)) (i : Fin r) :
    (block b (b i)).card = (block b' (b' (w i))).card ∧
    ∀ (d : ℕ) (h : (block b (b i)).card = d) (h' : (block b' (b' (w i))).card = d),
      ∃ π : GL (Fin d) F, ∀ g : GL (Fin d) F,
        (blockHom F b' (b' (w i)) h' (π * g * π⁻¹) : GL (Fin r) F) * permGL F w =
          permGL F w * (blockHom F b (b i) h g : GL (Fin r) F) := by
  refine ⟨?_, fun d h h' => ?_⟩
  · refine Finset.card_equiv w fun k => ?_
    simp [block, hw k i]
  · set e := blockEnum b (b i) h with he
    set e' := blockEnum b' (b' (w i)) h' with he'
    have hr : ∀ k, k ∈ Set.range e ↔ w k ∈ Set.range e' := fun k => by
      rw [he, he', range_blockEnum, range_blockEnum, hw k i]
    have hex : ∀ a, ∃ a', e' a' = w (e a) := fun a => (hr (e a)).1 ⟨a, rfl⟩
    choose p hp using hex
    have hinj : Function.Injective p := fun a a' haa => by
      apply e.injective
      apply w.injective
      rw [← hp, ← hp, haa]
    let π₀ : Equiv.Perm (Fin d) := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hinj)
    have hπ : ∀ a, e' (π₀ a) = w (e a) := hp
    refine ⟨permGL F π₀, fun g => ?_⟩
    refine eq_mul_inv_iff_mul_eq.1 ?_
    ext k l
    obtain ⟨k, rfl⟩ := w.surjective k
    obtain ⟨l, rfl⟩ := w.surjective l
    rw [conj_permGL_apply]
    show extendMat e' ((permGL F π₀ * g * (permGL F π₀)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) (w k) (w l)
      = extendMat e (g : Matrix (Fin d) (Fin d) F) k l
    by_cases hkl : k ∈ Set.range e ∧ l ∈ Set.range e
    · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := hkl
      rw [← hπ, ← hπ, extendMat_in, extendMat_in, conj_permGL_apply]
    · rw [not_and_or] at hkl
      rw [extendMat_out _ _ _ _ hkl, extendMat_out _ _ _ _ (by rwa [← hr, ← hr])]
      simp [Matrix.one_apply]

end GlobalTheory.Proof.BlockConj

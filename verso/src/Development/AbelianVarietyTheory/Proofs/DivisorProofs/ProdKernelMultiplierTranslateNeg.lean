import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.KerPerm

/- English proof (translation)
Use `choose g hgT hg using hmap`. Establish `ginj : ∀ a (ha : a ∈ T) b (hb : b ∈ T), g a ha = g b hb → a = b`. Introduce `a ha b hb h`. Apply `hsep a ha b hb` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Use `Λ.sub_mem (hg a ha) (hg b hb)` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `using this`. Use `Finset.prod_bij g hgT ginj ?_ ?_` and prove the remaining obligations. Introduce `b hb`.

Take `⟨a, ha, h⟩` from `Finset.surj_on_of_inj_on_of_card_le g hgT (fun a b ha hb h => ginj a ha b hb h) le_rfl b hb`. Conclude with `⟨a, ha, h.symm⟩`. Introduce `a ha`. Use `hψ (g a ha) _ (hg a ha)` as an intermediate fact. Simplify using `using this`.
-/
theorem prod_eq_of_perm_mod (Λ : Submodule ℤ ℂ) (T : Finset ℂ) (f ψ : ℂ → ℂ)
    (hψ : ∀ z l, l ∈ Λ → ψ (z + l) = ψ z)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ Λ → a = b)
    (hmap : ∀ t ∈ T, ∃ u ∈ T, f t - u ∈ Λ)
    (hinj : ∀ a b, f a - f b ∈ Λ → a - b ∈ Λ) :
    ∏ t ∈ T, ψ (f t) = ∏ t ∈ T, ψ t := by
  classical
  choose g hgT hg using hmap
  have ginj : ∀ a (ha : a ∈ T) b (hb : b ∈ T), g a ha = g b hb → a = b := by
    intro a ha b hb h
    apply hsep a ha b hb
    apply hinj
    have := Λ.sub_mem (hg a ha) (hg b hb)
    rw [h] at this
    simpa using this
  refine Finset.prod_bij g hgT ginj ?_ ?_
  · intro b hb
    obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le g hgT
      (fun a b ha hb h => ginj a ha b hb h) le_rfl b hb
    exact ⟨a, ha, h.symm⟩
  · intro a ha
    have := hψ (g a ha) _ (hg a ha)
    simpa using this

/- English proof (translation)
Introduce `L α S φ ⟨h1, h2, h3⟩ _ hφ`. Establish `h0 : (0 : ℂ) ∉ S` using `fun h => (h1 0 h).2 L.lattice.zero_mem`. Establish `hψ : ∀ z : ℂ, ∀ x l, l ∈ L.lattice → φ (z + (x + l)) = φ (z + x)`. Introduce `z x l hl`. Rewrite using `[← add_assoc, hφ _ _ hl]`.

Use `⟨fun z s hs => ?_, fun z => ?_⟩` and prove the remaining obligations. Establish `key` using `prod_eq_of_perm_mod L.lattice (insert 0 S) (fun t => s + t) (fun x => φ (z + x)) (hψ z) (by`. Introduce `a ha b hb hab`. Apply the tactic sequence `rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb`. Both sides reduce to the same expression.

Conclude with `absurd (by simpa using hab) (h1 b hb).2`. Conclude with `absurd (by simpa using hab) (h1 a ha).2`. Conclude with `h2 a ha b hb hab)`. Use the proof step `(by`. Introduce `t ht`.

Establish `hk : α * (s + t) ∈ L.lattice`. Rewrite using `[mul_add]`. Use `L.lattice.add_mem hs ?_` and prove the remaining obligations. Break down `Finset.mem_insert.1 ht with rfl | ht` into its components or cases. Simplify using the standard rewrite rules.

Conclude with `(h1 t ht).1`. Distinguish the cases in `hm : s + t ∈ L.lattice`. Conclude with `⟨0, Finset.mem_insert_self _ _, by simpa using hm⟩`. Take `⟨P, hP, h⟩` from `h3 _ hk hm`. Conclude with `⟨P, Finset.mem_insert_of_mem hP, h⟩)`.

Use the proof step `(by`. Introduce `a b h`. Simplify using `using h)`. Rewrite `key` using `[Finset.prod_insert h0, Finset.prod_insert h0]`. Simplify `key` using `[add_assoc]`.

Establish `key` using `prod_eq_of_perm_mod L.lattice S (fun t => -t) (fun x => φ (z + x)) (hψ z) h2 (by`. Introduce `t ht`. Use `h3 (-t) ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_neg]`. Conclude with `L.lattice.neg_mem (h1 t ht).1`.

Introduce `h; exact (h1 t ht).2 (by simpa using h))`. Use the proof step `(by`. Introduce `a b h`. Use `L.lattice.neg_mem h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use the proof step `ring)`. Simplify `key` using `[sub_eq_add_neg]`.
-/
theorem prod_ker_translate_neg : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (φ : ℂ → ℂ), IsKerReps L α S → MulStable L α → (∀ z l, l ∈ L.lattice → φ (z + l) = φ z) → (∀ z s, α * s ∈ L.lattice → φ (z + s) * ∏ t ∈ S, φ (z + s + t) = φ z * ∏ t ∈ S, φ (z + t)) ∧ ∀ z, ∏ t ∈ S, φ (z - t) = ∏ t ∈ S, φ (z + t) := by
  classical
  intro L α S φ ⟨h1, h2, h3⟩ _ hφ
  have h0 : (0 : ℂ) ∉ S := fun h => (h1 0 h).2 L.lattice.zero_mem
  have hψ : ∀ z : ℂ, ∀ x l, l ∈ L.lattice → φ (z + (x + l)) = φ (z + x) := by
    intro z x l hl
    rw [← add_assoc, hφ _ _ hl]
  refine ⟨fun z s hs => ?_, fun z => ?_⟩
  · have key := prod_eq_of_perm_mod L.lattice (insert 0 S) (fun t => s + t) (fun x => φ (z + x)) (hψ z)
      (by
        intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
        · rfl
        · exact absurd (by simpa using hab) (h1 b hb).2
        · exact absurd (by simpa using hab) (h1 a ha).2
        · exact h2 a ha b hb hab)
      (by
        intro t ht
        have hk : α * (s + t) ∈ L.lattice := by
          rw [mul_add]
          refine L.lattice.add_mem hs ?_
          rcases Finset.mem_insert.1 ht with rfl | ht
          · simp
          · exact (h1 t ht).1
        by_cases hm : s + t ∈ L.lattice
        · exact ⟨0, Finset.mem_insert_self _ _, by simpa using hm⟩
        · obtain ⟨P, hP, h⟩ := h3 _ hk hm
          exact ⟨P, Finset.mem_insert_of_mem hP, h⟩)
      (by
        intro a b h
        simpa using h)
    rw [Finset.prod_insert h0, Finset.prod_insert h0] at key
    simpa [add_assoc] using key
  · have key := prod_eq_of_perm_mod L.lattice S (fun t => -t) (fun x => φ (z + x)) (hψ z) h2
      (by
        intro t ht
        refine h3 (-t) ?_ ?_
        · rw [mul_neg]; exact L.lattice.neg_mem (h1 t ht).1
        · intro h; exact (h1 t ht).2 (by simpa using h))
      (by
        intro a b h
        have := L.lattice.neg_mem h
        convert this using 1
        ring)
    simpa [sub_eq_add_neg] using key

end GlobalTheory.KerPerm

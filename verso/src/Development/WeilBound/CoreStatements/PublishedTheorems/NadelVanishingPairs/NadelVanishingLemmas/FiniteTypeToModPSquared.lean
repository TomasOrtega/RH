import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NumberFieldToModPSquared
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteTypeToNumberField
open scoped TensorProduct Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `A _ _ _ hA a ha n`. Take `⟨K, _, _, χ₀, hχ⟩` from `GlobalTheory.T.finite_type_to_number_field A hA a ha`. Take `⟨s, hs⟩` from `hA.out`. Take `⟨p, hp, hn, ⟨ψ⟩⟩` from `GlobalTheory.T.number_field_to_mod_p_squared K (insert (χ₀ a)⁻¹ (s.image χ₀)) n`. Use `set R := Subring.closure ((insert (χ₀ a)⁻¹ (s.image χ₀) : Finset K) : Set K) with hR`.

Establish `hmem : ∀ x : A, χ₀ x ∈ R`. Introduce `x`. Establish `hx : x ∈ Algebra.adjoin ℤ (s : Set A)` using `by rw [hs]; trivial`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem y hy`.

Apply `Subring.subset_closure` to reduce the goal to its premises. Simplify using `only [Finset.coe_insert, Finset.coe_image]`. Conclude with `Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩`. Consider the case `algebraMap r => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `R.add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `R.mul_mem hx hy`. Establish `hinv : (χ₀ a)⁻¹ ∈ R`. Apply `Subring.subset_closure` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Use `⟨p, hp, hn, ψ.comp (χ₀.codRestrict R hmem), ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply]`. Apply `IsUnit.map` to reduce the goal to its premises. Use `IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hχ]`.
-/
theorem exists_ringHom_zmod_prime_sq_isUnit_of_finiteType :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ χ : A →+* ZMod (p ^ 2), IsUnit (χ a) := by
  intro A _ _ _ hA a ha n
  classical
  obtain ⟨K, _, _, χ₀, hχ⟩ := GlobalTheory.T.finite_type_to_number_field A hA a ha
  obtain ⟨s, hs⟩ := hA.out
  obtain ⟨p, hp, hn, ⟨ψ⟩⟩ := GlobalTheory.T.number_field_to_mod_p_squared K (insert (χ₀ a)⁻¹ (s.image χ₀)) n
  set R := Subring.closure ((insert (χ₀ a)⁻¹ (s.image χ₀) : Finset K) : Set K) with hR
  have hmem : ∀ x : A, χ₀ x ∈ R := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      apply Subring.subset_closure
      simp only [Finset.coe_insert, Finset.coe_image]
      exact Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add]; exact R.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact R.mul_mem hx hy
  have hinv : (χ₀ a)⁻¹ ∈ R := by
    apply Subring.subset_closure
    simp
  refine ⟨p, hp, hn, ψ.comp (χ₀.codRestrict R hmem), ?_⟩
  rw [RingHom.comp_apply]
  apply IsUnit.map
  refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_
  apply Subtype.ext
  simp [hχ]

end GlobalTheory

import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denint

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

/- English proof (translation)
Rewrite using `[primorial, ← Finset.prod_Ico_id_eq_factorial]`. Apply `Finset.prod_dvd_prod_of_subset` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_range] at hp`. Simplify using `only [Finset.mem_Ico]`.

Conclude with `⟨hp.2.one_lt.le, hp.1⟩`.
-/
private theorem primorial_dvd_fact (n : ℕ) : primorial n ∣ n.factorial := by
  rw [primorial, ← Finset.prod_Ico_id_eq_factorial]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  simp only [Finset.mem_Ico]
  exact ⟨hp.2.one_lt.le, hp.1⟩

/- English proof (translation)
Take `⟨z, hz⟩` from `b_denint N k b.val hN`. Take `⟨c, hc⟩` from `primorial_dvd_fact (k + 1)`. Use `⟨c * z, ?_⟩` and prove the remaining obligations. Establish `hk0 : (k : ℚ) ≠ 0` using `by exact_mod_cast (show k ≠ 0 by omega)`. Simplify using `only [denY, Ek, den] at hz ⊢`.

Move the coercions through the operations in `[hc] at hz ⊢`. Rewrite using `[← hz]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem denY_Ek (N k : ℕ) (hN : 0 < N) (hk : 1 ≤ k) (b : ZMod N) :
    ∃ z : ℤ, (z : ℚ) = (denY N k : ℚ) * Ek N k b := by
  obtain ⟨z, hz⟩ := b_denint N k b.val hN
  obtain ⟨c, hc⟩ := primorial_dvd_fact (k + 1)
  refine ⟨c * z, ?_⟩
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  simp only [denY, Ek, den] at hz ⊢
  push_cast [hc] at hz ⊢
  rw [← hz]
  field_simp

/- English proof (translation)
Introduce `N _ Γ _ π a ha k hk`. Establish `hN : 0 < N` using `Nat.pos_of_ne_zero (NeZero.ne N)`. Use `choose w hw using fun b : ZMod N => denY_Ek N k hN hk b`. Use `⟨(1 - MonoidAlgebra.single (π (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℤ) ^ k)) * -∑ b : (ZMod N)ˣ, MonoidAlgebra.single (π b)⁻¹ (w b), ?_⟩` and prove the remaining obligations. Simplify using `only [yEl, thetaEl, sumEl, map_mul, map_sub, map_one, map_neg, map_sum, coefMap_single, hw]`.

Use `push_cast`. Rewrite using `[← mul_smul_comm, smul_neg, Finset.smul_sum]`. Simplify using `only [MonoidAlgebra.smul_single']`.
-/
theorem UpperTheory.V.B5.exists_int_higherStickelbergerDenom_smul :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 1 ≤ k → ∃ z : MonoidAlgebra ℤ Γ, coefMap ℚ Γ z = (denY N k : ℚ) • yEl k a ha π := by
  intro N _ Γ _ π a ha k hk
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  choose w hw using fun b : ZMod N => denY_Ek N k hN hk b
  refine ⟨(1 - MonoidAlgebra.single (π (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℤ) ^ k)) *
    -∑ b : (ZMod N)ˣ, MonoidAlgebra.single (π b)⁻¹ (w b), ?_⟩
  simp only [yEl, thetaEl, sumEl, map_mul, map_sub, map_one, map_neg, map_sum, coefMap_single, hw]
  push_cast
  rw [← mul_smul_comm, smul_neg, Finset.smul_sum]
  simp only [MonoidAlgebra.smul_single']

import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `ι Z H _ _ _ i q n hn hi hq hk`. Use `Fintype.ofFinite ι` as an intermediate fact. Set `i' : Z →ₗ[ℤ] (ι →₀ ℤ)` to `i.toIntLinearMap`. Establish `hi' : Function.Injective i'` using `hi`. Establish `: Module.Finite ℤ Z` using `Module.Finite.of_injective i' hi'`.

Establish `: Module.Free ℤ Z` using `Module.Free.of_equiv (LinearEquiv.ofInjective i' hi').symm`. Establish `hr : Module.finrank ℤ Z ≤ Nat.card ι`. Establish `h` using `LinearMap.finrank_le_finrank_of_injective hi'`. Rewrite `h` using `[Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]`. Then use the resulting hypothesis. Set `b` to `Module.finBasis ℤ Z`.

Set `f : (Fin (Module.finrank ℤ Z) → Fin n) → H` to `fun c => ∑ k, (((c k : ℕ) : ℤ)) • q (b k)`. Establish `hn0 : (0 : ℤ) < n` using `by exact_mod_cast hn`. Establish `hf : Function.Surjective f`. Introduce `h`. Take `⟨z, rfl⟩` from `hq h`.

Use `⟨fun k => ⟨(b.repr z k % n).toNat, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `Int.emod_nonneg (b.repr z k) hn0.ne'`. Establish `h2` using `Int.emod_lt_of_pos (b.repr z k) hn0`. Use linear arithmetic over natural numbers and integers. Use `conv_rhs => rw [← b.sum_repr z, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h1` using `Int.emod_nonneg (b.repr z k) hn0.ne'`. Rewrite using `[map_zsmul]`. Simplify using `only [Int.toNat_of_nonneg h1]`. Establish `h3 : (n : ℤ) • q (b k) = 0` using `by rw [natCast_zsmul]; exact hk _`.

Use `conv_rhs => rw [← Int.emod_add_ediv_mul (b.repr z k) n, add_smul, mul_smul, h3, smul_zero, add_zero]`. Use `⟨Finite.of_surjective f hf, (Nat.card_le_card_of_surjective f hf).trans ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_fun, Nat.card_fin, Nat.card_fin]`. Conclude with `Nat.pow_le_pow_right hn hr`.
-/
theorem UpperTheory.V.KH.subquot :
    ∀ (ι Z H : Type) [Finite ι] [AddCommGroup Z] [AddCommGroup H] (i : Z →+ (ι →₀ ℤ)) (q : Z →+ H)
      (n : ℕ), 1 ≤ n → Function.Injective i → Function.Surjective q → (∀ h : H, n • h = 0) →
      CardLe H (n ^ Nat.card ι) := by
  intro ι Z H _ _ _ i q n hn hi hq hk
  classical
  have := Fintype.ofFinite ι
  let i' : Z →ₗ[ℤ] (ι →₀ ℤ) := i.toIntLinearMap
  have hi' : Function.Injective i' := hi
  have : Module.Finite ℤ Z := Module.Finite.of_injective i' hi'
  have : Module.Free ℤ Z :=
    Module.Free.of_equiv (LinearEquiv.ofInjective i' hi').symm
  have hr : Module.finrank ℤ Z ≤ Nat.card ι := by
    have h := LinearMap.finrank_le_finrank_of_injective hi'
    rwa [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card] at h
  let b := Module.finBasis ℤ Z
  let f : (Fin (Module.finrank ℤ Z) → Fin n) → H := fun c => ∑ k, (((c k : ℕ) : ℤ)) • q (b k)
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨z, rfl⟩ := hq h
    refine ⟨fun k => ⟨(b.repr z k % n).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_nonneg (b.repr z k) hn0.ne'
      have h2 := Int.emod_lt_of_pos (b.repr z k) hn0
      omega
    · conv_rhs => rw [← b.sum_repr z, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 := Int.emod_nonneg (b.repr z k) hn0.ne'
      rw [map_zsmul]
      simp only [Int.toNat_of_nonneg h1]
      have h3 : (n : ℤ) • q (b k) = 0 := by rw [natCast_zsmul]; exact hk _
      conv_rhs => rw [← Int.emod_add_ediv_mul (b.repr z k) n, add_smul, mul_smul, h3, smul_zero,
        add_zero]
  refine ⟨Finite.of_surjective f hf, (Nat.card_le_card_of_surjective f hf).trans ?_⟩
  rw [Nat.card_fun, Nat.card_fin, Nat.card_fin]
  exact Nat.pow_le_pow_right hn hr

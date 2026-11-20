import Mathlib

namespace GlobalTheory

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ X`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hex : ∃ i, ¬ (k : ℤ) ∣ b.repr d i`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hne (∑ i, (b.repr d i / k) • b i)` to reduce the goal to its premises. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `j`. Rewrite using `[← natCast_zsmul]`.

Simplify using `[map_sum, Finsupp.single_apply, Int.mul_ediv_cancel' (h j)]`. Take `⟨i, hi⟩` from `hex`. Establish `hk0 : k ≠ 0` using `by rintro rfl; exact hk (by simp)`. Use `haveI : NeZero (k : F) := ⟨hk⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot F k`.

Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero hk0`. Set `u : Fˣ` to `Units.mk0 ζ hζ0`. Establish `hu : IsPrimitiveRoot u k` using `IsPrimitiveRoot.coe_units_iff.mp (by simpa [u] using hζ)`. Set `τ : Multiplicative X →* Fˣ` to `(zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)`. Establish `hτ : ∀ x : X, τ (Multiplicative.ofAdd x) = u ^ (b.repr x i)`.

Introduce `x`. Simplify using `[τ]`. Establish `hτk : τ ^ k = 1`. Use extensionality with `x`. Use `show (τ x ^ k : Fˣ).val = (1 : Fˣ).val`.

Use `congr 1`. Rewrite using `[← ofAdd_toAdd x, hτ, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu.pow_eq_one, one_zpow]`. Establish `h1` using `hd τ hτk`. Rewrite `h1` using `[hτ]`. Conclude with `hi ((hu.zpow_eq_one_iff_dvd _).1 h1)`.
-/
theorem mem_smul_of_forall_char_pow_eq_one
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F]
    [IsAlgClosed F] (k : ℕ) (hk : (k : F) ≠ 0) (d : X)
    (hd : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd d) = 1) :
    ∃ z : X, d = k • z := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  by_contra hne
  push_neg at hne
  have hex : ∃ i, ¬ (k : ℤ) ∣ b.repr d i := by
    by_contra h
    push_neg at h
    apply hne (∑ i, (b.repr d i / k) • b i)
    apply b.repr.injective
    ext j
    rw [← natCast_zsmul]
    simp [map_sum, Finsupp.single_apply, Int.mul_ediv_cancel' (h j)]
  obtain ⟨i, hi⟩ := hex
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (by simp)
  haveI : NeZero (k : F) := ⟨hk⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hk0
  let u : Fˣ := Units.mk0 ζ hζ0
  have hu : IsPrimitiveRoot u k := IsPrimitiveRoot.coe_units_iff.mp (by simpa [u] using hζ)
  let τ : Multiplicative X →* Fˣ :=
    (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
  have hτ : ∀ x : X, τ (Multiplicative.ofAdd x) = u ^ (b.repr x i) := by
    intro x; simp [τ]
  have hτk : τ ^ k = 1 := by
    ext x
    show (τ x ^ k : Fˣ).val = (1 : Fˣ).val
    congr 1
    rw [← ofAdd_toAdd x, hτ, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hu.pow_eq_one, one_zpow]
  have h1 := hd τ hτk
  rw [hτ] at h1
  exact hi ((hu.zpow_eq_one_iff_dvd _).1 h1)

end GlobalTheory

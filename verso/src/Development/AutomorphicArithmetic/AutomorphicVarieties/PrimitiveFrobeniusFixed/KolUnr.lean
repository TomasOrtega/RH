import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Rewrite `h` using `[map_pow]`. Break down `lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1` into its components or cases. Conclude with `absurd h (pow_lt_one₀ zero_le h1 hM).ne`. Conclude with `h1`. Conclude with `absurd h (one_lt_pow₀ h1 hM).ne'`.
-/
private theorem val_eq_one_of_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {M : ℕ} (hM : M ≠ 0) {x : Ω}
    (h : A.valuation (x ^ M) = 1) : A.valuation x = 1 := by
  rw [map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le h1 hM).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hM).ne'

/- English proof (translation)
Introduce `Ω _ _ _ M F n r a _ hFn hMF ζ hζ δ hδ y hy hfix hunit κ hκ A hA g hg`. Take `⟨-, -, hmul, -, hine, hroot, -, -, -, hconj⟩` from `placeBasic Ω`. Establish `hM : M ≠ 0` using `NeZero.ne M`. Establish `hA1 : ¬ Over A (F * n)` using `fun h => hA <| by`. Rewrite using `[mul_right_comm]`.

Conclude with `(hmul A _ _).2 (Or.inl h)`. Establish `hAr : ¬ Over A r` using `fun h => hA <| (hmul A _ _).2 (Or.inl ((hmul A _ _).2 (Or.inr h)))`. Establish `hAF : ¬ Over A F` using `fun h => hA1 ((hmul A _ _).2 (Or.inl h))`. Establish `hAM : ¬ Over A M` using `fun h => hAF <| by`. Take `⟨c, rfl⟩` from `hMF`.

Conclude with `(hmul A _ _).2 (Or.inl h)`. Establish `hgFn : g ∈ fixMu ℚ Ω (F * n)` using `hine A _ hA1 hg`. Establish `hgF : g ∈ fixMu ℚ Ω F` using `hine A _ hAF hg`. Take `⟨Y, hY, -⟩` from `id hκ`. Establish `key` using `(kolHom Ω M F n a hFn hMF ζ hζ δ hδ y hy hfix κ hκ).2.2 Y hY g hgF 1 (by rw [hfix g hgFn, one_pow, div_self hy])`.

Establish `h1 : opP δ a (1 : Ω) = 1` using `by simp [opP]`. Rewrite `key` using `[h1, div_one]`. Establish `hvY : A.valuation Y = 1` using `val_eq_one_of_pow A hM (by rw [hY]; exact hunit A hAr)`. Establish `hvδ : A.valuation (δ Y) = 1`. Use `val_eq_one_of_pow A hM ?_` and prove the remaining obligations.

Rewrite using `[← map_pow δ, hY]`. Establish `hB : ¬ Over (δ⁻¹ • A) r` using `fun h => hAr <| by`. Use `((hconj A δ⁻¹).2.2.2.1 (r : Ω)).1 (by rw [map_natCast]; exact h)` as an intermediate fact. Conclude with `this`. Use `((hconj (δ⁻¹ • A) δ).2.2.2.2 y).2 (hunit _ hB)` as an intermediate fact.

Rewrite `this` using `[smul_inv_smul]`. Then use the resulting hypothesis. Establish `hu : A.valuation (opP δ a Y) = 1`. Rewrite using `[opP, map_div₀, map_pow, hvY, hvδ, one_pow, div_one]`. Establish `hu0 : opP δ a Y ≠ 0` using `fun h => by`. Rewrite `hu` using `[h, map_zero]`.

Conclude with `zero_ne_one hu`. Establish `hlt : A.valuation (ζ ^ (κ g).val - 1) < 1`. Establish `e : ζ ^ (κ g).val - 1 = (g (opP δ a Y) - opP δ a Y) / opP δ a Y`. Rewrite using `[key, sub_div, div_self hu0]`. Rewrite using `[e, map_div₀, hu, div_one]`.

Conclude with `hg.2 _ hu.le`. Establish `h2 : ζ ^ (κ g).val = 1` using `hroot A M _ hAM (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) hlt`. Establish `h3 : M ∣ (κ g).val` using `(hζ.pow_eq_one_iff_dvd _).1 h2`. Conclude with `(ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt _))`.
-/
theorem UpperTheory.V.ML.kolUnr :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n r a : ℕ) [NeZero M], F * n ≠ 0 → M ∣ F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation y = 1) → ∀ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ →
    ∀ A : ValuationSubring Ω, ¬ Over A (F * r * n) → ∀ g ∈ Ine (F := ℚ) A, κ g = 0 := by
  intro Ω _ _ _ M F n r a _ hFn hMF ζ hζ δ hδ y hy hfix hunit κ hκ A hA g hg
  obtain ⟨-, -, hmul, -, hine, hroot, -, -, -, hconj⟩ := placeBasic Ω
  have hM : M ≠ 0 := NeZero.ne M
  have hA1 : ¬ Over A (F * n) := fun h => hA <| by
    rw [mul_right_comm]
    exact (hmul A _ _).2 (Or.inl h)
  have hAr : ¬ Over A r := fun h => hA <| (hmul A _ _).2 (Or.inl ((hmul A _ _).2 (Or.inr h)))
  have hAF : ¬ Over A F := fun h => hA1 ((hmul A _ _).2 (Or.inl h))
  have hAM : ¬ Over A M := fun h => hAF <| by
    obtain ⟨c, rfl⟩ := hMF
    exact (hmul A _ _).2 (Or.inl h)
  have hgFn : g ∈ fixMu ℚ Ω (F * n) := hine A _ hA1 hg
  have hgF : g ∈ fixMu ℚ Ω F := hine A _ hAF hg
  obtain ⟨Y, hY, -⟩ := id hκ
  have key := (kolHom Ω M F n a hFn hMF ζ hζ δ hδ y hy hfix κ hκ).2.2 Y hY g hgF 1
    (by rw [hfix g hgFn, one_pow, div_self hy])
  have h1 : opP δ a (1 : Ω) = 1 := by simp [opP]
  rw [h1, div_one] at key
  have hvY : A.valuation Y = 1 := val_eq_one_of_pow A hM (by rw [hY]; exact hunit A hAr)
  have hvδ : A.valuation (δ Y) = 1 := by
    refine val_eq_one_of_pow A hM ?_
    rw [← map_pow δ, hY]
    have hB : ¬ Over (δ⁻¹ • A) r := fun h => hAr <| by
      have := ((hconj A δ⁻¹).2.2.2.1 (r : Ω)).1 (by rw [map_natCast]; exact h)
      exact this
    have := ((hconj (δ⁻¹ • A) δ).2.2.2.2 y).2 (hunit _ hB)
    rwa [smul_inv_smul] at this
  have hu : A.valuation (opP δ a Y) = 1 := by
    rw [opP, map_div₀, map_pow, hvY, hvδ, one_pow, div_one]
  have hu0 : opP δ a Y ≠ 0 := fun h => by
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hlt : A.valuation (ζ ^ (κ g).val - 1) < 1 := by
    have e : ζ ^ (κ g).val - 1 = (g (opP δ a Y) - opP δ a Y) / opP δ a Y := by
      rw [key, sub_div, div_self hu0]
    rw [e, map_div₀, hu, div_one]
    exact hg.2 _ hu.le
  have h2 : ζ ^ (κ g).val = 1 := hroot A M _ hAM (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) hlt
  have h3 : M ∣ (κ g).val := (hζ.pow_eq_one_iff_dvd _).1 h2
  exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt _))

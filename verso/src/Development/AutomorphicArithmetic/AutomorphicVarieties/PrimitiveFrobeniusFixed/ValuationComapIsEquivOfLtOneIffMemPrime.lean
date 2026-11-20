import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Establish `h : IsIntegral A b` using `hb.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Rewrite using `[A.valuation_le_one_iff, ← hy]`. Conclude with `y.2`.
-/
private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

/- English proof (translation)
Introduce `K Ω _ _ _ ι A w h`. Establish `hle : ∀ y : 𝓞 K, A.valuation (ι (y : K)) ≤ 1` using `fun y => int_le A (y.isIntegral_coe.map ι.toIntAlgHom)`. Establish `key : ∀ x : K, w.valuation K x ≤ 1 → ∃ a s : 𝓞 K, s ∉ w.asIdeal ∧ x * (s : K) = (a : K) ∧ A.valuation (ι x) = A.valuation (ι (a : K))`. Introduce `x hx`. Take `⟨a, s, hs⟩` from `w.exists_primeCompl_mul_eq_of_integer x hx`.

Establish `hs' : (s : 𝓞 K) ∉ w.asIdeal` using `s.2`. Establish `hs2 : x * ((s : 𝓞 K) : K) = (a : K)` using `hs`. Use `⟨a, s, hs', hs2, ?_⟩` and prove the remaining obligations. Establish `h1 : A.valuation (ι ((s : 𝓞 K) : K)) = 1` using `le_antisymm (hle _) (not_lt.1 fun hh => hs' ((h _).1 hh))`. Rewrite using `[← hs2, map_mul, map_mul, h1, mul_one]`.

Rewrite using `[Valuation.isEquiv_iff_val_le_one]`. Introduce `x`. Rewrite using `[Valuation.comap_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Assume the negation of the conclusion as `hw`. Establish `hw' : 1 < w.valuation K x` using `not_le.1 hw`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hw'`.

Establish `hinv : w.valuation K x⁻¹ < 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_lt_one_of_one_lt₀ hw'`. Take `⟨a, s, -, hs2, he⟩` from `key x⁻¹ hinv.le`. Establish `ha : w.valuation K (a : K) < 1`.

Rewrite using `[← hs2, map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le hinv (w.valuation_le_one s)`. Establish `ha' : a ∈ w.asIdeal` using `(w.valuation_lt_one_iff_mem a).1 ha`. Establish `h2 : A.valuation (ι x⁻¹) < 1` using `he ▸ (h a).2 ha'`. Establish `h3` using `mul_lt_one_of_nonneg_of_lt_one_left zero_le h2 hx`.

Rewrite `h3` using `[← map_mul, ← map_mul, inv_mul_cancel₀ hx0, map_one, map_one]`. Conclude with `lt_irrefl _ h3`. Introduce `hx`. Take `⟨a, s, -, -, he⟩` from `key x hx`. Rewrite using `[he]`.

Conclude with `hle a`.
-/
theorem UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] (ι : K →+* Ω) (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), (∀ y : 𝓞 K, A.valuation (ι (y : K)) < 1 ↔ y ∈ w.asIdeal) → (A.valuation.comap ι).IsEquiv (w.valuation K) := by
  intro K Ω _ _ _ ι A w h
  have hle : ∀ y : 𝓞 K, A.valuation (ι (y : K)) ≤ 1 := fun y =>
    int_le A (y.isIntegral_coe.map ι.toIntAlgHom)
  have key : ∀ x : K, w.valuation K x ≤ 1 → ∃ a s : 𝓞 K, s ∉ w.asIdeal ∧ x * (s : K) = (a : K) ∧
      A.valuation (ι x) = A.valuation (ι (a : K)) := by
    intro x hx
    obtain ⟨a, s, hs⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    have hs' : (s : 𝓞 K) ∉ w.asIdeal := s.2
    have hs2 : x * ((s : 𝓞 K) : K) = (a : K) := hs
    refine ⟨a, s, hs', hs2, ?_⟩
    have h1 : A.valuation (ι ((s : 𝓞 K) : K)) = 1 :=
      le_antisymm (hle _) (not_lt.1 fun hh => hs' ((h _).1 hh))
    rw [← hs2, map_mul, map_mul, h1, mul_one]
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [Valuation.comap_apply]
  constructor
  · intro hx
    by_contra hw
    have hw' : 1 < w.valuation K x := not_le.1 hw
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hw'
    have hinv : w.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hw'
    obtain ⟨a, s, -, hs2, he⟩ := key x⁻¹ hinv.le
    have ha : w.valuation K (a : K) < 1 := by
      rw [← hs2, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hinv (w.valuation_le_one s)
    have ha' : a ∈ w.asIdeal := (w.valuation_lt_one_iff_mem a).1 ha
    have h2 : A.valuation (ι x⁻¹) < 1 := he ▸ (h a).2 ha'
    have h3 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h2 hx
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hx0, map_one, map_one] at h3
    exact lt_irrefl _ h3
  · intro hx
    obtain ⟨a, s, -, -, he⟩ := key x hx
    rw [he]
    exact hle a

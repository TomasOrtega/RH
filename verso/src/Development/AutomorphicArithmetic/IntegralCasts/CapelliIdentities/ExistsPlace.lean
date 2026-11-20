import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.ExistsPlace.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

/- English proof (translation)
Introduce `E _ _ _ q hq`. Establish `hne : (q : NumberField.RingOfIntegers E) ≠ 0`. Conclude with `hq.ne_zero` after adjusting the coercions. Establish `hnu : ¬ IsUnit (q : NumberField.RingOfIntegers E)`. Introduce `h`.

Establish `h1` using `h.map (Algebra.norm ℤ (S := NumberField.RingOfIntegers E))`. Establish `h2 : Algebra.norm ℤ (q : NumberField.RingOfIntegers E) = (q : ℤ) ^ Module.finrank ℤ (NumberField.RingOfIntegers E)`. Use `Algebra.norm_algebraMap (R := ℤ) (S := NumberField.RingOfIntegers E) (q : ℤ)` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[h2]`.

Establish `hpos : Module.finrank ℤ (NumberField.RingOfIntegers E) ≠ 0` using `Module.finrank_pos.ne'`. Establish `h3 : IsUnit (q : ℤ)` using `(isUnit_pow_iff hpos).1 h1`. Conclude with `hq.not_isUnit (Int.ofNat_isUnit.1 h3)`. Take `⟨M, hM, hqM⟩` from `exists_max_ideal_of_mem_nonunits hnu`. Use `⟨⟨M, hM.isPrime, ?_⟩, hqM⟩` and prove the remaining obligations.

Introduce `h`. Rewrite `hqM` using `[h]`. Conclude with `hne (by simpa using hqM)`.
-/
theorem UpperTheory.Reformulated.B.ExistsPlace.exists_place :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] (q : ℕ),
      Nat.Prime q → ∃ (w : UpperTheory.Reformulated.B.ExistsPlace.Plc E), (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ _ q hq
  have hne : (q : NumberField.RingOfIntegers E) ≠ 0 := by
    exact_mod_cast hq.ne_zero
  have hnu : ¬ IsUnit (q : NumberField.RingOfIntegers E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ (S := NumberField.RingOfIntegers E))
    have h2 : Algebra.norm ℤ (q : NumberField.RingOfIntegers E) =
        (q : ℤ) ^ Module.finrank ℤ (NumberField.RingOfIntegers E) := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := NumberField.RingOfIntegers E) (q : ℤ)
      simpa using this
    rw [h2] at h1
    have hpos : Module.finrank ℤ (NumberField.RingOfIntegers E) ≠ 0 := Module.finrank_pos.ne'
    have h3 : IsUnit (q : ℤ) := (isUnit_pow_iff hpos).1 h1
    exact hq.not_isUnit (Int.ofNat_isUnit.1 h3)
  obtain ⟨M, hM, hqM⟩ := exists_max_ideal_of_mem_nonunits hnu
  refine ⟨⟨M, hM.isPrime, ?_⟩, hqM⟩
  intro h
  rw [h] at hqM
  exact hne (by simpa using hqM)

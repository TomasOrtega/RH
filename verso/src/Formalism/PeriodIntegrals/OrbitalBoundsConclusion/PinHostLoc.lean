import Mathlib
import Formalism.PeriodIntegrals.PinHostLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalResidueCharacter.ResCharEq

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig p A g hg hne i hin hnot`. Establish `hres` using `PI.PinHostLoc.UnitaryGroupMassFormula.resChar_eq p (hg i) hin`. Establish `hi0 : ((g i : ℕ) : F) ≠ 0` using `Nat.cast_ne_zero.mpr (hg i).ne_zero`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hres]`.

Conclude with `PI.PinHostLoc.UnitaryGroupMassFormula.irr A (hg i).ne_zero hin hnot`. Choose the witnesses or unpack the hypotheses as in `⟨j, hgij, hj⟩ : ∃ j : Fin 2, g i ≠ g j ∧ ((g 0 : ℕ) : F) * ((g 1 : ℕ) : F) / ((g i : ℕ) : F) = ((g j : ℕ) : F) := by`. Apply the tactic sequence `rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl`. Conclude with `⟨1, hne, mul_div_cancel_left₀ _ hi0⟩`. Conclude with `⟨0, hne.symm, mul_div_cancel_right₀ _ hi0⟩`.

Establish `hjp : ((g j : ℕ) : NumberField.RingOfIntegers F) ∉ p.asIdeal`. Introduce `hjin`. Establish `hcop : IsCoprime ((g i : ℕ) : ℤ) ((g j : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hg i) (hg j)).mpr hgij)`. Take `⟨a, b, hab⟩` from `hcop`. Establish `h1 : (1 : NumberField.RingOfIntegers F) ∈ p.asIdeal`.

Establish `h2` using `congrArg (Int.cast : ℤ → NumberField.RingOfIntegers F) hab`. Move the coercions through the operations in `at h2`. Rewrite using `[← h2]`. Conclude with `p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hin) (p.asIdeal.mul_mem_left _ hjin)`. Conclude with `p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)`.

Take `⟨u, hu, hu'⟩` from `PI.PinHostLoc.UnitaryGroupMassFormula.unit A hjp`. Conclude with `⟨u, hu, by rw [hu', hj]⟩`.
-/
theorem prime_quotient_unit : PI.PinHostLoc.Target := by
  intro F E _ _ _ _ _ sig p A g hg hne i hin hnot
  have hres := PI.PinHostLoc.UnitaryGroupMassFormula.resChar_eq p (hg i) hin
  have hi0 : ((g i : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (hg i).ne_zero
  refine ⟨?_, ?_⟩
  · rw [hres]
    exact PI.PinHostLoc.UnitaryGroupMassFormula.irr A (hg i).ne_zero hin hnot
  · obtain ⟨j, hgij, hj⟩ : ∃ j : Fin 2, g i ≠ g j ∧
        ((g 0 : ℕ) : F) * ((g 1 : ℕ) : F) / ((g i : ℕ) : F) = ((g j : ℕ) : F) := by
      rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
      · exact ⟨1, hne, mul_div_cancel_left₀ _ hi0⟩
      · exact ⟨0, hne.symm, mul_div_cancel_right₀ _ hi0⟩
    have hjp : ((g j : ℕ) : NumberField.RingOfIntegers F) ∉ p.asIdeal := by
      intro hjin
      have hcop : IsCoprime ((g i : ℕ) : ℤ) ((g j : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hg i) (hg j)).mpr hgij)
      obtain ⟨a, b, hab⟩ := hcop
      have h1 : (1 : NumberField.RingOfIntegers F) ∈ p.asIdeal := by
        have h2 := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers F) hab
        push_cast at h2
        rw [← h2]
        exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hin) (p.asIdeal.mul_mem_left _ hjin)
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨u, hu, hu'⟩ := PI.PinHostLoc.UnitaryGroupMassFormula.unit A hjp
    exact ⟨u, hu, by rw [hu', hj]⟩

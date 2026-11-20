import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

noncomputable section
open IsLocalRing

namespace GlobalTheory.TChart

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : GlobalTheory.LocM.InvFun ℤ}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem Taut.s_ne_zero (C : Taut ζ g n φ) (k : Fin C.m ⊕ Fin C.N) : C.s k ≠ 0 := by
  intro h
  have hflat : C.ψ.Flat := C.compl.2.2.1
  algebraize [C.ψ]

  have hreg : IsSMulRegular C.R
      (algebraMap (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R (MvPolynomial.X k)) :=
    IsSMulRegular.of_flat (MvPolynomial.isRegular_X (n := k) (R := C.W)).left.isSMulRegular
  have h0 : algebraMap (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R (MvPolynomial.X k) = 0 := h
  rw [h0] at hreg
  exact one_ne_zero (hreg (a₁ := (1 : C.R)) (a₂ := 0) (by simp))

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem Taut.t_mem_ne_zero (C : Taut ζ g n φ) (k : Fin C.m) : C.t k ∈ maximalIdeal C.R ∧ C.t k ≠ 0 :=
  ⟨C.bd k, C.s_ne_zero (.inl k)⟩

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem Taut.comap_maximalIdeal (C : Taut ζ g n φ) : (maximalIdeal C.R).comap C.iw = maximalIdeal C.W := by
  have := C.ψ_loc
  exact IsLocalRing.maximalIdeal_comap (C.ψ.comp MvPolynomial.C)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem isComplAt_intCast_rat : IsComplAt (Int.castRingHom ℚ) := by

  have hm : maximalIdeal ℚ = ⊥ := IsLocalRing.maximalIdeal_eq_bot
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [hm]; infer_instance
  ·
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat _ (nonZeroDivisors ℤ)
  · rw [hm]; exact le_antisymm Ideal.map_comap_le bot_le
  ·
    intro r
    refine ⟨r.num, r.den, ?_, ?_⟩
    · simp [isUnit_iff_ne_zero, r.den_nz]
    · rw [hm, Ideal.mem_bot, sub_eq_zero]
      simp [Rat.mul_den_eq_num]

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem not_isComplAt_powerSeries_C : ¬ IsComplAt (PowerSeries.C (R := ℚ)) := by
  rintro ⟨-, -, -, h, -⟩

  have hc : (maximalIdeal (PowerSeries ℚ)).comap (PowerSeries.C (R := ℚ)) = ⊥ := by
    rcases Ideal.eq_bot_or_top ((maximalIdeal (PowerSeries ℚ)).comap (PowerSeries.C (R := ℚ))) with h' | h'
    · exact h'
    · exact absurd h' (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
  rw [hc, Ideal.map_bot] at h

  have hX : (PowerSeries.X : PowerSeries ℚ) ∈ maximalIdeal (PowerSeries ℚ) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  rw [← h, Ideal.mem_bot] at hX
  exact PowerSeries.X_ne_zero hX

end GlobalTheory.TChart

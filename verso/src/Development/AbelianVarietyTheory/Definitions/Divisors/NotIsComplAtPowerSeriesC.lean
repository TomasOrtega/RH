import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

noncomputable section
open IsLocalRing

namespace GlobalTheory.TChart

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : GlobalTheory.LocM.InvFun ℤ}

/- English proof (translation)
Introduce `h`. Establish `hflat : C.ψ.Flat` using `C.compl.2.2.1`. Use `algebraize [C.ψ]`. Establish `hreg : IsSMulRegular C.R (algebraMap (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R (MvPolynomial.X k))` using `IsSMulRegular.of_flat (MvPolynomial.isRegular_X (n := k) (R := C.W)).left.isSMulRegular`. Establish `h0 : algebraMap (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R (MvPolynomial.X k) = 0` using `h`.

Rewrite `hreg` using `[h0]`. Conclude with `one_ne_zero (hreg (a₁ := (1 : C.R)) (a₂ := 0) (by simp))`.
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
Assemble the required witnesses or components as `⟨C.bd k, C.s_ne_zero (.inl k)⟩`.
-/
theorem Taut.t_mem_ne_zero (C : Taut ζ g n φ) (k : Fin C.m) : C.t k ∈ maximalIdeal C.R ∧ C.t k ≠ 0 :=
  ⟨C.bd k, C.s_ne_zero (.inl k)⟩

/- English proof (translation)
Use `C.ψ_loc` as an intermediate fact. Conclude with `IsLocalRing.maximalIdeal_comap (C.ψ.comp MvPolynomial.C)`.
-/
theorem Taut.comap_maximalIdeal (C : Taut ζ g n φ) : (maximalIdeal C.R).comap C.iw = maximalIdeal C.W := by
  have := C.ψ_loc
  exact IsLocalRing.maximalIdeal_comap (C.ψ.comp MvPolynomial.C)

/- English proof (translation)
Establish `hm : maximalIdeal ℚ = ⊥` using `IsLocalRing.maximalIdeal_eq_bot`. Use `⟨inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`. Use `infer_instance`. Rewrite using `[show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, RingHom.flat_algebraMap_iff]`.

Conclude with `IsLocalization.flat _ (nonZeroDivisors ℤ)`. Rewrite using `[hm]`. Conclude with `le_antisymm Ideal.map_comap_le bot_le`. Introduce `r`. Use `⟨r.num, r.den, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[isUnit_iff_ne_zero, r.den_nz]`. Rewrite using `[hm, Ideal.mem_bot, sub_eq_zero]`. Simplify using `[Rat.mul_den_eq_num]`.
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
Introduce and unpack `⟨-, -, -, h, -⟩`. Establish `hc : (maximalIdeal (PowerSeries ℚ)).comap (PowerSeries.C (R` using `ℚ)) = ⊥ := by`. Break down `Ideal.eq_bot_or_top ((maximalIdeal (PowerSeries ℚ)).comap (PowerSeries.C (R := ℚ))) with h' | h'` into its components or cases. Conclude with `h'`. Conclude with `absurd h' (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)`.

Rewrite `h` using `[hc, Ideal.map_bot]`. Establish `hX : (PowerSeries.X : PowerSeries ℚ) ∈ maximalIdeal (PowerSeries ℚ)`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]`. Simplify using the standard rewrite rules. Rewrite `hX` using `[← h, Ideal.mem_bot]`.

Conclude with `PowerSeries.X_ne_zero hX`.
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

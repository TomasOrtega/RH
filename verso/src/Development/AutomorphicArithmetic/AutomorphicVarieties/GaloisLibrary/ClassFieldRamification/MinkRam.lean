import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Mathlib.NumberTheory.NumberField.Discriminant.Different

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `K _ _ hK`. Establish `h1 : 1 < Module.finrank ℚ K`. Use `Module.finrank_pos (R := ℚ) (M := K)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h2` using `NumberField.abs_discr_gt_two h1`.

Use `set D := differentIdeal ℤ (𝓞 K) with hD`. Establish `hnorm : D.absNorm = (NumberField.discr K).natAbs` using `NumberField.absNorm_differentIdeal K (𝓞 K)`. Establish `hDtop : D ≠ ⊤`. Introduce `h`. Rewrite `hnorm` using `[h, Ideal.absNorm_top]`.

Establish `h3 : ((NumberField.discr K).natAbs : ℤ) = |NumberField.discr K|` using `Int.natCast_natAbs _`. Rewrite `h3` using `[← hnorm]`. Use linear arithmetic over natural numbers and integers. Take `⟨P, hPmax, hDP⟩` from `Ideal.exists_le_maximal D hDtop`. Establish `hPne : P ≠ ⊥`.

Introduce `h`. Rewrite `hDP` using `[h, le_bot_iff]`. Conclude with `differentIdeal_ne_bot hDP`. Use `haveI : NeZero P := ⟨hPne⟩`. Use `⟨Ideal.absNorm (Ideal.under ℤ P), Nat.absNorm_under_prime P, fun hun => ?_⟩` and prove the remaining obligations.

Establish `hram` using `hun P hPmax.isPrime (Int.absNorm_under_mem P)`. Rewrite `hram` using `[Ideal.ramificationIdx_eq_one_iff]`. Conclude with `(dvd_differentIdeal_iff.mp (Ideal.dvd_iff_le.mpr hDP)) hram`.
-/
theorem UpperTheory.V.CF.minkRam :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K ≠ 1 → ∃ p : ℕ, p.Prime ∧ ¬ UnramAt K p := by
  intro K _ _ hK
  have h1 : 1 < Module.finrank ℚ K := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    omega
  have h2 := NumberField.abs_discr_gt_two h1
  set D := differentIdeal ℤ (𝓞 K) with hD
  have hnorm : D.absNorm = (NumberField.discr K).natAbs :=
    NumberField.absNorm_differentIdeal K (𝓞 K)
  have hDtop : D ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at hnorm
    have h3 : ((NumberField.discr K).natAbs : ℤ) = |NumberField.discr K| := Int.natCast_natAbs _
    rw [← hnorm] at h3
    omega
  obtain ⟨P, hPmax, hDP⟩ := Ideal.exists_le_maximal D hDtop
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff] at hDP
    exact differentIdeal_ne_bot hDP
  haveI : NeZero P := ⟨hPne⟩
  refine ⟨Ideal.absNorm (Ideal.under ℤ P), Nat.absNorm_under_prime P, fun hun => ?_⟩
  have hram := hun P hPmax.isPrime (Int.absNorm_under_mem P)
  rw [Ideal.ramificationIdx_eq_one_iff] at hram
  exact (dvd_differentIdeal_iff.mp (Ideal.dvd_iff_le.mpr hDP)) hram

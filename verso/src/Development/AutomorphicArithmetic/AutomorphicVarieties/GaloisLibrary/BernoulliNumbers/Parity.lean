import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `Ω _ _ N _ k χ`. Establish `hne : (-1 : Ω) ≠ 1` using `by norm_num`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hval : χ.toUnitHom (-1) = 1 ↔ χ (-1) = 1`. Rewrite using `[← Units.val_inj, MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, Units.val_one]`.

Use `show ((-1 : (ZMod N)ˣ) ∈ χ.toUnitHom.ker ↔ Even k) ↔ _`. Rewrite using `[MonoidHom.mem_ker, hval]`. Break down `Nat.even_or_odd k with hk | hk` into its components or cases. Rewrite using `[hk.neg_one_pow]`. Simplify using `[hk]`.

Rewrite using `[hk.neg_one_pow]`. Establish `hk' : ¬ Even k` using `Nat.not_even_iff_odd.mpr hk`. Break down `χ.even_or_odd with h | h` into its components or cases. Establish `h1 : χ (-1) = 1` using `h`. Simplify using `[hk', h1, hne.symm]`.

Establish `h1 : χ (-1) = -1` using `h`. Simplify using `[hk', h1, hne]`. Establish `hd` using `DirichletCharacter.conductor_dvd_level χ`. Establish `h` using `DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter hd (-1)`. Rewrite `h` using `[DirichletCharacter.changeLevel_primitiveCharacter, Units.val_neg, Units.val_one, ZMod.cast_neg hd, ZMod.cast_one hd]`.

Conclude with `h.symm`.
-/
theorem UpperTheory.V.Bern.b_parity :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter Ω N), (χ.toUnitHom.ker ∈ parKer N k ↔ χ (-1) = (-1) ^ k) ∧ (χ.primitiveCharacter (-1) = χ (-1)) := by
  intro Ω _ _ N _ k χ
  have hne : (-1 : Ω) ≠ 1 := by norm_num
  refine ⟨?_, ?_⟩
  · have hval : χ.toUnitHom (-1) = 1 ↔ χ (-1) = 1 := by
      rw [← Units.val_inj, MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, Units.val_one]
    show ((-1 : (ZMod N)ˣ) ∈ χ.toUnitHom.ker ↔ Even k) ↔ _
    rw [MonoidHom.mem_ker, hval]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow]
      simp [hk]
    · rw [hk.neg_one_pow]
      have hk' : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      rcases χ.even_or_odd with h | h
      · have h1 : χ (-1) = 1 := h
        simp [hk', h1, hne.symm]
      · have h1 : χ (-1) = -1 := h
        simp [hk', h1, hne]
  · have hd := DirichletCharacter.conductor_dvd_level χ
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter hd (-1)
    rw [DirichletCharacter.changeLevel_primitiveCharacter, Units.val_neg, Units.val_one,
      ZMod.cast_neg hd, ZMod.cast_one hd] at h
    exact h.symm

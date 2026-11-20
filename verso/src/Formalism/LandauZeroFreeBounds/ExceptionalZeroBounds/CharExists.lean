import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne

open Complex
noncomputable section
namespace Formalism.ZeroFreeDirichlet

/- English proof (authored)
Lift both characters to the product modulus and multiply them. At a unit of the product modulus, reduction into each factor modulus gives the original character value. At a nonunit, at least one factor residue is a nonunit by the coprimality criterion. The lifted product and the product of the original values both vanish there.
-/
theorem isProdChar_changeLevel_mul {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    IsProdChar χ₁ χ₂ (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
      DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) := by
  intro n
  rw [MulChar.mul_apply]
  by_cases h : IsUnit (n : ZMod (q₁ * q₂))
  · have h1 : ∀ {q : ℕ} (hq : q ∣ q₁ * q₂) (χ : DirichletCharacter ℂ q),
        DirichletCharacter.changeLevel hq χ (n : ZMod (q₁ * q₂)) = χ (n : ZMod q) := by
      intro q hq χ
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ := χ) hq h.unit
      rw [IsUnit.unit_spec] at this
      rw [this]
      congr 1
      first
        | exact ZMod.cast_natCast hq n
        | exact ZMod.cast_natCast hq _ n
        | exact ZMod.cast_nat_cast hq n
    rw [h1, h1]
  · rw [MulChar.map_nonunit _ h]
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right] at h
    rcases not_and_or.mp h with h' | h'
    · rw [MulChar.map_nonunit χ₁ (by rwa [ZMod.isUnit_iff_coprime])]
      simp
    · rw [MulChar.map_nonunit χ₂ (by rwa [ZMod.isUnit_iff_coprime])]
      simp

/- English proof (authored)
Use the product of the two characters lifted to the product modulus. Its evaluation identity at every natural number is the required property.
-/
theorem exists_product_character : ProdCharExists :=
  fun _ _ χ₁ χ₂ => ⟨_, isProdChar_changeLevel_mul χ₁ χ₂⟩

def characterModFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/- English proof (authored)
The complex-valued character is defined by composing the integer-valued character modulo four with the inclusion of the integers into the complex numbers. Evaluating gives the stated value.
-/
theorem characterModFour_apply (a : ZMod 4) :
    characterModFour a = ((ZMod.χ₄ a : ℤ) : ℂ) := rfl

/- English proof (authored)
The integer character modulo four is quadratic. The ring map into the complex numbers preserves its values, products, and unit, so its complex-valued square is the principal character.
-/
theorem characterModFour_sq : characterModFour ^ 2 = 1 := by
  first
    | exact (ZMod.isQuadratic_χ₄.comp _).sq_eq_one
    | exact (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

/- English proof (authored)
At the unit 3 modulo four this character has value −1, whereas the principal character has value 1. The two characters therefore differ.
-/
theorem characterModFour_ne_one : characterModFour ≠ 1 := by
  intro h
  have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have h3 := DFunLike.congr_fun h (3 : ZMod 4)
  rw [characterModFour_apply, MulChar.one_apply hu] at h3
  have hv : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [hv] at h3
  norm_num at h3

/- English proof (authored)
Choose modulus four and the character just constructed. The modulus is nonzero, the character squares to the principal character, and its value at three proves it is nonprincipal.
-/
theorem exists_real_nontrivial_character : RealCharExists :=
  ⟨4, ⟨by norm_num⟩, characterModFour, characterModFour_sq, characterModFour_ne_one⟩

end Formalism.ZeroFreeDirichlet

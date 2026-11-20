import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

/- English proof (translation)
Introduce `l _ _ Ω _ _ _ A _ c Z hZ m s hs t ht`. Establish `hsI : s ∈ Ine (F` using `ℚ) A := (Subgroup.mem_inf.1 hs).1`. Establish `hsk : cycMod ℚ Ω l m s = 1` using `MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).2`. Establish `hti : t⁻¹ ∈ Ine (F` using `ℚ) A := inv_mem ht`. Establish `h1I : (1 : G ℚ Ω) ∈ Ine (F` using `ℚ) A := one_mem _`.

Use `⟨Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hsI) hti, ?_⟩, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker, map_mul, map_mul, hsk, mul_one, ← map_mul, mul_inv_cancel, map_one]`. Establish `h0 : Z m 1 x = 0`. Establish `h` using `hZ.coc m 1 h1I 1 h1I x`. Rewrite `h` using `[mul_one, map_one, inv_one, mul_one]`.

Take the linear combination `-h`. Establish `h2` using `hZ.coc m t ht t⁻¹ hti x`. Rewrite `h2` using `[mul_inv_cancel, h0]`. Establish `h3` using `hZ.coc m t ht (s * t⁻¹) (mul_mem hsI hti) x`. Establish `h4` using `hZ.coc m s hsI t⁻¹ hti (x * (cycMod ℚ Ω l m t)⁻¹)`.

Rewrite `h4` using `[hsk, inv_one, mul_one]`. Rewrite using `[mul_assoc, h3, h4]`. Take the linear combination `-h2`.
-/
theorem pConj : SConj := by
  intro l _ _ Ω _ _ _ A _ c Z hZ m s hs t ht
  have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
  have hsk : cycMod ℚ Ω l m s = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).2
  have hti : t⁻¹ ∈ Ine (F := ℚ) A := inv_mem ht
  have h1I : (1 : G ℚ Ω) ∈ Ine (F := ℚ) A := one_mem _
  refine ⟨Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hsI) hti, ?_⟩, fun x => ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_mul, hsk, mul_one, ← map_mul, mul_inv_cancel, map_one]
  · have h0 : Z m 1 x = 0 := by
      have h := hZ.coc m 1 h1I 1 h1I x
      rw [mul_one, map_one, inv_one, mul_one] at h
      linear_combination -h
    have h2 := hZ.coc m t ht t⁻¹ hti x
    rw [mul_inv_cancel, h0] at h2
    have h3 := hZ.coc m t ht (s * t⁻¹) (mul_mem hsI hti) x
    have h4 := hZ.coc m s hsI t⁻¹ hti (x * (cycMod ℚ Ω l m t)⁻¹)
    rw [hsk, inv_one, mul_one] at h4
    rw [mul_assoc, h3, h4]
    linear_combination -h2

end UpperTheory.Kd.C7

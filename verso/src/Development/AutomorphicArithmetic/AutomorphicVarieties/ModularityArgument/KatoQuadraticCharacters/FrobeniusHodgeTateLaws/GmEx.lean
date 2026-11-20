import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames

open UpperTheory.V.Z.Kato.Joint
open scoped Matrix MatrixGroups

/- English proof (translation)
Introduce `l _ N h`. Establish `hN : (N : ZMod l) * (N : ZMod l)⁻¹ = 1` using `ZMod.coe_mul_inv_eq_one N h.symm`. Set `m : (ZMod l)ˣ → ℤ` to `fun r => (((-(r : ZMod l)) * (N : ZMod l)⁻¹).val : ℤ)`. Establish `hm : ∀ r : (ZMod l)ˣ, (N : ZMod l) * ((m r : ℤ) : ZMod l) = -(r : ZMod l)`. Introduce `r`.

Simplify using `only [m, Int.cast_natCast, ZMod.natCast_zmod_val]`. Rewrite using `[mul_left_comm, hN, mul_one]`. Use `⟨fun r => ⟨!![1, 0; (N : ℤ) * m r, 1], by simp [Matrix.det_fin_two]⟩, fun r => ?_⟩` and prove the remaining obligations. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩ <;> simp`.

Simplify using the standard rewrite rules. Simplify using `[hm r]`. Use `⟨-1, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hm r]`.
-/
theorem UpperTheory.V.Z.Kato.Joint.gmEx :
    UpperTheory.V.Z.Kato.Joint.GmEx := by
  intro l _ N h
  have hN : (N : ZMod l) * (N : ZMod l)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one N h.symm
  let m : (ZMod l)ˣ → ℤ := fun r => (((-(r : ZMod l)) * (N : ZMod l)⁻¹).val : ℤ)
  have hm : ∀ r : (ZMod l)ˣ, (N : ZMod l) * ((m r : ℤ) : ZMod l) = -(r : ZMod l) := by
    intro r
    simp only [m, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [mul_left_comm, hN, mul_one]
  refine ⟨fun r => ⟨!![1, 0; (N : ℤ) * m r, 1], by simp [Matrix.det_fin_two]⟩, fun r => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩ <;> simp
  · simp
  · simp [hm r]
  · refine ⟨-1, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hm r]

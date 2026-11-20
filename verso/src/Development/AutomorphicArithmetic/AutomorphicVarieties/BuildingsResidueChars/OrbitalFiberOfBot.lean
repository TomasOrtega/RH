import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs

open MulAction in
/- English proof (translation)
Introduce `H Y _ _ H₀ k`. Establish `hmul : ∀ (a : ℂ) (g : orbitRel.Quotient H Y → ℂ), ∑ᶠ o, a * g o = a * ∑ᶠ o, g o` using `fun a g => by simpa only [smul_eq_mul] using (smul_finsum a g).symm`. Use `⟨fun a => ?_, fun hc htriv => ?_⟩` and prove the remaining obligations. Unfold `UpperTheory.V.Z.Sym.gq`. Rewrite using `[← hmul]`.

Conclude with `finsum_congr fun o => mul_div_assoc _ _ _`. Unfold `UpperTheory.V.Z.Sym.gq`. Rewrite using `[← hmul]`. Use `finsum_congr fun o => ?_` and prove the remaining obligations. Establish `hle : H₀ ≤ stabilizer H o.out` using `fun z hz => htriv z hz _`.

Establish `h` using `Subgroup.relIndex_mul_relIndex ⊥ H₀ (stabilizer H o.out) bot_le hle`. Rewrite `h` using `[Subgroup.relIndex_bot_left]`. Establish `hc' : (Nat.card H₀ : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hc`. Rewrite using `[← h, Nat.cast_mul, ← mul_div_assoc, mul_div_mul_left _ _ hc']`.
-/
theorem UpperTheory.orbitalFiber_of_bot :
    UpperTheory.V.Z.Sym.Glob.Fib.Bot := by
  intro H Y _ _ H₀ k
  have hmul : ∀ (a : ℂ) (g : orbitRel.Quotient H Y → ℂ), ∑ᶠ o, a * g o = a * ∑ᶠ o, g o :=
    fun a g => by simpa only [smul_eq_mul] using (smul_finsum a g).symm
  refine ⟨fun a => ?_, fun hc htriv => ?_⟩
  · unfold UpperTheory.V.Z.Sym.gq
    rw [← hmul]
    exact finsum_congr fun o => mul_div_assoc _ _ _
  · unfold UpperTheory.V.Z.Sym.gq
    rw [← hmul]
    refine finsum_congr fun o => ?_
    have hle : H₀ ≤ stabilizer H o.out := fun z hz => htriv z hz _
    have h := Subgroup.relIndex_mul_relIndex ⊥ H₀ (stabilizer H o.out) bot_le hle
    rw [Subgroup.relIndex_bot_left] at h
    have hc' : (Nat.card H₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
    rw [← h, Nat.cast_mul, ← mul_div_assoc, mul_div_mul_left _ _ hc']

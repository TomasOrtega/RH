import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexRingEquivExtendingSubfieldAut

/- English proof (translation)
Establish `hne : ∀ b : ℚ, b ^ 2 ≠ (p : ℚ)`. Introduce `b hb`. Apply `hp.irrational_sqrt` to reduce the goal to its premises. Use `⟨|b|, ?_⟩` and prove the remaining obligations. Establish `h2 : ((b : ℝ)) ^ 2 = (p : ℝ)` using `by exact_mod_cast hb`.

Rewrite using `[← h2, Real.sqrt_sq_eq_abs]`. Use `push_cast`. Both sides reduce to the same expression. Take `⟨a, ha⟩` from `IsAlgClosed.exists_pow_nat_eq (p : Ω) (by norm_num : 0 < 2)`. Establish `hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (p : ℚ))` using `X_pow_sub_C_irreducible_of_prime Nat.prime_two hne`.

Establish `hev : ∀ x : Ω, x ^ 2 = (p : Ω) → Polynomial.aeval x (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)) = 0`. Introduce `x hx`. Simplify using `[hx]`. Establish `hmon : (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)).Monic` using `Polynomial.monic_X_pow_sub_C _ (by norm_num)`. Establish `hmin : minpoly ℚ (-a) = minpoly ℚ a`.

Rewrite using `[← minpoly.eq_of_irreducible_of_monic hirr (hev a ha) hmon, ← minpoly.eq_of_irreducible_of_monic hirr (hev (-a) (by rw [neg_sq, ha])) hmon]`. Take `⟨σ, hσ⟩` from `(Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).mp hmin`. Set `s : Ω ≃+* Ω` to `σ.toRingEquiv`. Establish `hsa : s a = -a` using `hσ`. Take `⟨g, hg⟩` from `GlobalTheory.FN.exists_ringEquiv_extend_of_embedding Ω ε s`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Establish `hea : (ε a) ^ 2 = ((Real.sqrt p : ℝ) : ℂ) ^ 2`. Rewrite using `[← map_pow, ha, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Establish `hga : g (ε a) = -(ε a)` using `by rw [hg, hsa, map_neg]`.

Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hea with h | h` into its components or cases. Rewrite using `[← h, hga]`. Establish `: ((Real.sqrt p : ℝ) : ℂ) = -(ε a)` using `by rw [h, neg_neg]`. Rewrite using `[this, map_neg, hga, neg_neg]`.
-/
private theorem UpperTheory.V.Z.Sym.Unl.exists_ring_equiv_flip_sqrt (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsAlgClosed Ω]
    (ε : Ω →+* ℂ) (p : ℕ) (hp : p.Prime) :
    ∃ σ : ℂ ≃+* ℂ, σ ((Real.sqrt p : ℝ) : ℂ) = -((Real.sqrt p : ℝ) : ℂ) := by
  have hne : ∀ b : ℚ, b ^ 2 ≠ (p : ℚ) := by
    intro b hb
    apply hp.irrational_sqrt
    refine ⟨|b|, ?_⟩
    have h2 : ((b : ℝ)) ^ 2 = (p : ℝ) := by exact_mod_cast hb
    rw [← h2, Real.sqrt_sq_eq_abs]
    push_cast
    rfl
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (p : Ω) (by norm_num : 0 < 2)
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hne
  have hev : ∀ x : Ω, x ^ 2 = (p : Ω) → Polynomial.aeval x (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)) = 0 := by
    intro x hx
    simp [hx]
  have hmon : (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)).Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hmin : minpoly ℚ (-a) = minpoly ℚ a := by
    rw [← minpoly.eq_of_irreducible_of_monic hirr (hev a ha) hmon,
      ← minpoly.eq_of_irreducible_of_monic hirr (hev (-a) (by rw [neg_sq, ha])) hmon]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).mp hmin
  let s : Ω ≃+* Ω := σ.toRingEquiv
  have hsa : s a = -a := hσ
  obtain ⟨g, hg⟩ := GlobalTheory.FN.exists_ringEquiv_extend_of_embedding Ω ε s
  refine ⟨g, ?_⟩
  have hea : (ε a) ^ 2 = ((Real.sqrt p : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, ha, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hga : g (ε a) = -(ε a) := by rw [hg, hsa, map_neg]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hea with h | h
  · rw [← h, hga]
  · have : ((Real.sqrt p : ℝ) : ℂ) = -(ε a) := by rw [h, neg_neg]
    rw [this, map_neg, hga, neg_neg]

/- English proof (translation)
Introduce `p hp` and use `UpperTheory.V.Z.Sym.Unl.exists_ring_equiv_flip_sqrt (AlgebraicClosure ℚ) (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom p hp`.
-/
theorem UpperTheory.V.Z.Sym.Unl.sqrtFlip :
    UpperTheory.V.Z.Sym.Unl.SqrtFlip := fun p hp =>
  UpperTheory.V.Z.Sym.Unl.exists_ring_equiv_flip_sqrt (AlgebraicClosure ℚ)
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom p hp

import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Rootdeg

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Introduce `l j N hl hN L₀ L₁ _ _ _ _ _ ⟨f⟩ ⟨⟨k, hk⟩, _⟩`. Establish `hlk : 0 < l ^ k` using `pow_pos hl.pos k`. Establish `hM : 0 < l ^ k * N` using `Nat.mul_pos hlk hN`. Use `haveI : NeZero (l ^ k) := ⟨hlk.ne'⟩`. Use `haveI : NeZero N := ⟨hN.ne'⟩`.

Use `haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩`. Use `haveI : NeZero ((l ^ k * N : ℕ) : ℚ) := ⟨by exact_mod_cast hM.ne'⟩`. Use `⟨l ^ k * N, hM, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Nat.mul_le_mul_right N (rootdeg L₁ l k hl ⟨_, IsCyclotomicExtension.zeta_spec (l ^ k) L₀ L₁⟩)`. Take `⟨ζ, hζ⟩` from `@IsCyclotomicExtension.exists_isPrimitiveRoot _ ℚ (CyclotomicField (l ^ k * N) ℚ) _ _ _ (CyclotomicField.isCyclotomicExtension _ ℚ) _ (Set.mem_singleton _) hM.ne'`.

Establish `hN'` using `hζ.pow hM rfl`. Establish `hl'` using `hζ.pow hM (Nat.mul_comm _ _)`. Establish `i2` using `@IsCyclotomicExtension.isSplittingField_X_pow_sub_one N _ ℚ (CyclotomicField N ℚ) _ _ _ (CyclotomicField.isCyclotomicExtension N ℚ)`. Set `e : CyclotomicField N ℚ →+* CyclotomicField (l ^ k * N) ℚ` to `(@Polynomial.IsSplittingField.lift (CyclotomicField (l ^ k * N) ℚ) ℚ (CyclotomicField N ℚ) _ _ _ _ _ (Polynomial.X ^ N - 1) i2 (by simpa using Polynomial.X_pow_sub_one_splits hN')).toRingHom`. Use `letI : Algebra L₀ (CyclotomicField (l ^ k * N) ℚ) := (e.comp f.toRingHom).toAlgebra`.

Use `haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one (l ^ k) L₀ L₁`. Set `h : L₁ →ₐ[L₀] CyclotomicField (l ^ k * N) ℚ` to `Polynomial.IsSplittingField.lift _ (Polynomial.X ^ (l ^ k) - 1) (by simpa using Polynomial.X_pow_sub_one_splits hl')`. Conclude with `⟨h.toRingHom.toRatAlgHom⟩`.
-/
theorem UpperTheory.V.Win.layeremb :
    ∀ (l j N : ℕ), l.Prime → 0 < N → ∀ (L₀ L₁ : Type) [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
      [Algebra L₀ L₁], Nonempty (L₀ →ₐ[ℚ] CyclotomicField N ℚ) → IsLayer l j L₀ L₁ →
        ∃ N' : ℕ, 0 < N' ∧ N' ≤ 2 * Module.finrank ℚ L₁ * N ∧ Nonempty (L₁ →ₐ[ℚ] CyclotomicField N' ℚ) := by
  intro l j N hl hN L₀ L₁ _ _ _ _ _ ⟨f⟩ ⟨⟨k, hk⟩, _⟩
  have hlk : 0 < l ^ k := pow_pos hl.pos k
  have hM : 0 < l ^ k * N := Nat.mul_pos hlk hN
  haveI : NeZero (l ^ k) := ⟨hlk.ne'⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : NeZero ((l ^ k * N : ℕ) : ℚ) := ⟨by exact_mod_cast hM.ne'⟩
  refine ⟨l ^ k * N, hM, ?_, ?_⟩
  · exact Nat.mul_le_mul_right N (rootdeg L₁ l k hl ⟨_, IsCyclotomicExtension.zeta_spec (l ^ k) L₀ L₁⟩)
  · obtain ⟨ζ, hζ⟩ := @IsCyclotomicExtension.exists_isPrimitiveRoot _ ℚ (CyclotomicField (l ^ k * N) ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension _ ℚ) _ (Set.mem_singleton _) hM.ne'
    have hN' := hζ.pow hM rfl
    have hl' := hζ.pow hM (Nat.mul_comm _ _)
    have i2 := @IsCyclotomicExtension.isSplittingField_X_pow_sub_one N _ ℚ (CyclotomicField N ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension N ℚ)
    let e : CyclotomicField N ℚ →+* CyclotomicField (l ^ k * N) ℚ :=
      (@Polynomial.IsSplittingField.lift (CyclotomicField (l ^ k * N) ℚ) ℚ (CyclotomicField N ℚ) _ _ _ _ _
        (Polynomial.X ^ N - 1) i2 (by simpa using Polynomial.X_pow_sub_one_splits hN')).toRingHom
    letI : Algebra L₀ (CyclotomicField (l ^ k * N) ℚ) := (e.comp f.toRingHom).toAlgebra
    haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one (l ^ k) L₀ L₁
    let h : L₁ →ₐ[L₀] CyclotomicField (l ^ k * N) ℚ :=
      Polynomial.IsSplittingField.lift _ (Polynomial.X ^ (l ^ k) - 1)
        (by simpa using Polynomial.X_pow_sub_one_splits hl')
    exact ⟨h.toRingHom.toRatAlgHom⟩

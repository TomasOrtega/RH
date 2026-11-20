import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.PadicNormDivLeOne

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

/- English proof (translation)
Establish `hl2 : ¬ l ∣ 2` using `fun h2 => by have := Nat.le_of_dvd two_pos h2; omega`. Establish `hla : ¬ l ∣ a₀`. Introduce `hla`. Apply `hin` to reduce the goal to its premises. Use `⟨(b₀ : ZMod l), ?_⟩` and prove the remaining obligations.

Establish `e` using `congrArg (Int.cast : ℤ → ZMod l) hCm.1`. Move the coercions through the operations in `at e`. Establish `ha0 : (a₀ : ZMod l) = 0` using `(CharP.cast_eq_zero_iff (ZMod l) l a₀).mpr hla`. Rewrite `e` using `[ha0]`. Take the linear combination `-e`.

Use `set N := relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) with hN`. Establish `hN0 : N ≠ 0` using `fun h0 => hIdx (by rw [h0]; exact dvd_zero l)`. Establish `hden : ¬ l ∣ 2 * N ^ 2 * a₀`. Introduce `hd`. Establish `hp : l.Prime` using `Fact.out`.

Break down `(Nat.Prime.dvd_mul hp).mp hd with h' | h'` into its components or cases. Break down `(Nat.Prime.dvd_mul hp).mp h' with h'' | h''` into its components or cases. Conclude with `hl2 h''`. Conclude with `hIdx (hp.dvd_of_dvd_pow h'')`. Conclude with `hla h'`.

Establish `he : Pi.single w (lam * (a₀ : ℂ)) ∈ stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)`. Introduce `i _`. Distinguish the cases in `hi : i = w`. Substitute `hi` using the available equality. Rewrite using `[Pi.single_eq_same]`.

Conclude with `(cmL a₀ b₀ dK ha hdK lam hlam).ω₁_mem_lattice`. Rewrite using `[Pi.single_eq_of_ne hi]`. Conclude with `(cmL a₀ b₀ dK ha hdK lam hlam).lattice.toAddSubgroup.zero_mem`. Establish `h1` using `idx_smul_symm_mem (cmL a₀ b₀ dK ha hdK lam hlam) h Λ hΛ g₁ hIso he`. Establish `h3` using `idx_smul_mem (cmL a₀ b₀ dK ha hdK lam hlam) Λ g₁ (hτ _ h1)`.

Establish `h4` using `h3 x (Set.mem_univ x)`. Take `⟨m, k, hmk⟩` from `PeriodPair.mem_lattice.mp h4`. Establish `hsingle : Pi.single w (lam * (a₀ : ℂ)) = (lam * (a₀ : ℂ)) • Pi.single w (1 : ℂ)`. Use extensionality with `i`. Distinguish the cases in `hi : i = w`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hi]`. Rewrite `hmk` using `[hsingle, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]`. Simplify using `only [map_smul, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at hmk`.

Establish `hω1 : (cmL a₀ b₀ dK ha hdK lam hlam).ω₁ = lam * (a₀ : ℂ)` using `rfl`. Establish `hω2 : (cmL a₀ b₀ dK ha hdK lam hlam).ω₂ = lam * cmTheta b₀ dK` using `rfl`. Rewrite `hmk` using `[hω1, hω2, cmTheta]`. Use `⟨((2 * m * a₀ + k * b₀ : ℤ) : ℚ) / ((2 * N ^ 2 * a₀ : ℕ) : ℚ), ((k : ℤ) : ℚ) / ((2 * N ^ 2 * a₀ : ℕ) : ℚ), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[padicNorm.div, (padicNorm.nat_eq_one_iff _).mpr hden, div_one]`.

Conclude with `padicNorm.of_int _`. Rewrite using `[padicNorm.div, (padicNorm.nat_eq_one_iff _).mpr hden, div_one]`. Conclude with `padicNorm.of_int _`. Establish `hNc : (N : ℂ) ≠ 0` using `by exact_mod_cast hN0`. Establish `hac : (a₀ : ℂ) ≠ 0` using `by exact_mod_cast ha.ne'`.

Use `set E := g₁ (τ (g₁.symm (Pi.single w 1))) x with hEdef`. Establish `hE : ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) * E = lam * (2 * (m : ℂ) * a₀ + k * b₀ + k * (Complex.I * ((Real.sqrt dK : ℝ) : ℂ)))`. Take the linear combination `(-2 : ℂ) * hmk`. Establish `hc : ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) ≠ 0` using `by simp [hNc, hac, hlam]`. Establish `hE' : E = lam * (2 * (m : ℂ) * a₀ + k * b₀ + k * (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) / ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2)`.

Rewrite using `[eq_div_iff hc, mul_comm]`. Conclude with `hE`. Rewrite using `[hE']`. Unfold `sq`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem conj_entry_int {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} {ha : 0 < a₀} {hdK : 0 < dK} {lam : ℂ} {hlam : lam ≠ 0}
    (hCm : CmOK a₀ b₀ c₀ dK) (l : ℕ) [Fact l.Prime] (hl5 : 5 ≤ l)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) {n : Type} [Fintype n] [DecidableEq n]
    (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (hΛ : IsSelfDual (matH h) Λ)
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hIso : IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hIdx : ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)))
    (τ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (hτ : ∀ y ∈ pow4 Λ, τ y ∈ pow4 Λ) (x w : Fin 4 × n) :
    ∃ q₁ q₂ : ℚ, padicNorm l q₁ ≤ 1 ∧ padicNorm l q₂ ≤ 1 ∧
      g₁ (τ (g₁.symm (Pi.single w 1))) x = q₁ + q₂ * sq dK := by
  classical
  have hl2 : ¬ l ∣ 2 := fun h2 => by have := Nat.le_of_dvd two_pos h2; omega
  have hla : ¬ l ∣ a₀ := by
    intro hla
    apply hin
    refine ⟨(b₀ : ZMod l), ?_⟩
    have e := congrArg (Int.cast : ℤ → ZMod l) hCm.1
    push_cast at e
    have ha0 : (a₀ : ZMod l) = 0 := (CharP.cast_eq_zero_iff (ZMod l) l a₀).mpr hla
    rw [ha0] at e
    linear_combination -e
  set N := relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) with hN
  have hN0 : N ≠ 0 := fun h0 => hIdx (by rw [h0]; exact dvd_zero l)
  have hden : ¬ l ∣ 2 * N ^ 2 * a₀ := by
    intro hd
    have hp : l.Prime := Fact.out
    rcases (Nat.Prime.dvd_mul hp).mp hd with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
      · exact hl2 h''
      · exact hIdx (hp.dvd_of_dvd_pow h'')
    · exact hla h'
  have he : Pi.single w (lam * (a₀ : ℂ)) ∈ stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n) := by
    intro i _
    by_cases hi : i = w
    · subst hi
      rw [Pi.single_eq_same]
      exact (cmL a₀ b₀ dK ha hdK lam hlam).ω₁_mem_lattice
    · rw [Pi.single_eq_of_ne hi]
      exact (cmL a₀ b₀ dK ha hdK lam hlam).lattice.toAddSubgroup.zero_mem
  have h1 := idx_smul_symm_mem (cmL a₀ b₀ dK ha hdK lam hlam) h Λ hΛ g₁ hIso he
  have h3 := idx_smul_mem (cmL a₀ b₀ dK ha hdK lam hlam) Λ g₁ (hτ _ h1)
  have h4 := h3 x (Set.mem_univ x)
  obtain ⟨m, k, hmk⟩ := PeriodPair.mem_lattice.mp h4
  have hsingle : Pi.single w (lam * (a₀ : ℂ)) = (lam * (a₀ : ℂ)) • Pi.single w (1 : ℂ) := by
    ext i; by_cases hi : i = w
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  rw [hsingle, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hmk
  simp only [map_smul, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at hmk
  have hω1 : (cmL a₀ b₀ dK ha hdK lam hlam).ω₁ = lam * (a₀ : ℂ) := rfl
  have hω2 : (cmL a₀ b₀ dK ha hdK lam hlam).ω₂ = lam * cmTheta b₀ dK := rfl
  rw [hω1, hω2, cmTheta] at hmk
  refine ⟨((2 * m * a₀ + k * b₀ : ℤ) : ℚ) / ((2 * N ^ 2 * a₀ : ℕ) : ℚ),
    ((k : ℤ) : ℚ) / ((2 * N ^ 2 * a₀ : ℕ) : ℚ), ?_, ?_, ?_⟩
  · rw [padicNorm.div, (padicNorm.nat_eq_one_iff _).mpr hden, div_one]; exact padicNorm.of_int _
  · rw [padicNorm.div, (padicNorm.nat_eq_one_iff _).mpr hden, div_one]; exact padicNorm.of_int _
  · have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
    have hac : (a₀ : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    set E := g₁ (τ (g₁.symm (Pi.single w 1))) x with hEdef
    have hE : ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) * E =
        lam * (2 * (m : ℂ) * a₀ + k * b₀ + k * (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) := by
      linear_combination (-2 : ℂ) * hmk
    have hc : ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) ≠ 0 := by simp [hNc, hac, hlam]
    have hE' : E = lam * (2 * (m : ℂ) * a₀ + k * b₀ + k * (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) /
        ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) := by
      rw [eq_div_iff hc, mul_comm]; exact hE
    rw [hE']
    unfold sq
    push_cast
    field_simp

/- English proof (translation)
Use extensionality with `x w`. Rewrite using `[LinearMap.toMatrix'_apply]`. Both sides reduce to the same expression.
-/
theorem gmat_eq {n : Type} [Fintype n] [DecidableEq n] (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    gmat g = LinearMap.toMatrix' (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
  ext x w
  rw [LinearMap.toMatrix'_apply]
  rfl

/- English proof (translation)
Establish `e : LinearMap.toMatrix' (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) * T * gmat g = LinearMap.toMatrix' ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ Matrix.toLin' T ∘ₗ (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))`. Rewrite using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', gmat_eq, mul_assoc]`. Rewrite using `[e, LinearMap.toMatrix'_apply]`. Both sides reduce to the same expression.
-/
theorem conj_matrix_apply {n : Type} [Fintype n] [DecidableEq n] (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (T : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) (x w : Fin 4 × n) :
    (LinearMap.toMatrix' (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) * T * gmat g) x w
      = g (Matrix.toLin' T (g.symm (Pi.single w 1))) x := by
  have e : LinearMap.toMatrix' (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) * T * gmat g =
      LinearMap.toMatrix' ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ Matrix.toLin' T ∘ₗ
        (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))) := by
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', gmat_eq, mul_assoc]
  rw [e, LinearMap.toMatrix'_apply]
  rfl

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame

import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, N = n + 1` from `⟨N - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos N)).symm⟩`. Take `⟨j, hj⟩` from `h`. Introduce `x hx`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hj, map_pow, Units.val_neg, Units.val_one, ZMod.val_neg_one]`.

Establish `hz : (j x) ^ (n + 1) = 1` using `by rw [← map_pow, hx, map_one]`. Establish `hnorm : ‖j x‖ = 1`. Establish `: ‖j x‖ ^ (n + 1) = 1` using `by rw [← norm_pow, hz, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.succ_ne_zero n)).1 this`. Establish `hne : j x ≠ 0`.

Introduce `h0`. Rewrite `hnorm` using `[h0, norm_zero]`. Conclude with `zero_ne_one hnorm`. Establish `h1 : j x * (starRingEnd ℂ) (j x) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]`.

Evaluate the numerical expressions. Establish `h2 : j x * (j x) ^ n = 1` using `by rw [← pow_succ', hz]`. Conclude with `mul_left_cancel₀ hne (h1.trans h2.symm)`.
-/
private theorem conj_cycLift {Ω : Type} [Field Ω] (N : ℕ) [NeZero N] {σ : Ω ≃+* Ω} (h : IsConjOm σ) :
    CycLift N (-1) σ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos N)).symm⟩
  obtain ⟨j, hj⟩ := h
  intro x hx
  apply j.injective
  rw [hj, map_pow, Units.val_neg, Units.val_one, ZMod.val_neg_one]
  have hz : (j x) ^ (n + 1) = 1 := by rw [← map_pow, hx, map_one]
  have hnorm : ‖j x‖ = 1 := by
    have : ‖j x‖ ^ (n + 1) = 1 := by rw [← norm_pow, hz, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.succ_ne_zero n)).1 this
  have hne : j x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have h1 : j x * (starRingEnd ℂ) (j x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have h2 : j x * (j x) ^ n = 1 := by rw [← pow_succ', hz]
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ N _ ρ hρ`. Take `⟨σ, hσ⟩` from `exists_isConjOm (E := E) (Ω := Ω)`. Establish `hL1 : IsLift (cE E) σ` using `hσ.isLift`. Establish `hL2 : IsLift (ρ (-1)).toRingEquiv σ` using `hρ (-1) σ (conj_cycLift N hσ)`. Establish `heq : (ρ (-1)).toRingEquiv = cE E`.

Use extensionality with `x`. Apply `(algebraMap E Ω).injective` to reduce the goal to its premises. Rewrite using `[← hL2 x, hL1 x]`. Use `⟨heq, ?_⟩` and prove the remaining obligations. Introduce `hone`.

Establish `hker : ρ (-1) = 1`. Use `(QuotientGroup.eq_one_iff (N := ρ.ker) (-1 : (ZMod N)ˣ)).1 hone` as an intermediate fact. Conclude with `this`. Apply `IsCMField.complexConj_ne_one (K := E)` to reduce the goal to its premises. Use extensionality with `x`.

Use `congrArg (fun f : E ≃+* E => f x) heq` as an intermediate fact. Simplify using `only [hker] at this`. Conclude with `this.symm`.
-/
theorem UpperTheory.V.Odd.actConj :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → (ρ (-1)).toRingEquiv = cE E ∧ piQ ρ (-1) ≠ 1 := by
  intro E Ω _ _ _ _ _ _ N _ ρ hρ
  obtain ⟨σ, hσ⟩ := exists_isConjOm (E := E) (Ω := Ω)
  have hL1 : IsLift (cE E) σ := hσ.isLift
  have hL2 : IsLift (ρ (-1)).toRingEquiv σ := hρ (-1) σ (conj_cycLift N hσ)
  have heq : (ρ (-1)).toRingEquiv = cE E := by
    ext x
    apply (algebraMap E Ω).injective
    rw [← hL2 x, hL1 x]
  refine ⟨heq, ?_⟩
  intro hone
  have hker : ρ (-1) = 1 := by
    have := (QuotientGroup.eq_one_iff (N := ρ.ker) (-1 : (ZMod N)ˣ)).1 hone
    exact this
  apply IsCMField.complexConj_ne_one (K := E)
  ext x
  have := congrArg (fun f : E ≃+* E => f x) heq
  simp only [hker] at this
  exact this.symm

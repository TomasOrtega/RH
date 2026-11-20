import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDefs

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

scoped instance (p p' : PC) : NeZero ((p.1 + 1) * (p'.1 + 1)) := ⟨by positivity⟩

def mulLevel (p p' : PC) : DirichletCharacter ℂ ((p.1 + 1) * (p'.1 + 1)) :=
  DirichletCharacter.changeLevel (dvd_mul_right (p.1 + 1) (p'.1 + 1)) p.2 *
    (DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2)⁻¹

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem mulLevel_ne_one (p p' : PC) (hp : p.2.IsPrimitive) (hp' : p'.2.IsPrimitive) (hne : p ≠ p') :
    mulLevel p p' ≠ 1 := by
  intro h
  have h1 := mul_inv_eq_one.mp h
  have hc := congrArg DirichletCharacter.conductor h1
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
    hp, hp'] at hc
  obtain ⟨N, χ⟩ := p
  obtain ⟨N', χ'⟩ := p'
  simp only [add_left_inj] at hc
  subst hc
  apply hne
  have := DirichletCharacter.changeLevel_injective (dvd_mul_right (N + 1) (N + 1)) h1
  exact congrArg (Sigma.mk N) this

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem mulLevel_apply (p p' : PC) (n : ℕ) :
    mulLevel p p' (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p n * (starRingEnd ℂ) (cv p' n) := by
  by_cases hu : IsUnit (n : ZMod ((p.1 + 1) * (p'.1 + 1)))
  · obtain ⟨u, hu⟩ := hu
    have e1 : DirichletCharacter.changeLevel (dvd_mul_right (p.1 + 1) (p'.1 + 1)) p.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p n := by
      rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
        ZMod.cast_natCast (dvd_mul_right _ _)]
      rfl
    have e2 : DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p' n := by
      rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
        ZMod.cast_natCast (dvd_mul_left _ _)]
      rfl
    have hn : ‖DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1)))‖ = 1 := by
      rw [← hu]
      exact DirichletCharacter.unit_norm_eq_one _ u
    unfold mulLevel
    rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv', e1, Complex.inv_eq_conj hn, e2]
  · rw [MulChar.map_nonunit _ hu]
    rw [ZMod.isUnit_iff_coprime] at hu
    by_cases h1 : n.Coprime (p.1 + 1)
    · have h2 : ¬ n.Coprime (p'.1 + 1) := fun h2 => hu (Nat.Coprime.mul_right h1 h2)
      have h3 : cv p' n = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [h3, map_zero, mul_zero]
    · have h3 : cv p n = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [h3, zero_mul]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
private lemma sum_range_natCast_zmod_eq_sum_univ {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) :
    ∑ n ∈ Finset.range Q, f (n : ZMod Q) = ∑ x : ZMod Q, f x := by
  refine Finset.sum_nbij (fun n : ℕ => (n : ZMod Q)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro a ha b hb hab
    have ha' : a < Q := Finset.mem_range.mp ha
    have hb' : b < Q := Finset.mem_range.mp hb
    have h := congrArg ZMod.val hab
    simp only at h
    rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at h
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

/- English proof (translation)
Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private lemma sum_range_modulus_shift_eq_zero_of_ne_one {Q : ℕ} [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hψ : ψ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.range Q, ψ ((M + n : ℕ) : ZMod Q) = 0 := by
  calc ∑ n ∈ Finset.range Q, ψ ((M + n : ℕ) : ZMod Q)
        = ∑ n ∈ Finset.range Q, (fun x => ψ ((M : ZMod Q) + x)) (n : ZMod Q) := by
          simp [Nat.cast_add]
    _ = ∑ x : ZMod Q, ψ ((M : ZMod Q) + x) := sum_range_natCast_zmod_eq_sum_univ (fun x => ψ ((M : ZMod Q) + x))
    _ = ∑ x : ZMod Q, ψ x := Equiv.sum_comp (Equiv.addLeft (M : ZMod Q)) ψ
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hψ

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Chain the equalities or inequalities of the calculation.

Extract witnesses or component facts from the available result. Substitute using the available equality. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma norm_charSum_range_le_modulus_of_ne_one {Q : ℕ} [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hψ : ψ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, ψ (n : ZMod Q)‖ ≤ (Q : ℝ) := by
  have hQ : 0 < Q := NeZero.pos Q
  refine Nat.strong_induction_on M ?_
  intro M ih
  by_cases hM : M < Q
  · calc ‖∑ n ∈ Finset.range M, ψ (n : ZMod Q)‖
          ≤ ∑ n ∈ Finset.range M, ‖ψ (n : ZMod Q)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range M, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one ψ _
      _ = M := by simp
      _ ≤ Q := by exact_mod_cast hM.le
  · obtain ⟨K, hK⟩ : ∃ K, M = K + Q := ⟨M - Q, by omega⟩
    subst hK
    rw [Finset.sum_range_add, sum_range_modulus_shift_eq_zero_of_ne_one ψ hψ K, add_zero]
    exact ih K (by omega)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem pair_sum_bound : PairSum := by
  intro p p' hp hp' hne M
  have h := norm_charSum_range_le_modulus_of_ne_one (mulLevel p p') (mulLevel_ne_one p p' hp hp' hne) M
  simpa only [mulLevel_apply] using h

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

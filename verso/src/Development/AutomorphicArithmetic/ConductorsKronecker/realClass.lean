import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
import Development.AutomorphicArithmetic.MeanSquareBounds.realCond

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

/- English proof (translation)
Apply `MulChar.ext` to reduce the goal to its premises. Introduce `u`. Rewrite using `[MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply u.isUnit]`. Establish `hn : ‖χ (u : ZMod N)‖ = 1` using `DirichletCharacter.unit_norm_eq_one χ u`. Establish `him : (χ (u : ZMod N)).im = 0` using `hreal _`.

Use `set z := χ (u : ZMod N) with hz`. Apply the tactic sequence `have h1 : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]`. Establish `h2 : z.re ^ 2 = 1`. Use `Complex.sq_norm z` as an intermediate fact. Rewrite `this` using `[hn, Complex.normSq_apply, him]`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[h1]`. Conclude with `h2` after adjusting the coercions.
-/
private theorem realClass_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hreal : ∀ a : ZMod N, (χ a).im = 0) : χ ^ 2 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply u.isUnit]
  have hn : ‖χ (u : ZMod N)‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
  have him : (χ (u : ZMod N)).im = 0 := hreal _
  set z := χ (u : ZMod N) with hz
  have h1 : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  have h2 : z.re ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hn, Complex.normSq_apply, him] at this
    nlinarith
  rw [h1]; exact_mod_cast h2

/- English proof (translation)
Take `⟨θ, hθ⟩` from `h`. Establish `e` using `(H.isPrimOf_iff θ ⟨N, χ, hθ.1⟩).1 hθ`. Establish `e2 : N = (H.dir θ).conductor` using `congrArg Formalism.HC.PChar.N e`. Rewrite using `[e2]`. Conclude with `DirichletCharacter.conductor_dvd_level _`.
-/
private theorem realClass_level_dvd {φ : Frame} (H : HostRaw φ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : H.IsCharE χ) : N ∣ H.condN := by
  obtain ⟨θ, hθ⟩ := h
  have e := (H.isPrimOf_iff θ ⟨N, χ, hθ.1⟩).1 hθ
  have e2 : N = (H.dir θ).conductor := congrArg Formalism.HC.PChar.N e
  rw [e2]
  exact DirichletCharacter.conductor_dvd_level _

/- English proof (translation)
Introduce `φ H N _ χ hχ`. Establish `hdvd` using `realClass_level_dvd H χ hχ`. Use `⟨hdvd, fun hreal => ?_⟩` and prove the remaining obligations. Establish `hp : χ.IsPrimitive`. Take `⟨θ, hθ⟩` from `hχ`.

Conclude with `hθ.1`. Establish `h2` using `realClass_sq χ hreal`. Distinguish the cases in `hqd : H.q ∣ N ∨ H.d ∣ N`. Conclude with `Or.inr hqd`. Use `left`.

Establish `hq : H.q.Prime` using `H.hyp.1`. Establish `hd : H.d.Prime` using `H.hyp.2.1`. Rewrite `hqd` using `[not_or]`. Establish `hN : N ∣ 8 * ordCompl[2] H.QS * H.q * H.d`. Use `QH.real_cond _ H.q H.d N χ hp h2 (dvd_mul_right _ _) hq hd fun p hpp hpN => ?_` and prove the remaining obligations.

Establish `h3 : p ∣ H.QS * H.q * H.d` using `hpN.trans hdvd`. Break down `hpp.dvd_mul.1 h3 with h4 | h4` into its components or cases. Break down `hpp.dvd_mul.1 h4 with h5 | h5` into its components or cases. Use `left`. Rewrite `h5` using `[← Nat.ordProj_mul_ordCompl_eq_self H.QS 2]`.

Break down `hpp.dvd_mul.1 h5 with h6 | h6` into its components or cases. Conclude with `((hpp.dvd_of_dvd_pow h6).trans (by norm_num)).mul_right _`. Conclude with `h6.mul_left _`. Conclude with `Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp hq).1 h5))`. Conclude with `Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp hd).1 h4))`.

Establish `cq : N.Coprime H.q` using `((Nat.Prime.coprime_iff_not_dvd hq).2 hqd.1).symm`. Establish `cd : N.Coprime H.d` using `((Nat.Prime.coprime_iff_not_dvd hd).2 hqd.2).symm`. Conclude with `cq.dvd_of_dvd_mul_right (cd.dvd_of_dvd_mul_right hN)`.
-/
theorem UpperTheory.GL.realClass :
    ∀ {φ : Frame} (H : HostRaw φ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsCharE χ →
      N ∣ H.condN ∧ ((∀ a : ZMod N, (χ a).im = 0) → N ∣ 8 * ordCompl[2] H.QS ∨ H.q ∣ N ∨ H.d ∣ N) := by
  intro φ H N _ χ hχ
  have hdvd := realClass_level_dvd H χ hχ
  refine ⟨hdvd, fun hreal => ?_⟩
  have hp : χ.IsPrimitive := by
    obtain ⟨θ, hθ⟩ := hχ
    exact hθ.1
  have h2 := realClass_sq χ hreal
  by_cases hqd : H.q ∣ N ∨ H.d ∣ N
  · exact Or.inr hqd
  · left
    have hq : H.q.Prime := H.hyp.1
    have hd : H.d.Prime := H.hyp.2.1
    rw [not_or] at hqd
    have hN : N ∣ 8 * ordCompl[2] H.QS * H.q * H.d := by
      refine QH.real_cond _ H.q H.d N χ hp h2 (dvd_mul_right _ _) hq hd fun p hpp hpN => ?_
      have h3 : p ∣ H.QS * H.q * H.d := hpN.trans hdvd
      rcases hpp.dvd_mul.1 h3 with h4 | h4
      · rcases hpp.dvd_mul.1 h4 with h5 | h5
        · left
          rw [← Nat.ordProj_mul_ordCompl_eq_self H.QS 2] at h5
          rcases hpp.dvd_mul.1 h5 with h6 | h6
          · exact ((hpp.dvd_of_dvd_pow h6).trans (by norm_num)).mul_right _
          · exact h6.mul_left _
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp hq).1 h5))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp hd).1 h4))
    have cq : N.Coprime H.q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd.1).symm
    have cd : N.Coprime H.d := ((Nat.Prime.coprime_iff_not_dvd hd).2 hqd.2).symm
    exact cq.dvd_of_dvd_mul_right (cd.dvd_of_dvd_mul_right hN)

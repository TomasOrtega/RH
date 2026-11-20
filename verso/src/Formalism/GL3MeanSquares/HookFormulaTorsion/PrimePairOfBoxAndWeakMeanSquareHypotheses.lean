import Mathlib
import Formalism.GL3MeanSquares.PrimePairOfBoxAndWeakMeanSquareHypotheses
import Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity
import Formalism.GL3MeanSquares.HookFormulaTorsion.NumericalZeroDensityBound

open Filter

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

/- English proof (translation)
The claim follows from `Real.exp_pos _`.
-/
private lemma exp_scale_pos (ε x : ℝ) : 0 < X1 ε x := Real.exp_pos _
/- English proof (translation)
The claim follows from `Real.exp_pos _`.
-/
private lemma double_exp_scale_pos (ε x : ℝ) : 0 < X2 ε x := Real.exp_pos _
/- English proof (translation)
The claim follows from `Real.log_exp _`.
-/
private lemma log_exp_scale (ε x : ℝ) : Real.log (X1 ε x) = x ^ (ε / 5) := Real.log_exp _
/- English proof (translation)
The claim follows from `Real.log_exp _`.
-/
private lemma log_double_exp_scale (ε x : ℝ) : Real.log (X2 ε x) = x ^ (ε / 5) * Real.log x ^ 2 := Real.log_exp _

open DirichletCharacter in
/- English proof (translation)
Establish `hA : A.conductor ∣ (A * B).conductor`. Establish `h1 : A.conductor ∣ ((A * B).conductor).lcm (B⁻¹).conductor`. Use `conductor_mul_dvd_lcm_conductor (A * B) B⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right]`. Then use the resulting hypothesis. Rewrite `h1` using `[conductor_inv]`.

Establish `h2 : A.conductor ∣ (A * B).conductor * B.conductor` using `h1.trans (Nat.lcm_dvd_mul _ _)`. Conclude with `h.dvd_of_dvd_mul_right h2`. Establish `hB : B.conductor ∣ (A * B).conductor`. Establish `h1 : B.conductor ∣ ((A * B).conductor).lcm (A⁻¹).conductor`. Use `conductor_mul_dvd_lcm_conductor (A * B) A⁻¹` as an intermediate fact.

Rewrite `this` using `[mul_comm A B, mul_inv_cancel_right, mul_comm B A]`. Then use the resulting hypothesis. Rewrite `h1` using `[conductor_inv]`. Establish `h2 : B.conductor ∣ (A * B).conductor * A.conductor` using `h1.trans (Nat.lcm_dvd_mul _ _)`. Conclude with `h.symm.dvd_of_dvd_mul_right h2`. Conclude with `h.mul_dvd_of_dvd_of_dvd hA hB`.
-/
private lemma cond_mul_coprime {n : ℕ} [NeZero n] (A B : DirichletCharacter ℂ n)
    (h : A.conductor.Coprime B.conductor) : A.conductor * B.conductor ∣ (A * B).conductor := by
  have hA : A.conductor ∣ (A * B).conductor := by
    have h1 : A.conductor ∣ ((A * B).conductor).lcm (B⁻¹).conductor := by
      have := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
      rwa [mul_inv_cancel_right] at this
    rw [conductor_inv] at h1
    have h2 : A.conductor ∣ (A * B).conductor * B.conductor := h1.trans (Nat.lcm_dvd_mul _ _)
    exact h.dvd_of_dvd_mul_right h2
  have hB : B.conductor ∣ (A * B).conductor := by
    have h1 : B.conductor ∣ ((A * B).conductor).lcm (A⁻¹).conductor := by
      have := conductor_mul_dvd_lcm_conductor (A * B) A⁻¹
      rwa [mul_comm A B, mul_inv_cancel_right, mul_comm B A] at this
    rw [conductor_inv] at h1
    have h2 : B.conductor ∣ (A * B).conductor * A.conductor := h1.trans (Nat.lcm_dvd_mul _ _)
    exact h.symm.dvd_of_dvd_mul_right h2
  exact h.mul_dvd_of_dvd_of_dvd hA hB

/- English proof (translation)
Introduce `h`. Establish `h1 : quadraticChar (ZMod q) ≠ 1` using `quadraticChar_ne_one (by rwa [ZMod.ringChar_zmod_n])`. Apply `h1` to reduce the goal to its premises. Use extensionality with `a`. Use `congrArg (fun χ : DirichletCharacter ℂ q => χ a) h` as an intermediate fact.

Simplify using `only [qc, MulChar.ringHomComp_apply, MulChar.one_apply_coe] at this`. Establish `h2 : ((quadraticChar (ZMod q) (a : ZMod q) : ℤ) : ℂ) = ((1 : ℤ) : ℂ)` using `by simpa using this`. Rewrite using `[MulChar.one_apply_coe]`. Conclude with `h2` after adjusting the coercions.
-/
private lemma qc_ne_one (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) : qc q ≠ 1 := by
  intro h
  have h1 : quadraticChar (ZMod q) ≠ 1 := quadraticChar_ne_one (by rwa [ZMod.ringChar_zmod_n])
  apply h1
  ext a
  have := congrArg (fun χ : DirichletCharacter ℂ q => χ a) h
  simp only [qc, MulChar.ringHomComp_apply, MulChar.one_apply_coe] at this
  have h2 : ((quadraticChar (ZMod q) (a : ZMod q) : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by simpa using this
  rw [MulChar.one_apply_coe]
  exact_mod_cast h2

/- English proof (translation)
Establish `hp : q.Prime` using `Fact.out`. Establish `: NeZero q` using `⟨hp.ne_zero⟩`. Break down `(Nat.dvd_prime hp).1 (DirichletCharacter.conductor_dvd_level (qc q)) with h | h` into its components or cases. Conclude with `absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q hq)`. Conclude with `h`.
-/
private lemma qc_prim (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) : (qc q).IsPrimitive := by
  have hp : q.Prime := Fact.out
  have : NeZero q := ⟨hp.ne_zero⟩
  rcases (Nat.dvd_prime hp).1 (DirichletCharacter.conductor_dvd_level (qc q)) with h | h
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q hq)
  · exact h

/- English proof (translation)
The claim follows from `((quadraticChar_isQuadratic (ZMod q)).comp _).sq_eq_one`.
-/
private lemma qc_sq (q : ℕ) [Fact q.Prime] : qc q ^ 2 = 1 :=
  ((quadraticChar_isQuadratic (ZMod q)).comp _).sq_eq_one

/- English proof (translation)
The claim follows from `(ZMod.isQuadratic_χ₈.comp _).sq_eq_one`.
-/
private lemma chi_eight_sq : chi8 ^ 2 = 1 := (ZMod.isQuadratic_χ₈.comp _).sq_eq_one

/- English proof (translation)
Establish `hd : chi8.conductor ∣ 2 ^ 3` using `DirichletCharacter.conductor_dvd_level chi8`. Take `⟨k, hk, hk'⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 hd`. Distinguish the cases in `h3 : k = 3`. Substitute `h3` using the available equality. Conclude with `hk'`.

It suffices to derive a contradiction. Establish `h4 : chi8.conductor ∣ 4`. Rewrite using `[hk', show (4 : ℕ) = 2 ^ 2 by norm_num]`. Conclude with `pow_dvd_pow 2 (by omega)`. Establish `hmem` using `(DirichletCharacter.mem_conductorSet_iff_conductor_dvd chi8 (show 4 ∣ 8 by norm_num)).2 h4`.

Take `⟨h, χ₀, hχ⟩` from `hmem`. Establish `h5 : chi8 ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4)`. Rewrite using `[hχ]`. Conclude with `DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ h (by`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`.

Use the proof step `decide)`. Establish `h6 : ((5 : ℤ) : ZMod 4) = 1` using `by decide`. Establish `h7 : chi8 ((5 : ℤ) : ZMod 8) = -1`. Simplify using `[chi8, MulChar.ringHomComp_apply]`. Rewrite `h5` using `[h6, map_one, h7]`.

Evaluate the numerical expressions using `at h5`.
-/
private lemma chi_eight_primitive : chi8.IsPrimitive := by
  have hd : chi8.conductor ∣ 2 ^ 3 := DirichletCharacter.conductor_dvd_level chi8
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  by_cases h3 : k = 3
  · subst h3; exact hk'
  · exfalso
    have h4 : chi8.conductor ∣ 4 := by
      rw [hk', show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    have hmem := (DirichletCharacter.mem_conductorSet_iff_conductor_dvd chi8 (show 4 ∣ 8 by norm_num)).2 h4
    obtain ⟨h, χ₀, hχ⟩ := hmem
    have h5 : chi8 ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4) := by
      rw [hχ]
      exact DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ h (by
        rw [Int.isCoprime_iff_gcd_eq_one]; decide)
    have h6 : ((5 : ℤ) : ZMod 4) = 1 := by decide
    have h7 : chi8 ((5 : ℤ) : ZMod 8) = -1 := by
      simp [chi8, MulChar.ringHomComp_apply]
    rw [h6, map_one, h7] at h5
    norm_num at h5

/- English proof (translation)
Use `⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩` and prove the remaining obligations. Introduce `t θ q _ hθ hq hc`. Establish `hp : q.Prime` using `Fact.out`. Establish `ht : t ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hc` using `[Nat.coprime_zero_right]`. Conclude with `hp.one_lt.ne' hc`. Establish `: NeZero t` using `⟨ht⟩`. Establish `hprim : (tw θ q).IsPrimitive`. Establish `h1 : (DirichletCharacter.changeLevel (Dvd.intro q rfl : t ∣ t * q) θ).conductor = t`.

Rewrite using `[DirichletCharacter.conductor_changeLevel]`. Conclude with `hθ`. Establish `h2 : (DirichletCharacter.changeLevel (Dvd.intro_left t rfl : q ∣ t * q) (qc q)).conductor = q`. Rewrite using `[DirichletCharacter.conductor_changeLevel]`. Conclude with `qc_prim q hq`.

Establish `h3` using `cond_mul_coprime (DirichletCharacter.changeLevel (Dvd.intro q rfl : t ∣ t * q) θ) (DirichletCharacter.changeLevel (Dvd.intro_left t rfl : q ∣ t * q) (qc q)) (by rw [h1, h2]; exact hc.symm)`. Rewrite `h3` using `[h1, h2]`. Conclude with `Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level _) h3`. Use `⟨hprim, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Establish `h1` using `DirichletCharacter.eq_one_iff_conductor_eq_one.1 h`. Rewrite `h1` using `[(DirichletCharacter.isPrimitive_def _).1 hprim]`. Conclude with `hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_left h1)`. Introduce `h2`. Unfold `tw`.

Rewrite using `[mul_pow, ← map_pow, ← map_pow, h2, qc_sq, map_one, map_one, one_mul]`.
-/
private theorem twist_is_primitive : TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q _ hθ hq hc
  have hp : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hc
    exact hp.one_lt.ne' hc
  have : NeZero t := ⟨ht⟩
  have hprim : (tw θ q).IsPrimitive := by
    have h1 : (DirichletCharacter.changeLevel (Dvd.intro q rfl : t ∣ t * q) θ).conductor = t := by
      rw [DirichletCharacter.conductor_changeLevel]; exact hθ
    have h2 : (DirichletCharacter.changeLevel (Dvd.intro_left t rfl : q ∣ t * q) (qc q)).conductor = q := by
      rw [DirichletCharacter.conductor_changeLevel]; exact qc_prim q hq
    have h3 := cond_mul_coprime (DirichletCharacter.changeLevel (Dvd.intro q rfl : t ∣ t * q) θ)
      (DirichletCharacter.changeLevel (Dvd.intro_left t rfl : q ∣ t * q) (qc q)) (by rw [h1, h2]; exact hc.symm)
    rw [h1, h2] at h3
    exact Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level _) h3
  refine ⟨hprim, ?_, ?_⟩
  · intro h
    have h1 := DirichletCharacter.eq_one_iff_conductor_eq_one.1 h
    rw [(DirichletCharacter.isPrimitive_def _).1 hprim] at h1
    exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_left h1)
  · intro h2
    unfold tw
    rw [mul_pow, ← map_pow, ← map_pow, h2, qc_sq, map_one, map_one, one_mul]

open Finset ArithmeticFunction in
private noncomputable def SS {t : ℕ} (θ : DirichletCharacter ℂ t) (x : ℝ) (q : ℕ) : ℝ :=
  ‖∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * θ (n : ZMod t) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖

open Classical in
private noncomputable def badSet {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) :
    Finset ℕ :=
  P.filter (fun q => ∃ h : Fact q.Prime, ¬ ZeroFreeBox Q (@tw t θ q h))

open Classical in
/- English proof (translation)
Unfold `badSet`. Conclude with `Finset.mem_filter`.
-/
private lemma mem_badSet {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) (q : ℕ) :
    q ∈ badSet θ Q P ↔ q ∈ P ∧ ∃ h : Fact q.Prime, ¬ ZeroFreeBox Q (@tw t θ q h) := by
  unfold badSet; exact Finset.mem_filter

/- English proof (translation)
Unfold `PPset at h`. Rewrite `h` using `[Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨h.2.1, h.2.2.1, h.2.2.2, (Nat.le_floor_iff hX).1 h.1.2⟩`.
-/
private lemma mem_PP {m a q : ℕ} {X : ℝ} (hX : 0 ≤ X) (h : q ∈ PPset m a X) :
    q.Prime ∧ q % m = a % m ∧ X ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X := by
  unfold PPset at h
  rw [Finset.mem_filter, Finset.mem_Icc] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2, (Nat.le_floor_iff hX).1 h.1.2⟩

/- English proof (translation)
Apply `hBC t θ Q _ h1 h2` to reduce the goal to its premises. Introduce `q hq`. Rewrite `hq` using `[mem_badSet]`. Take `⟨hqP, hF, hz⟩` from `hq`. Take `⟨a, b, c⟩` from `hP q hqP`.

Conclude with `⟨hF, a, b, c, hz⟩`.
-/
private lemma badCard {C : ℝ} (hBC : BoxCountHyp C) {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ)
    (P : Finset ℕ) (h1 : θ.IsPrimitive) (h2 : θ ^ 2 = 1)
    (hP : ∀ q ∈ P, q % 4 = 3 ∧ q.Coprime t ∧ ((t * q : ℕ) : ℝ) ≤ Q) :
    ((badSet θ Q P).card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  apply hBC t θ Q _ h1 h2
  intro q hq
  rw [mem_badSet] at hq
  obtain ⟨hqP, hF, hz⟩ := hq
  obtain ⟨a, b, c⟩ := hP q hqP
  exact ⟨hF, a, b, c, hz⟩

/- English proof (translation)
Take `⟨p1, p2, p3⟩` from `twist_is_primitive.2 t θ q h1 hq2 hc`. Use `⟨⟨p1, p3 h2, hQ, ?_⟩, p2⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hz`. Conclude with `hb ((mem_badSet θ Q P q).2 ⟨hqP, hF, hz⟩)`.
-/
private lemma goodOf {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) (q : ℕ)
    [hF : Fact q.Prime] (h1 : θ.IsPrimitive) (h2 : θ ^ 2 = 1) (hq2 : q ≠ 2) (hc : q.Coprime t)
    (hQ : ((t * q : ℕ) : ℝ) ≤ Q) (hqP : q ∈ P) (hb : q ∉ badSet θ Q P) :
    GoodFor Q (tw θ q) ∧ tw θ q ≠ 1 := by
  obtain ⟨p1, p2, p3⟩ := twist_is_primitive.2 t θ q h1 hq2 hc
  refine ⟨⟨p1, p3 h2, hQ, ?_⟩, p2⟩
  by_contra hz
  exact hb ((mem_badSet θ Q P q).2 ⟨hqP, hF, hz⟩)

/- English proof (translation)
Take `⟨t1, t2⟩` from `hBT x Q (t * q) (tw θ q) hx2 hw1 hw2 hg.2 hg.1`. Use `⟨?_, t2⟩` and prove the remaining obligations. Establish `hxz : x ≤ x ^ 400` using `le_self_pow₀ hx1 (by norm_num)`. Rewrite using `[finite_splitting_of_group (t * q) (tw θ q) x (x ^ 400) (by linarith) hxz]`. Establish `hSz : ‖Sz (tw θ q) x (x ^ 400)‖ = SS θ x q`.

Unfold `Sz SS`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`. Rewrite using `[twist_evaluation_formula t θ q n, mul_assoc]`.

Combine the equalities or inequalities in the displayed calculation.
-/
private lemma gBound {ε C x₂ x Q : ℝ} (hBT : BoxTailHyp ε C x₂) (hx2 : x₂ ≤ x) (hx1 : 1 ≤ x)
    (hw1 : x ^ (ε / 6) ≤ Real.log Q) (hw2 : Real.log Q ≤ x ^ (ε / 4))
    (hlast : x ^ (1 / 2 + ε) / 2 + x ^ ε ≤ x ^ (1 / 2 + ε))
    {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime]
    (hg : GoodFor Q (tw θ q) ∧ tw θ q ≠ 1) (hS : SS θ x q ≤ x ^ (1 / 2 + ε) / 2) :
    ‖Gchi (tw θ q) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw θ q)‖ ≤ C * Real.log x := by
  obtain ⟨t1, t2⟩ := hBT x Q (t * q) (tw θ q) hx2 hw1 hw2 hg.2 hg.1
  refine ⟨?_, t2⟩
  have hxz : x ≤ x ^ 400 := le_self_pow₀ hx1 (by norm_num)
  rw [finite_splitting_of_group (t * q) (tw θ q) x (x ^ 400) (by linarith) hxz]
  have hSz : ‖Sz (tw θ q) x (x ^ 400)‖ = SS θ x q := by
    unfold Sz SS
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [twist_evaluation_formula t θ q n, mul_assoc]
  calc ‖- Sz (tw θ q) x (x ^ 400) - (x : ℂ) * tailL (tw θ q) (x ^ 400)‖
      ≤ ‖- Sz (tw θ q) x (x ^ 400)‖ + ‖(x : ℂ) * tailL (tw θ q) (x ^ 400)‖ := norm_sub_le _ _
    _ ≤ x ^ (1 / 2 + ε) := by rw [norm_neg, hSz]; linarith

/- English proof (translation)
The claim follows from `DirichletCharacter.norm_le_one θ _`.
-/
private lemma kappa_norm {t : ℕ} (θ : DirichletCharacter ℂ t) (n : ℕ) : ‖θ (n : ZMod t)‖ ≤ 1 :=
  DirichletCharacter.norm_le_one θ _

/- English proof (translation)
Rewrite using `[Nat.cast_mul, map_mul]`.
-/
private lemma kappa_mul {t : ℕ} (θ : DirichletCharacter ℂ t) (a b : ℕ) :
    θ ((a * b : ℕ) : ZMod t) = θ (a : ZMod t) * θ (b : ZMod t) := by
  rw [Nat.cast_mul, map_mul]

/- English proof (translation)
The claim follows from `DirichletCharacter.isPrimitive_one_level_one`.
-/
private lemma trivial_character_primitive : one1.IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
/- English proof (translation)
The claim follows from `one_pow 2`.
-/
private lemma trivial_character_sq : one1 ^ 2 = 1 := one_pow 2

end Formalism.HermitianLattices.ZeroFreeRegionGL2

namespace Formalism.HermitianLattices.WeakMeanSquareEstimates

open Formalism.HermitianLattices.ZeroFreeRegionGL2

end Formalism.HermitianLattices.WeakMeanSquareEstimates

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

/- English proof (translation)
Introduce `ε C₂ C₂' x₂ C₄ x₄ hε hε1 hC₂ hC₄ hBC hBT hMS`. Take `⟨xa, ha⟩` from `numerical_bound_unit_modulus ε C₂ hε hε1 hC₂`. Take `⟨xb, hb⟩` from `numerical_bound_unit_modulus ε C₄ hε hε1 hC₄`. Take `⟨xc, hc⟩` from `numerical_zero_density_bound ε C₂ hε hε1 hC₂`. Use `⟨max (max (max x₂ x₄) (max xa xb)) (max xc (Real.exp 1)), fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hx2 : x₂ ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx`. Establish `hx4 : x₄ ≤ x` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx`. Establish `hxa : xa ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx`. Establish `hxb : xb ≤ x` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx`. Establish `hxc : xc ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`.

Establish `hxe : Real.exp 1 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Establish `hx1 : 1 ≤ x` using `le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hxe`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hl1 : 1 ≤ Real.log x`. Rewrite using `[← Real.log_exp 1]`.

Conclude with `Real.log_le_log (Real.exp_pos 1) hxe`. Take `⟨a1, a2, a3, -, a5, a6, a7, -, a9, a10⟩` from `ha x hxa`. Take `⟨-, -, -, -, -, -, -, b8, -, -⟩` from `hb x hxb`. Take `⟨c1, c2, -, c4, c5, c6, c7⟩` from `hc x hxc`. Use `set y := x ^ (ε / 5) with hy`.

Use `set t := x ^ (1 / 2 + ε) / 2 with ht`. Use `set V := C₄ * x * Real.log x with hV`. Establish `htpos : 0 < t` using `by have := Real.rpow_pos_of_pos hx0 (1 / 2 + ε); positivity`. Establish `hr : V / t ^ 2 ≤ 1 / 8` using `le_trans b8 a9`. Establish `hX1` using `exp_scale_pos ε x`.

Establish `hX2` using `double_exp_scale_pos ε x`. Establish `hX1one : 1 ≤ X1 ε x` using `Real.one_le_exp (Real.rpow_nonneg hx0.le _)`. Take `⟨hP1, hM1⟩` from `hMS x (X1 ε x) 8 3 (fun n => one1 (n : ZMod 1)) hx4 (by norm_num) (by`. Introduce `p hp hp8`. Use `left`.

Establish `: p ∣ 2 ^ 3` using `by simpa using hp8`. Establish `h2` using `(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)`. Substitute `h2` using the available equality. Conclude with `a2)` after adjusting the coercions. Use the proof step `(by decide) (by norm_num) (by exact_mod_cast a3) a5`.

Use the proof step `(by rw [log_exp_scale]; exact le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _) (one_le_pow₀ hl1)) (kappa_norm one1) (kappa_mul one1)`. Use `set P1 := PPset 8 3 (X1 ε x) with hP1def`. Establish `hP1mem : ∀ q ∈ P1, q.Prime ∧ q % 8 = 3 ∧ X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X1 ε x`. Introduce `q hq`. Take `⟨u1, u2, u3, u4⟩` from `mem_PP hX1.le hq`.

Conclude with `⟨u1, by omega, u3, u4⟩`. Establish `hodd8 : ∀ q : ℕ, q % 2 = 1 → q.Coprime 8`. Introduce `q hq`. Rewrite using `[show (8 : ℕ) = 2 ^ 3 by norm_num]`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises.

Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]`. Use linear arithmetic over natural numbers and integers. Establish `hB1a` using `badCard hBC one1 (8 * X1 ε x) P1 trivial_character_primitive trivial_character_sq (by`. Introduce `q hq`. Take `⟨u1, u2, u3, u4⟩` from `hP1mem q hq`.

Use `⟨by omega, Nat.coprime_one_right q, ?_⟩` and prove the remaining obligations. Use `push_cast`. Use the proof step `linarith)`. Establish `hB1b` using `badCard hBC chi8 (8 * X1 ε x) P1 twist_is_primitive.1.1 twist_is_primitive.1.2 (by`. Introduce `q hq`.

Take `⟨u1, u2, u3, u4⟩` from `hP1mem q hq`. Use `⟨by omega, hodd8 q (by omega), ?_⟩` and prove the remaining obligations. Use `push_cast`. Use the proof step `linarith)`. Establish `hp1pos : (0 : ℝ) < (P1.card : ℝ)` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hX1 _) hP1`.

Take `⟨q₁, hq₁P, hq₁B, hq₁S⟩` from `markov_discard_bound P1 (badSet one1 (8 * X1 ε x) P1 ∪ badSet chi8 (8 * X1 ε x) P1) 1 (fun _ q => SS one1 x q) V t htpos (fun _ => hM1) (by`. Establish `h1 : (((badSet one1 (8 * X1 ε x) P1 ∪ badSet chi8 (8 * X1 ε x) P1).card : ℕ) : ℝ) ≤ ((badSet one1 (8 * X1 ε x) P1).card : ℝ) + ((badSet chi8 (8 * X1 ε x) P1).card : ℝ)`. Conclude with `Finset.card_union_le _ _` after adjusting the coercions. Establish `h2` using `mul_le_mul_of_nonneg_right hr hp1pos.le`. Use `push_cast`.

Use the proof step `linarith)`. Rewrite `hq₁B` using `[Finset.mem_union, not_or]`. Take `⟨q1p, q18, q1lo, q1hi⟩` from `hP1mem q₁ hq₁P`. Establish `hF1 : Fact q₁.Prime` using `⟨q1p⟩`. Establish `q1ne2 : q₁ ≠ 2` using `by omega`.

Establish `q1S : SS one1 x q₁ ≤ t` using `le_trans (le_abs_self _) (hq₁S 0)`. Establish `g1` using `goodOf one1 (8 * X1 ε x) P1 q₁ trivial_character_primitive trivial_character_sq q1ne2 (Nat.coprime_one_right _) (by push_cast; linarith) hq₁P hq₁B.1`. Establish `g2` using `goodOf chi8 (8 * X1 ε x) P1 q₁ twist_is_primitive.1.1 twist_is_primitive.1.2 q1ne2 (hodd8 q₁ (by omega)) (by push_cast; linarith) hq₁P hq₁B.2`. Establish `hy0 : 0 ≤ y` using `by linarith`. Take `⟨a₀, e1, e2, e3, e4, e5, e6, e7⟩` from `class_admissible y (x ^ 400) q₁ a2 q1p q18 (lt_trans a1 q1lo)`.

Use `set M := oddM y q₁ with hMdef`. Establish `hMpos : 0 < M` using `Nat.pos_of_ne_zero (by`. Introduce `h`. Rewrite `e2` using `[h, zero_dvd_iff]`. Use the proof step `omega)`.

Establish `hm0 : (1 / 4) * Real.log x ^ 2 * Real.log ((16 * M : ℕ) : ℝ) ≤ Real.log (X2 ε x)`. Apply `c1` to reduce the goal to its premises. Conclude with `Nat.mul_pos (by norm_num) hMpos` after adjusting the coercions. Use `primorial_upper_bound y q₁ hy0 q1hi` as an intermediate fact. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hMS2 : ∀ {s : ℕ} (θ : DirichletCharacter ℂ s), X2 ε x ^ (9 / 10 : ℝ) ≤ ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ) ∧ (∑ q ∈ PPset (16 * M) a₀ (X2 ε x), SS θ x q ^ 2) ≤ V * ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ)` using `fun {s} θ => hMS x (X2 ε x) (16 * M) a₀ (fun n => θ (n : ZMod s)) hx4 e5 e6 e3 e4 hm0 c2 (le_of_eq (log_double_exp_scale ε x)) (kappa_norm θ) (kappa_mul θ)`. Use `set P2 := PPset (16 * M) a₀ (X2 ε x) with hP2def`. Use `set Q := 8 * X1 ε x * X2 ε x with hQ`. Establish `hP2mem : ∀ d ∈ P2, d.Prime ∧ d % 16 = 7 ∧ M ∣ d + 1 ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧ d.Coprime q₁ ∧ (d : ℝ) ≤ X1 ε x * X2 ε x ∧ (q₁ : ℝ) * d ≤ X1 ε x * X2 ε x`.

Introduce `d hd`. Take `⟨u1, u2, u3, u4⟩` from `mem_PP hX2.le hd`. Take `⟨v1, v2⟩` from `e7 d u2`. Use `⟨u1, v1, v2, u3, u4, ?_, by nlinarith, mul_le_mul q1hi u4 (Nat.cast_nonneg _) hX1.le⟩` and prove the remaining obligations. Rewrite using `[Nat.coprime_primes u1 q1p]`.

Introduce and unpack `rfl`. Establish `h1 : d ∣ d + 1` using `(Dvd.intro _ rfl : d ∣ M).trans v2`. Establish `h2 : d ∣ 1` using `(Nat.dvd_add_right (dvd_refl d)).1 h1`. Conclude with `u1.one_lt.ne' (Nat.dvd_one.1 h2)`. Establish `hXX : 0 < X1 ε x * X2 ε x` using `mul_pos hX1 hX2`.

Establish `hQeq : Q = 8 * (X1 ε x * X2 ε x)` using `by rw [hQ]; ring`. Establish `side1 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime 1 ∧ ((1 * d : ℕ) : ℝ) ≤ Q`. Introduce `d hd`. Take `⟨u1, u2, u3, u4, u5, u6, u7, u8⟩` from `hP2mem d hd`. Conclude with `⟨by omega, Nat.coprime_one_right d, by push_cast; rw [hQeq]; linarith⟩`.

Establish `side2 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime 8 ∧ ((8 * d : ℕ) : ℝ) ≤ Q`. Introduce `d hd`. Take `⟨u1, u2, u3, u4, u5, u6, u7, u8⟩` from `hP2mem d hd`. Conclude with `⟨by omega, hodd8 d (by omega), by push_cast; rw [hQeq]; linarith⟩`. Establish `side3 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime (1 * q₁) ∧ ((1 * q₁ * d : ℕ) : ℝ) ≤ Q`.

Introduce `d hd`. Take `⟨u1, u2, u3, u4, u5, u6, u7, u8⟩` from `hP2mem d hd`. Conclude with `⟨by omega, by rwa [one_mul], by push_cast; rw [hQeq]; linarith⟩`. Establish `side4 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime (8 * q₁) ∧ ((8 * q₁ * d : ℕ) : ℝ) ≤ Q`. Introduce `d hd`.

Take `⟨u1, u2, u3, u4, u5, u6, u7, u8⟩` from `hP2mem d hd`. Conclude with `⟨by omega, Nat.Coprime.mul_right (hodd8 d (by omega)) u6, by push_cast; rw [hQeq]; linarith⟩`. Establish `k1` using `badCard hBC one1 Q P2 trivial_character_primitive trivial_character_sq side1`. Establish `k2` using `badCard hBC chi8 Q P2 twist_is_primitive.1.1 twist_is_primitive.1.2 side2`. Establish `k3` using `badCard hBC (tw one1 q₁) Q P2 g1.1.1 g1.1.2.1 side3`.

Establish `k4` using `badCard hBC (tw chi8 q₁) Q P2 g2.1.1 g2.1.2.1 side4`. Establish `hP2` using `(hMS2 one1).1`. Establish `hp2pos : (0 : ℝ) < (P2.card : ℝ)` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hX2 _) hP2`. Take `⟨d, hdP, hdB, hdS⟩` from `markov_discard_bound P2 ((badSet one1 Q P2 ∪ badSet chi8 Q P2) ∪ (badSet (tw one1 q₁) Q P2 ∪ badSet (tw chi8 q₁) Q P2)) 2 (fun j q => if j = 0 then SS one1 x q else SS (tw one1 q₁) x q) V t htpos (by`. Introduce `j`.

Distinguish the cases in `hj : j = 0`. Simplify using `only [hj, if_true]`. Conclude with `(hMS2 one1).2`. Simplify using `only [hj, if_false]`. Conclude with `(hMS2 (tw one1 q₁)).2)`.

Use the proof step `(by`. Establish `h1 : ((((badSet one1 Q P2 ∪ badSet chi8 Q P2) ∪ (badSet (tw one1 q₁) Q P2 ∪ badSet (tw chi8 q₁) Q P2)).card : ℕ) : ℝ) ≤ (((badSet one1 Q P2).card : ℝ) + ((badSet chi8 Q P2).card : ℝ)) + (((badSet (tw one1 q₁) Q P2).card : ℝ) + ((badSet (tw chi8 q₁) Q P2).card : ℝ))`. Conclude with `(Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _))` after adjusting the coercions. Establish `h2` using `mul_le_mul_of_nonneg_right hr hp2pos.le`. Use `push_cast`.

Use the proof step `linarith)`. Simplify using `only [Finset.mem_union, not_or] at hdB`. Take `⟨⟨nb1, nb2⟩, nb3, nb4⟩` from `hdB`. Take `⟨dp, d16, dM, dlo, dhi, -, -, -⟩` from `hP2mem d hdP`. Establish `hF2 : Fact d.Prime` using `⟨dp⟩`.

Establish `dne2 : d ≠ 2` using `by omega`. Establish `dS0 : SS one1 x d ≤ t` using `le_trans (le_abs_self _) (by simpa using hdS 0)`. Establish `dS1 : SS (tw one1 q₁) x d ≤ t` using `le_trans (le_abs_self _) (by simpa using hdS 1)`. Establish `g3` using `goodOf one1 Q P2 d trivial_character_primitive trivial_character_sq dne2 (side1 d hdP).2.1 (side1 d hdP).2.2 hdP nb1`. Establish `g4` using `goodOf chi8 Q P2 d twist_is_primitive.1.1 twist_is_primitive.1.2 dne2 (side2 d hdP).2.1 (side2 d hdP).2.2 hdP nb2`.

Establish `g5` using `goodOf (tw one1 q₁) Q P2 d g1.1.1 g1.1.2.1 dne2 (side3 d hdP).2.1 (side3 d hdP).2.2 hdP nb3`. Establish `g6` using `goodOf (tw chi8 q₁) Q P2 d g2.1.1 g2.1.2.1 dne2 (side4 d hdP).2.1 (side4 d hdP).2.2 hdP nb4`. Take `⟨sp1, sp2⟩` from `class_splits y q₁ d q1p d16 dM`. Conclude with `⟨q₁, d, hF1, hF2, q18, d16, q1lo, q1hi, dlo, dhi, sp1, sp2, g1.1, g2.1, g3.1, g4.1, g5.1, g6.1, gBound hBT hx2 hx1 a6 a7 c7 one1 q₁ g1 q1S, gBound hBT hx2 hx1 c4 c5 c7 one1 d g3 dS0, gBound hBT hx2 hx1 c4 c5 c7 (tw one1 q₁) d g5 dS1⟩`.
-/
theorem _root_.Formalism.HermitianLattices.WeakMeanSquareEstimates.prime_pair_of_box_and_weak_mean_square_hypotheses : Formalism.HermitianLattices.WeakMeanSquareEstimates.PrimePairOfBoxAndWeakMeanSquareHypotheses := by
  intro ε C₂ C₂' x₂ C₄ x₄ hε hε1 hC₂ hC₄ hBC hBT hMS
  obtain ⟨xa, ha⟩ := numerical_bound_unit_modulus ε C₂ hε hε1 hC₂
  obtain ⟨xb, hb⟩ := numerical_bound_unit_modulus ε C₄ hε hε1 hC₄
  obtain ⟨xc, hc⟩ := numerical_zero_density_bound ε C₂ hε hε1 hC₂
  refine ⟨max (max (max x₂ x₄) (max xa xb)) (max xc (Real.exp 1)), fun x hx => ?_⟩
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx4 : x₄ ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxa : xa ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxc : xc ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx1 : 1 ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hxe
  have hx0 : 0 < x := by linarith
  have hl1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  obtain ⟨a1, a2, a3, -, a5, a6, a7, -, a9, a10⟩ := ha x hxa
  obtain ⟨-, -, -, -, -, -, -, b8, -, -⟩ := hb x hxb
  obtain ⟨c1, c2, -, c4, c5, c6, c7⟩ := hc x hxc
  set y := x ^ (ε / 5) with hy
  set t := x ^ (1 / 2 + ε) / 2 with ht
  set V := C₄ * x * Real.log x with hV
  have htpos : 0 < t := by have := Real.rpow_pos_of_pos hx0 (1 / 2 + ε); positivity
  have hr : V / t ^ 2 ≤ 1 / 8 := le_trans b8 a9
  have hX1 := exp_scale_pos ε x
  have hX2 := double_exp_scale_pos ε x
  have hX1one : 1 ≤ X1 ε x := Real.one_le_exp (Real.rpow_nonneg hx0.le _)

  obtain ⟨hP1, hM1⟩ := hMS x (X1 ε x) 8 3 (fun n => one1 (n : ZMod 1)) hx4 (by norm_num)
    (by
      intro p hp hp8
      left
      have : p ∣ 2 ^ 3 := by simpa using hp8
      have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
      subst h2; exact_mod_cast a2)
    (by decide) (by norm_num) (by exact_mod_cast a3) a5
    (by rw [log_exp_scale]; exact le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _) (one_le_pow₀ hl1)) (kappa_norm one1) (kappa_mul one1)
  set P1 := PPset 8 3 (X1 ε x) with hP1def
  have hP1mem : ∀ q ∈ P1, q.Prime ∧ q % 8 = 3 ∧ X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X1 ε x := by
    intro q hq
    obtain ⟨u1, u2, u3, u4⟩ := mem_PP hX1.le hq
    exact ⟨u1, by omega, u3, u4⟩
  have hodd8 : ∀ q : ℕ, q % 2 = 1 → q.Coprime 8 := by
    intro q hq
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  have hB1a := badCard hBC one1 (8 * X1 ε x) P1 trivial_character_primitive trivial_character_sq (by
    intro q hq
    obtain ⟨u1, u2, u3, u4⟩ := hP1mem q hq
    refine ⟨by omega, Nat.coprime_one_right q, ?_⟩
    push_cast; linarith)
  have hB1b := badCard hBC chi8 (8 * X1 ε x) P1 twist_is_primitive.1.1 twist_is_primitive.1.2 (by
    intro q hq
    obtain ⟨u1, u2, u3, u4⟩ := hP1mem q hq
    refine ⟨by omega, hodd8 q (by omega), ?_⟩
    push_cast; linarith)
  have hp1pos : (0 : ℝ) < (P1.card : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hX1 _) hP1
  obtain ⟨q₁, hq₁P, hq₁B, hq₁S⟩ := markov_discard_bound P1
    (badSet one1 (8 * X1 ε x) P1 ∪ badSet chi8 (8 * X1 ε x) P1) 1 (fun _ q => SS one1 x q) V t htpos
    (fun _ => hM1) (by
      have h1 : (((badSet one1 (8 * X1 ε x) P1 ∪ badSet chi8 (8 * X1 ε x) P1).card : ℕ) : ℝ) ≤
          ((badSet one1 (8 * X1 ε x) P1).card : ℝ) + ((badSet chi8 (8 * X1 ε x) P1).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
      have h2 := mul_le_mul_of_nonneg_right hr hp1pos.le
      push_cast
      linarith)
  rw [Finset.mem_union, not_or] at hq₁B
  obtain ⟨q1p, q18, q1lo, q1hi⟩ := hP1mem q₁ hq₁P
  have hF1 : Fact q₁.Prime := ⟨q1p⟩
  have q1ne2 : q₁ ≠ 2 := by omega
  have q1S : SS one1 x q₁ ≤ t := le_trans (le_abs_self _) (hq₁S 0)
  have g1 := goodOf one1 (8 * X1 ε x) P1 q₁ trivial_character_primitive trivial_character_sq q1ne2 (Nat.coprime_one_right _)
    (by push_cast; linarith) hq₁P hq₁B.1
  have g2 := goodOf chi8 (8 * X1 ε x) P1 q₁ twist_is_primitive.1.1 twist_is_primitive.1.2 q1ne2 (hodd8 q₁ (by omega))
    (by push_cast; linarith) hq₁P hq₁B.2

  have hy0 : 0 ≤ y := by linarith
  obtain ⟨a₀, e1, e2, e3, e4, e5, e6, e7⟩ := class_admissible y (x ^ 400) q₁ a2 q1p q18 (lt_trans a1 q1lo)
  set M := oddM y q₁ with hMdef
  have hMpos : 0 < M := Nat.pos_of_ne_zero (by
    intro h; rw [h, zero_dvd_iff] at e2; omega)
  have hm0 : (1 / 4) * Real.log x ^ 2 * Real.log ((16 * M : ℕ) : ℝ) ≤ Real.log (X2 ε x) := by
    apply c1
    · exact_mod_cast Nat.mul_pos (by norm_num) hMpos
    · have := primorial_upper_bound y q₁ hy0 q1hi
      push_cast
      linarith
  have hMS2 : ∀ {s : ℕ} (θ : DirichletCharacter ℂ s),
      X2 ε x ^ (9 / 10 : ℝ) ≤ ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ) ∧
      (∑ q ∈ PPset (16 * M) a₀ (X2 ε x), SS θ x q ^ 2) ≤ V * ((PPset (16 * M) a₀ (X2 ε x)).card : ℝ) :=
    fun {s} θ => hMS x (X2 ε x) (16 * M) a₀ (fun n => θ (n : ZMod s)) hx4 e5 e6 e3 e4 hm0 c2 (le_of_eq (log_double_exp_scale ε x))
      (kappa_norm θ) (kappa_mul θ)
  set P2 := PPset (16 * M) a₀ (X2 ε x) with hP2def
  set Q := 8 * X1 ε x * X2 ε x with hQ
  have hP2mem : ∀ d ∈ P2, d.Prime ∧ d % 16 = 7 ∧ M ∣ d + 1 ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧
      d.Coprime q₁ ∧ (d : ℝ) ≤ X1 ε x * X2 ε x ∧ (q₁ : ℝ) * d ≤ X1 ε x * X2 ε x := by
    intro d hd
    obtain ⟨u1, u2, u3, u4⟩ := mem_PP hX2.le hd
    obtain ⟨v1, v2⟩ := e7 d u2
    refine ⟨u1, v1, v2, u3, u4, ?_, by nlinarith, mul_le_mul q1hi u4 (Nat.cast_nonneg _) hX1.le⟩
    rw [Nat.coprime_primes u1 q1p]
    rintro rfl
    have h1 : d ∣ d + 1 := (Dvd.intro _ rfl : d ∣ M).trans v2
    have h2 : d ∣ 1 := (Nat.dvd_add_right (dvd_refl d)).1 h1
    exact u1.one_lt.ne' (Nat.dvd_one.1 h2)
  have hXX : 0 < X1 ε x * X2 ε x := mul_pos hX1 hX2
  have hQeq : Q = 8 * (X1 ε x * X2 ε x) := by rw [hQ]; ring
  have side1 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime 1 ∧ ((1 * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, Nat.coprime_one_right d, by push_cast; rw [hQeq]; linarith⟩
  have side2 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime 8 ∧ ((8 * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, hodd8 d (by omega), by push_cast; rw [hQeq]; linarith⟩
  have side3 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime (1 * q₁) ∧ ((1 * q₁ * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, by rwa [one_mul], by push_cast; rw [hQeq]; linarith⟩
  have side4 : ∀ d ∈ P2, d % 4 = 3 ∧ d.Coprime (8 * q₁) ∧ ((8 * q₁ * d : ℕ) : ℝ) ≤ Q := by
    intro d hd
    obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hP2mem d hd
    exact ⟨by omega, Nat.Coprime.mul_right (hodd8 d (by omega)) u6, by push_cast; rw [hQeq]; linarith⟩
  have k1 := badCard hBC one1 Q P2 trivial_character_primitive trivial_character_sq side1
  have k2 := badCard hBC chi8 Q P2 twist_is_primitive.1.1 twist_is_primitive.1.2 side2
  have k3 := badCard hBC (tw one1 q₁) Q P2 g1.1.1 g1.1.2.1 side3
  have k4 := badCard hBC (tw chi8 q₁) Q P2 g2.1.1 g2.1.2.1 side4
  have hP2 := (hMS2 one1).1
  have hp2pos : (0 : ℝ) < (P2.card : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hX2 _) hP2
  obtain ⟨d, hdP, hdB, hdS⟩ := markov_discard_bound P2
    ((badSet one1 Q P2 ∪ badSet chi8 Q P2) ∪ (badSet (tw one1 q₁) Q P2 ∪ badSet (tw chi8 q₁) Q P2)) 2
    (fun j q => if j = 0 then SS one1 x q else SS (tw one1 q₁) x q) V t htpos
    (by
      intro j
      by_cases hj : j = 0
      · simp only [hj, if_true]; exact (hMS2 one1).2
      · simp only [hj, if_false]; exact (hMS2 (tw one1 q₁)).2)
    (by
      have h1 : ((((badSet one1 Q P2 ∪ badSet chi8 Q P2) ∪
          (badSet (tw one1 q₁) Q P2 ∪ badSet (tw chi8 q₁) Q P2)).card : ℕ) : ℝ) ≤
          (((badSet one1 Q P2).card : ℝ) + ((badSet chi8 Q P2).card : ℝ)) +
          (((badSet (tw one1 q₁) Q P2).card : ℝ) + ((badSet (tw chi8 q₁) Q P2).card : ℝ)) := by
        exact_mod_cast (Finset.card_union_le _ _).trans
          (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _))
      have h2 := mul_le_mul_of_nonneg_right hr hp2pos.le
      push_cast
      linarith)
  simp only [Finset.mem_union, not_or] at hdB
  obtain ⟨⟨nb1, nb2⟩, nb3, nb4⟩ := hdB
  obtain ⟨dp, d16, dM, dlo, dhi, -, -, -⟩ := hP2mem d hdP
  have hF2 : Fact d.Prime := ⟨dp⟩
  have dne2 : d ≠ 2 := by omega
  have dS0 : SS one1 x d ≤ t := le_trans (le_abs_self _) (by simpa using hdS 0)
  have dS1 : SS (tw one1 q₁) x d ≤ t := le_trans (le_abs_self _) (by simpa using hdS 1)
  have g3 := goodOf one1 Q P2 d trivial_character_primitive trivial_character_sq dne2 (side1 d hdP).2.1 (side1 d hdP).2.2 hdP nb1
  have g4 := goodOf chi8 Q P2 d twist_is_primitive.1.1 twist_is_primitive.1.2 dne2 (side2 d hdP).2.1 (side2 d hdP).2.2
    hdP nb2
  have g5 := goodOf (tw one1 q₁) Q P2 d g1.1.1 g1.1.2.1 dne2 (side3 d hdP).2.1 (side3 d hdP).2.2 hdP nb3
  have g6 := goodOf (tw chi8 q₁) Q P2 d g2.1.1 g2.1.2.1 dne2 (side4 d hdP).2.1 (side4 d hdP).2.2 hdP nb4
  obtain ⟨sp1, sp2⟩ := class_splits y q₁ d q1p d16 dM
  exact ⟨q₁, d, hF1, hF2, q18, d16, q1lo, q1hi, dlo, dhi, sp1, sp2, g1.1, g2.1, g3.1, g4.1, g5.1, g6.1,
    gBound hBT hx2 hx1 a6 a7 c7 one1 q₁ g1 q1S,
    gBound hBT hx2 hx1 c4 c5 c7 one1 d g3 dS0,
    gBound hBT hx2 hx1 c4 c5 c7 (tw one1 q₁) d g5 dS1⟩

end Formalism.HermitianLattices.ZeroFreeRegionGL2

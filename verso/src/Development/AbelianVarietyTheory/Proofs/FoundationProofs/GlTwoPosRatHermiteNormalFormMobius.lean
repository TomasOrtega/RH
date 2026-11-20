import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HermFN

/- English proof (translation)
Introduce `h0`. Establish `him` using `congrArg Complex.im h0`. Establish `hre` using `congrArg Complex.re h0`. Simplify using `at him hre`. Break down `him with hc | hc` into its components or cases.

Apply the tactic sequence `subst hc; simp at hre; rcases h with h | h <;> simp_all`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma lin_ne_zero (c e : ℤ) (z : ℂ) (hz : 0 < z.im) (h : c ≠ 0 ∨ e ≠ 0) : (c : ℂ) * z + e ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  rcases him with hc | hc
  · subst hc; simp at hre; rcases h with h | h <;> simp_all
  · linarith

/- English proof (translation)
Use `⟨∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => (ent g i j).den_pos))`. Introduce `i j`. Establish `hdv : (ent g i j).den ∣ ∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den` using `(Finset.dvd_prod_of_mem (fun j => (ent g i j).den) (Finset.mem_univ j)).trans (Finset.dvd_prod_of_mem (fun i => ∏ j : Fin 2, (ent g i j).den) (Finset.mem_univ i))`. Take `⟨k, hk⟩` from `hdv`.

Use `⟨k * (ent g i j).num, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Use `Rat.mul_den_eq_num (ent g i j)` as an intermediate fact. Use `push_cast`. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma common_den (g : GQ) : ∃ N : ℕ, 0 < N ∧ ∀ i j, ∃ z : ℤ, (N : ℚ) * ent g i j = z := by
  refine ⟨∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den, ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => (ent g i j).den_pos))
  · intro i j
    have hdv : (ent g i j).den ∣ ∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den :=
      (Finset.dvd_prod_of_mem (fun j => (ent g i j).den) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j : Fin 2, (ent g i j).den) (Finset.mem_univ i))
    obtain ⟨k, hk⟩ := hdv
    refine ⟨k * (ent g i j).num, ?_⟩
    rw [hk]
    have := Rat.mul_den_eq_num (ent g i j)
    push_cast
    rw [← this]; ring

/- English proof (translation)
Rewrite using `[hpC, ← hq'C]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma upper_step (p p' x b dd q : ℤ) (a : ℕ) (τ : ℂ) (hd0 : (dd : ℂ) ≠ 0) (hpC : (p : ℂ) = a * p')
    (hq'C : (p' : ℂ) * b + x * dd = q) :
    ((p' : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((x : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd := by
  rw [hpC, ← hq'C]; field_simp; ring

/- English proof (translation)
Establish `hD' : τ * (C : ℂ) + D ≠ 0` using `by rwa [mul_comm]`. Rewrite using `[eq_div_iff (mul_ne_zero hN hD)]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma left_step (m0 m1 A B C D : ℤ) (N : ℕ) (τ : ℂ) (hN : (N : ℂ) ≠ 0) (hD : (C : ℂ) * τ + D ≠ 0) :
    (m0 : ℂ) / N * (((A : ℂ) * τ + B) / ((C : ℂ) * τ + D)) + (m1 : ℂ) / N =
      (((m0 * A + m1 * C : ℤ) : ℂ) * τ + ((m0 * B + m1 * D : ℤ) : ℂ)) / (N * ((C : ℂ) * τ + D)) := by
  have hD' : τ * (C : ℂ) + D ≠ 0 := by rwa [mul_comm]
  rw [eq_div_iff (mul_ne_zero hN hD)]
  push_cast
  field_simp
  ring

end GlobalTheory.HermFN

namespace GlobalTheory.HermFN

/- English proof (translation)
Take `⟨N, hN, hm⟩` from `common_den g`. Use `choose m hm using hm`. Establish `hdetg : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0`. Establish `h` using `g.2`. Rewrite `h` using `[Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`.

Conclude with `h`. Use `set nI : ℤ := m 0 0 * m 1 1 - m 0 1 * m 1 0 with hnI`. Establish `hn : 0 < nI`. Establish `hq : (nI : ℚ) = (N : ℚ) ^ 2 * (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0)`. Rewrite using `[hnI]`.

Use `push_cast`. Rewrite using `[← hm 0 0, ← hm 0 1, ← hm 1 0, ← hm 1 1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hNq : (0 : ℚ) < N` using `by exact_mod_cast hN`. Establish `: (0 : ℚ) < nI` using `by rw [hq]; positivity`.

Conclude with `this` after adjusting the coercions. Use `⟨nI.toNat, by omega, ?_⟩` and prove the remaining obligations. Introduce `γ₀`. Establish `hdet0 : γ₀ 0 0 * γ₀ 1 1 - γ₀ 0 1 * γ₀ 1 0 = 1`. Use `γ₀.2` as an intermediate fact.

Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Use `set p : ℤ := m 0 0 * γ₀ 0 0 + m 0 1 * γ₀ 1 0 with hp_def`. Use `set r : ℤ := m 1 0 * γ₀ 0 0 + m 1 1 * γ₀ 1 0 with hr_def`. Use `set q : ℤ := m 0 0 * γ₀ 0 1 + m 0 1 * γ₀ 1 1 with hq_def`. Use `set s : ℤ := m 1 0 * γ₀ 0 1 + m 1 1 * γ₀ 1 1 with hs_def`.

Establish `hps : p * s - q * r = nI`. Rewrite using `[hp_def, hr_def, hq_def, hs_def, hnI]`. Take the linear combination `(m 0 0 * m 1 1 - m 0 1 * m 1 0) * hdet0`. Establish `hpr : p ≠ 0 ∨ r ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Rewrite `hps` using `[h.1, h.2]`. Use linear arithmetic over natural numbers and integers. Establish `hrs : r ≠ 0 ∨ s ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Rewrite `hps` using `[h.1, h.2]`. Use linear arithmetic over natural numbers and integers. Use `set a : ℕ := Int.gcd p r with ha_def`. Establish `ha : 0 < a` using `Int.gcd_pos_iff.mpr hpr`.

Use `set p' : ℤ := p / a`. Use `set r' : ℤ := r / a`. Establish `hp : p = a * p'` using `(Int.mul_ediv_cancel' (Int.gcd_dvd_left p r)).symm`. Establish `hr : r = a * r'` using `(Int.mul_ediv_cancel' (Int.gcd_dvd_right p r)).symm`. Establish `cop : IsCoprime p' r'` using `Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd ha)`.

Take `⟨γ, h0, h1⟩` from `cop.exists_SL2_col 0`. Establish `hγ : p' * γ 1 1 - γ 0 1 * r' = 1`. Use `γ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two, h0, h1]`. Take the linear combination `this`.

Use `set b : ℤ := γ 1 1 * q - γ 0 1 * s with hb_def`. Use `set dd : ℤ := p' * s - r' * q with hdd_def`. Establish `had : (a : ℤ) * dd = nI`. Rewrite using `[hdd_def, ← hps]`. Take the linear combination `(-s) * hp + q * hr`.

Establish `hd : 0 < dd`. Establish `: (0 : ℤ) < a` using `by exact_mod_cast ha`. Use the polynomial consequences of the given equalities and inequalities. Establish `hq' : p' * b + γ 0 1 * dd = q` using `by rw [hb_def, hdd_def]; linear_combination q * hγ`. Establish `hs' : r' * b + γ 1 1 * dd = s` using `by rw [hb_def, hdd_def]; linear_combination s * hγ`.

Use `⟨γ, a, dd.toNat, b, ?_, ?_⟩` and prove the remaining obligations. Use `zify`. Rewrite using `[Int.toNat_of_nonneg hd.le, Int.toNat_of_nonneg hn.le]`. Conclude with `had`. Introduce `τ`.

Establish `hz : 0 < (τ : ℂ).im` using `τ.im_pos`. Establish `hNC : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `haC : (a : ℂ) ≠ 0` using `by exact_mod_cast ha.ne'`. Establish `hdC : ((dd.toNat : ℕ) : ℂ) = (dd : ℂ)`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg hd.le]`.

Establish `hd0 : (dd : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hc : ∀ i j, ((ent g i j : ℚ) : ℂ) = (m i j : ℂ) / N`. Introduce `i j`. Establish `: ent g i j = (m i j : ℚ) / N`. Rewrite using `[← hm i j]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hD0 : ((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ) ≠ 0`.

Apply `lin_ne_zero _ _ _ hz` to reduce the goal to its premises. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Rewrite `hdet0` using `[h.1, h.2]`. Simplify using `at hdet0`.

Establish `hRS : (r : ℂ) * τ + s ≠ 0` using `lin_ne_zero r s _ hz hrs`. Establish `hpC : (p : ℂ) = a * p'` using `by exact_mod_cast hp`. Establish `hrC : (r : ℂ) = a * r'` using `by exact_mod_cast hr`. Establish `hq'C : (p' : ℂ) * b + γ 0 1 * dd = q` using `by exact_mod_cast hq'`. Establish `hs'C : (r' : ℂ) * b + γ 1 1 * dd = s` using `by exact_mod_cast hs'`.

Rewrite using `[UpperHalfPlane.coe_specialLinearGroup_apply, hdC]`. Simplify using `only [mob, hc, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]`. Establish `eL : ((m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N) / ((m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N) = ((p …`. Establish `e1 : (m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N = ((p : ℂ) * τ + q) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ)))`. Conclude with `left_step (m 0 0) (m 0 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0`.

Establish `e2 : (m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N = ((r : ℂ) * τ + s) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ)))`. Conclude with `left_step (m 1 0) (m 1 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0`. Rewrite using `[e1, e2, div_div_div_cancel_right₀ (mul_ne_zero hNC hD0)]`. Establish `eR : ((γ 0 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 0 1 : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd`. Rewrite using `[h0]`.

Conclude with `upper_step p p' (γ 0 1) b dd q a τ hd0 hpC hq'C`. Establish `eR2 : ((γ 1 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 1 1 : ℤ) : ℂ) = ((r : ℂ) * τ + s) / dd`. Rewrite using `[h1]`. Conclude with `upper_step r r' (γ 1 1) b dd s a τ hd0 hrC hs'C`. Establish `hofSL : ∀ i j, ((ent (ofSL γ) i j : ℚ) : ℂ) = ((γ i j : ℤ) : ℂ)`.

Introduce `i j`. Use `show (((γ i j : ℤ) : ℚ) : ℂ) = _`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [hofSL]`.

Rewrite using `[eL, eR, eR2, div_div_div_cancel_right₀ hd0]`.
-/
theorem hermite (g : GQ) : ∃ n : ℕ, 0 < n ∧ ∀ γ₀ : SL(2, ℤ), ∃ (γ : SL(2, ℤ)) (a d : ℕ) (b : ℤ), a * d = n ∧
    ∀ τ : ℍ, mob g ((γ₀ • τ : ℍ) : ℂ) = mob (ofSL γ) (((a : ℂ) * τ + b) / d) := by
  obtain ⟨N, hN, hm⟩ := common_den g
  choose m hm using hm
  have hdetg : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
    have h := g.2
    rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
    exact h
  set nI : ℤ := m 0 0 * m 1 1 - m 0 1 * m 1 0 with hnI
  have hn : 0 < nI := by
    have hq : (nI : ℚ) = (N : ℚ) ^ 2 * (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0) := by
      rw [hnI]; push_cast; rw [← hm 0 0, ← hm 0 1, ← hm 1 0, ← hm 1 1]; ring
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have : (0 : ℚ) < nI := by rw [hq]; positivity
    exact_mod_cast this
  refine ⟨nI.toNat, by omega, ?_⟩
  intro γ₀
  have hdet0 : γ₀ 0 0 * γ₀ 1 1 - γ₀ 0 1 * γ₀ 1 0 = 1 := by
    have := γ₀.2; rwa [Matrix.det_fin_two] at this
  set p : ℤ := m 0 0 * γ₀ 0 0 + m 0 1 * γ₀ 1 0 with hp_def
  set r : ℤ := m 1 0 * γ₀ 0 0 + m 1 1 * γ₀ 1 0 with hr_def
  set q : ℤ := m 0 0 * γ₀ 0 1 + m 0 1 * γ₀ 1 1 with hq_def
  set s : ℤ := m 1 0 * γ₀ 0 1 + m 1 1 * γ₀ 1 1 with hs_def
  have hps : p * s - q * r = nI := by
    rw [hp_def, hr_def, hq_def, hs_def, hnI]; linear_combination (m 0 0 * m 1 1 - m 0 1 * m 1 0) * hdet0
  have hpr : p ≠ 0 ∨ r ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hps; omega
  have hrs : r ≠ 0 ∨ s ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hps; omega
  set a : ℕ := Int.gcd p r with ha_def
  have ha : 0 < a := Int.gcd_pos_iff.mpr hpr
  set p' : ℤ := p / a
  set r' : ℤ := r / a
  have hp : p = a * p' := (Int.mul_ediv_cancel' (Int.gcd_dvd_left p r)).symm
  have hr : r = a * r' := (Int.mul_ediv_cancel' (Int.gcd_dvd_right p r)).symm
  have cop : IsCoprime p' r' := Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd ha)
  obtain ⟨γ, h0, h1⟩ := cop.exists_SL2_col 0
  have hγ : p' * γ 1 1 - γ 0 1 * r' = 1 := by
    have := γ.2; rw [Matrix.det_fin_two, h0, h1] at this; linear_combination this
  set b : ℤ := γ 1 1 * q - γ 0 1 * s with hb_def
  set dd : ℤ := p' * s - r' * q with hdd_def
  have had : (a : ℤ) * dd = nI := by
    rw [hdd_def, ← hps]; linear_combination (-s) * hp + q * hr
  have hd : 0 < dd := by
    have : (0 : ℤ) < a := by exact_mod_cast ha
    nlinarith
  have hq' : p' * b + γ 0 1 * dd = q := by rw [hb_def, hdd_def]; linear_combination q * hγ
  have hs' : r' * b + γ 1 1 * dd = s := by rw [hb_def, hdd_def]; linear_combination s * hγ
  refine ⟨γ, a, dd.toNat, b, ?_, ?_⟩
  · zify; rw [Int.toNat_of_nonneg hd.le, Int.toNat_of_nonneg hn.le]; exact had
  · intro τ
    have hz : 0 < (τ : ℂ).im := τ.im_pos
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hdC : ((dd.toNat : ℕ) : ℂ) = (dd : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hd.le]
    have hd0 : (dd : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hc : ∀ i j, ((ent g i j : ℚ) : ℂ) = (m i j : ℂ) / N := by
      intro i j
      have : ent g i j = (m i j : ℚ) / N := by
        rw [← hm i j]; field_simp
      rw [this]; push_cast; rfl
    have hD0 : ((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ) ≠ 0 := by
      apply lin_ne_zero _ _ _ hz
      by_contra h; push_neg at h; rw [h.1, h.2] at hdet0; simp at hdet0
    have hRS : (r : ℂ) * τ + s ≠ 0 := lin_ne_zero r s _ hz hrs
    have hpC : (p : ℂ) = a * p' := by exact_mod_cast hp
    have hrC : (r : ℂ) = a * r' := by exact_mod_cast hr
    have hq'C : (p' : ℂ) * b + γ 0 1 * dd = q := by exact_mod_cast hq'
    have hs'C : (r' : ℂ) * b + γ 1 1 * dd = s := by exact_mod_cast hs'
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, hdC]
    simp only [mob, hc, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    have eL : ((m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N) /
        ((m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N)
        = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + s) := by
      have e1 : (m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N
          = ((p : ℂ) * τ + q) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) := by
        exact left_step (m 0 0) (m 0 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0
      have e2 : (m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N
          = ((r : ℂ) * τ + s) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) := by
        exact left_step (m 1 0) (m 1 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0
      rw [e1, e2, div_div_div_cancel_right₀ (mul_ne_zero hNC hD0)]
    have eR : ((γ 0 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 0 1 : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd := by
      rw [h0]; exact upper_step p p' (γ 0 1) b dd q a τ hd0 hpC hq'C
    have eR2 : ((γ 1 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 1 1 : ℤ) : ℂ) = ((r : ℂ) * τ + s) / dd := by
      rw [h1]; exact upper_step r r' (γ 1 1) b dd s a τ hd0 hrC hs'C
    have hofSL : ∀ i j, ((ent (ofSL γ) i j : ℚ) : ℂ) = ((γ i j : ℤ) : ℂ) := by
      intro i j; show (((γ i j : ℤ) : ℚ) : ℂ) = _; push_cast; rfl
    simp only [hofSL]
    rw [eL, eR, eR2, div_div_div_cancel_right₀ hd0]

end GlobalTheory.HermFN

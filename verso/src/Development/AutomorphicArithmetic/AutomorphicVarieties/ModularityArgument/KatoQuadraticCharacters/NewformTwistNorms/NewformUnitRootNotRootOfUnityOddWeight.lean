import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformNormCoeffPrimeLeOfNotDvdLevel

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

/- English proof (translation)
Establish `h1 : ‖z‖ ^ n = 1` using `by rw [← norm_pow, h, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 h1`.
-/
theorem norm_eq_one_of_pow_eq_one' {R : Type} [NormedDivisionRing R] {z : R} {n : ℕ} (hn : 0 < n)
    (h : z ^ n = 1) : ‖z‖ = 1 := by
  have h1 : ‖z‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 h1

/- English proof (translation)
Use `haveI : NeZero M := ⟨hM.ne'⟩`. Use `⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, ?_⟩` and prove the remaining obligations. Rewrite using `[← ZMod.coe_unitOfCoprime l h, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]`.
-/
theorem dirichlet_pow_card_eq_one {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) (l : ℕ) (h : l.Coprime M) :
    ∃ n : ℕ, 0 < n ∧ χ (l : ZMod M) ^ n = 1 := by
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, ?_⟩
  rw [← ZMod.coe_unitOfCoprime l h, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one,
    map_one]

/- English proof (translation)
Establish `hL0 : 0 < L` using `by linarith`. Use `set s := Real.sqrt L with hs`. Establish `hs0 : 0 ≤ s` using `Real.sqrt_nonneg L`. Establish `hss : s * s = L` using `Real.mul_self_sqrt hL0.le`. Establish `h1 : L ^ (((2 * e + 1 : ℕ) : ℝ) / 2) = L ^ e * s`.

Rewrite using `[hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast L e, ← Real.rpow_add hL0]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : L ^ (((2 * e + 1 : ℕ) : ℝ) / 2 - 1) = L ^ e * s / L`.

Rewrite using `[Real.rpow_sub hL0, Real.rpow_one, h1]`. Rewrite using `[h1, h2]`. Use `set N := L ^ e with hN`. Establish `hNL : L ≤ N`. Rewrite using `[hN]; calc L = L ^ 1 := (pow_one L).symm _ ≤ L ^ e := pow_le_pow_right₀ (by linarith) he`.

Establish `hsL : s < L - 1` using `by nlinarith`. Establish `key : N * s * (L + 1) < L * (N ^ 2 - 1)`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hNL) (show 0 ≤ L * (N + L) - (L + 1) * s by nlinarith), mul_pos (mul_pos (show (0:ℝ) < L + 1 by linarith) hL0) (show 0 < L - 1 - s by linarith)]`. Establish `: N * s + N * s / L = N * s * (L + 1) / L` using `by field_simp`. Rewrite using `[this, div_lt_iff₀ hL0]`.

Establish `: L ^ (2 * e) = N ^ 2` using `by rw [hN, ← pow_mul, mul_comm]`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hecke_gap (L : ℝ) (hL : 3 ≤ L) (e : ℕ) (he : 1 ≤ e) :
    L ^ (((2 * e + 1 : ℕ) : ℝ) / 2) + L ^ (((2 * e + 1 : ℕ) : ℝ) / 2 - 1) < L ^ (2 * e) - 1 := by
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg L
  have hss : s * s = L := Real.mul_self_sqrt hL0.le
  have h1 : L ^ (((2 * e + 1 : ℕ) : ℝ) / 2) = L ^ e * s := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast L e, ← Real.rpow_add hL0]
    congr 1; push_cast; ring
  have h2 : L ^ (((2 * e + 1 : ℕ) : ℝ) / 2 - 1) = L ^ e * s / L := by
    rw [Real.rpow_sub hL0, Real.rpow_one, h1]
  rw [h1, h2]
  set N := L ^ e with hN
  have hNL : L ≤ N := by
    rw [hN]; calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ e := pow_le_pow_right₀ (by linarith) he
  have hsL : s < L - 1 := by nlinarith
  have key : N * s * (L + 1) < L * (N ^ 2 - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hNL) (show 0 ≤ L * (N + L) - (L + 1) * s by nlinarith),
      mul_pos (mul_pos (show (0:ℝ) < L + 1 by linarith) hL0) (show 0 < L - 1 - s by linarith)]
  have : N * s + N * s / L = N * s * (L + 1) / L := by field_simp
  rw [this, div_lt_iff₀ hL0]
  have : L ^ (2 * e) = N ^ 2 := by rw [hN, ← pow_mul, mul_comm]
  rw [this]; linarith

/- English proof (translation)
Use `h.eq_zero` as an intermediate fact. Simplify using `only [Newform.heckePoly, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at this`. Take the linear combination `-this`.
-/
theorem heckePoly_root_eq {k : ℕ} (g : Newform k) (p : ℕ) (α : ℂ) (h : (g.heckePoly p).IsRoot α) :
    g.a p * α = α ^ 2 + g.χ (p : ZMod g.M) * (p : ℂ) ^ (k - 1) := by
  have := h.eq_zero
  simp only [Newform.heckePoly, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] at this
  linear_combination -this

/- English proof (translation)
Introduce `l _ ι e g α hl2 he hdiv hroot hα`. Establish `hp : l.Prime` using `Fact.out`. Establish `hcop : l.Coprime g.M` using `(Nat.Prime.coprime_iff_not_dvd hp).2 hdiv`. Take `⟨n, hn, hχn⟩` from `dirichlet_pow_card_eq_one g.pos g.χ l hcop`. Establish `hrel` using `heckePoly_root_eq g l α hroot`.

Establish `hk : 2 * e + 1 - 1 = 2 * e` using `by omega`. Rewrite `hrel` using `[hk]`. Use `set c := g.χ (l : ZMod g.M) with hc`. Establish `hα0 : α ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hα`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hA0 : ι.symm α ≠ 0` using `by rw [Ne, map_eq_zero_iff _ ι.symm.injective]; exact hα0`. Establish `hrel' : ι.symm (g.a l) = ι.symm α + ι.symm c * (l : Qbar l) ^ (2 * e) / ι.symm α`. Clear the denominators using the available nonvanishing facts.

Use `congrArg ι.symm hrel` as an intermediate fact. Simplify using `only [map_mul, map_add, map_pow, map_natCast] at this`. Take the linear combination `this`. Establish `hcn : ‖ι.symm c‖ = 1` using `norm_eq_one_of_pow_eq_one' hn (by rw [← map_pow, hχn, map_one])`. Establish `hln : ‖(l : Qbar l)‖ < 1`.

Establish `h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l])` using `by simp`. Rewrite using `[h, PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_p_lt_one`. Establish `hB : ‖ι.symm c * (l : Qbar l) ^ (2 * e) / ι.symm α‖ < 1`. Rewrite using `[norm_div, norm_mul, norm_pow, hcn, hα, one_mul, div_one]`.

Conclude with `pow_lt_one₀ (norm_nonneg _) hln (by omega)`. Rewrite using `[hrel', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hα]; exact hB.ne'), hα]`. Conclude with `max_eq_left hB.le`. Introduce `m hm hαm`. Establish `hαn : ‖α‖ = 1` using `norm_eq_one_of_pow_eq_one' hm hαm`.

Establish `hcn : ‖c‖ = 1` using `norm_eq_one_of_pow_eq_one' hn hχn`. Establish `hb` using `hbd (2 * e + 1) g l hp hdiv`. Establish `ha : g.a l = α + c * (l : ℂ) ^ (2 * e) / α` using `by field_simp; linear_combination hrel`. Establish `hlow : (l : ℝ) ^ (2 * e) - 1 ≤ ‖g.a l‖`. Establish `h1 : ‖c * (l : ℂ) ^ (2 * e) / α‖ = (l : ℝ) ^ (2 * e)`.

Rewrite using `[norm_div, norm_mul, norm_pow, hcn, hαn, one_mul, div_one, Complex.norm_natCast]`. Establish `h2` using `norm_sub_norm_le (c * (l : ℂ) ^ (2 * e) / α) (-α)`. Rewrite `h2` using `[h1, norm_neg, hαn, sub_neg_eq_add, add_comm]`. Rewrite using `[ha]`. Conclude with `h2`.

Establish `hl3 : (3 : ℝ) ≤ l`. Use `hp.two_le` as an intermediate fact. Establish `: 3 ≤ l` using `by omega`. Conclude with `this` after adjusting the coercions. Use `hecke_gap (l : ℝ) hl3 e he` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem root_facts_of_bound
    (hbd : ∀ (k : ℕ) (g : Newform k) (p : ℕ), p.Prime → ¬ p ∣ g.M →
      ‖g.a p‖ ≤ (p : ℝ) ^ ((k : ℝ) / 2) + (p : ℝ) ^ ((k : ℝ) / 2 - 1)) :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M →
      (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 := by
  intro l _ ι e g α hl2 he hdiv hroot hα
  have hp : l.Prime := Fact.out
  have hcop : l.Coprime g.M := (Nat.Prime.coprime_iff_not_dvd hp).2 hdiv
  obtain ⟨n, hn, hχn⟩ := dirichlet_pow_card_eq_one g.pos g.χ l hcop
  have hrel := heckePoly_root_eq g l α hroot
  have hk : 2 * e + 1 - 1 = 2 * e := by omega
  rw [hk] at hrel
  set c := g.χ (l : ZMod g.M) with hc
  have hα0 : α ≠ 0 := by
    rintro rfl; simp at hα
  refine ⟨?_, ?_⟩
  ·
    have hA0 : ι.symm α ≠ 0 := by rw [Ne, map_eq_zero_iff _ ι.symm.injective]; exact hα0
    have hrel' : ι.symm (g.a l) = ι.symm α + ι.symm c * (l : Qbar l) ^ (2 * e) / ι.symm α := by
      field_simp
      have := congrArg ι.symm hrel
      simp only [map_mul, map_add, map_pow, map_natCast] at this
      linear_combination this
    have hcn : ‖ι.symm c‖ = 1 :=
      norm_eq_one_of_pow_eq_one' hn (by rw [← map_pow, hχn, map_one])
    have hln : ‖(l : Qbar l)‖ < 1 := by
      have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
      rw [h, PadicAlgCl.norm_extends]; exact Padic.norm_p_lt_one
    have hB : ‖ι.symm c * (l : Qbar l) ^ (2 * e) / ι.symm α‖ < 1 := by
      rw [norm_div, norm_mul, norm_pow, hcn, hα, one_mul, div_one]
      exact pow_lt_one₀ (norm_nonneg _) hln (by omega)
    rw [hrel', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hα]; exact hB.ne'), hα]
    exact max_eq_left hB.le
  ·
    intro m hm hαm
    have hαn : ‖α‖ = 1 := norm_eq_one_of_pow_eq_one' hm hαm
    have hcn : ‖c‖ = 1 := norm_eq_one_of_pow_eq_one' hn hχn
    have hb := hbd (2 * e + 1) g l hp hdiv
    have ha : g.a l = α + c * (l : ℂ) ^ (2 * e) / α := by
      field_simp; linear_combination hrel
    have hlow : (l : ℝ) ^ (2 * e) - 1 ≤ ‖g.a l‖ := by
      have h1 : ‖c * (l : ℂ) ^ (2 * e) / α‖ = (l : ℝ) ^ (2 * e) := by
        rw [norm_div, norm_mul, norm_pow, hcn, hαn, one_mul, div_one, Complex.norm_natCast]
      have h2 := norm_sub_norm_le (c * (l : ℂ) ^ (2 * e) / α) (-α)
      rw [h1, norm_neg, hαn, sub_neg_eq_add, add_comm] at h2
      rw [ha]; exact h2
    have hl3 : (3 : ℝ) ≤ l := by
      have := hp.two_le
      have : 3 ≤ l := by omega
      exact_mod_cast this
    have := hecke_gap (l : ℝ) hl3 e he
    linarith

/- English proof (translation)
The claim follows from `root_facts_of_bound GlobalTheory.T.newform_norm_coeff_prime_le_of_not_dvd_level`.
-/
theorem root_facts :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M →
      (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 :=
  root_facts_of_bound GlobalTheory.T.newform_norm_coeff_prime_le_of_not_dvd_level

end GlobalTheory.Ord2

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Ord2.root_facts | exact GlobalTheory.Ord2.root_facts | (intros; apply GlobalTheory.Ord2.root_facts <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M → (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 := by
  first | exact @GlobalTheory.Ord2.root_facts | exact GlobalTheory.Ord2.root_facts | (intros; apply GlobalTheory.Ord2.root_facts <;> assumption)

end

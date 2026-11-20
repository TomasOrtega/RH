import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowAdditive

noncomputable section

namespace GlobalTheory.PMonE.WinBounds

open GlobalTheory.PMonE

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Function.iterate_succ_apply', pow_succ', pow_mul]`. Establish `h` using `frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[m] x)`.

Rewrite `h` using `[frobenius_def]`. Rewrite using `[h, ih]`.
-/
theorem pow_iter_frobeniusEquiv_symm {F : Type} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (x : F) (m : ℕ) : (((frobeniusEquiv F p).symm)^[m] x) ^ p ^ m = x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul]
    have h := frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[m] x)
    rw [frobenius_def] at h
    rw [h, ih]

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

/- English proof (translation)
Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).pos`. Unfold `pw`. Use `split_ifs with hk`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le hk`. Rewrite using `[norm_pow, Int.toNat_natCast, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]`.

Take `⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ)` from `⟨(-k).toNat, by omega⟩`. Substitute `hm` using the available equality. Rewrite using `[neg_neg, Int.toNat_natCast]`. Establish `hy` using `pow_iter_frobeniusEquiv_symm p x m`. Use `conv_rhs => rw [← hy]`.

Rewrite using `[norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_pow, zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity), Real.rpow_one]`.
-/
theorem norm_pw (k : ℤ) (x : F) : ‖pw p k x‖ = ‖x‖ ^ ((p : ℝ) ^ k) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold pw
  split_ifs with hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [norm_pow, Int.toNat_natCast, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hm
    rw [neg_neg, Int.toNat_natCast]
    have hy := pow_iter_frobeniusEquiv_symm p x m
    conv_rhs => rw [← hy]
    rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_pow, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (by positivity), Real.rpow_one]

/- English proof (translation)
Unfold `term`. Rewrite using `[norm_mul, norm_mul, norm_zpow, hϖ, norm_pw, inv_zpow', neg_neg]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem norm_term (k : ℕ) (ϖ : F) (hϖ : ‖ϖ‖ = (p : ℝ)⁻¹) (lam π : Fin (k + 1) → F) (r j : Fin (k + 1)) (n : ℤ) :
    ‖term p ϖ lam π r j n‖ = ‖lam j‖ * (p : ℝ) ^ n * ‖π j‖ ^ ((p : ℝ) ^ (((r : ℕ) : ℤ) + n * ((k : ℤ) + 1))) := by
  unfold term
  rw [norm_mul, norm_mul, norm_zpow, hϖ, norm_pw, inv_zpow', neg_neg]
  push_cast
  rfl

def idx (k : ℕ) (J : ℤ) : Fin (k + 1) :=
  ⟨(J % ((k : ℤ) + 1)).toNat, by
    have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos J (show (0 : ℤ) < (k : ℤ) + 1 by omega)
    omega⟩

/- English proof (translation)
Establish `hj` using `j.isLt`. Establish `h0 : ((j : ℕ) : ℤ) / ((k : ℤ) + 1) = 0` using `Int.ediv_eq_zero_of_lt (by omega) (by omega)`. Establish `h1 : ((j : ℕ) : ℤ) % ((k : ℤ) + 1) = j` using `Int.emod_eq_of_lt (by omega) (by omega)`. Prove the components needed by the constructor for the conclusion. Use `ext`.

Simplify using `[idx, Int.add_mul_emod_self_left, h1]`. Rewrite using `[Int.add_mul_ediv_left _ _ (by omega), h0, zero_add]`.
-/
theorem idx_spec (k : ℕ) (j : Fin (k + 1)) (m : ℤ) :
    idx k (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = j ∧ (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) / ((k : ℤ) + 1) = m := by
  have hj := j.isLt
  have h0 : ((j : ℕ) : ℤ) / ((k : ℤ) + 1) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have h1 : ((j : ℕ) : ℤ) % ((k : ℤ) + 1) = j := Int.emod_eq_of_lt (by omega) (by omega)
  constructor
  · ext
    simp [idx, Int.add_mul_emod_self_left, h1]
  · rw [Int.add_mul_ediv_left _ _ (by omega), h0, zero_add]

/- English proof (translation)
Use `⟨idx k J, J / ((k : ℤ) + 1), ?_⟩` and prove the remaining obligations. Establish `h1` using `Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)`. Establish `h2 : J % ((k : ℤ) + 1) = J - ((k : ℤ) + 1) * (J / ((k : ℤ) + 1))` using `Int.emod_def _ _`. Use `show J = (((J % ((k : ℤ) + 1)).toNat : ℕ) : ℤ) + _`. Rewrite using `[Int.toNat_of_nonneg h1]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem decomp (k : ℕ) (J : ℤ) : ∃ j : Fin (k + 1), ∃ m : ℤ, J = ((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
  refine ⟨idx k J, J / ((k : ℤ) + 1), ?_⟩
  have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
  have h2 : J % ((k : ℤ) + 1) = J - ((k : ℤ) + 1) * (J / ((k : ℤ) + 1)) := Int.emod_def _ _
  show J = (((J % ((k : ℤ) + 1)).toNat : ℕ) : ℤ) + _
  rw [Int.toNat_of_nonneg h1]
  linarith

def aW (k : ℕ) (lam : Fin (k + 1) → F) (J : ℤ) : ℝ :=
  ‖lam (idx k J)‖ * (p : ℝ) ^ (-(J / ((k : ℤ) + 1)))

def rW (k : ℕ) (π : Fin (k + 1) → F) (J : ℤ) : ℝ :=
  ‖π (idx k J)‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * (J / ((k : ℤ) + 1)))))

/- English proof (translation)
Take `⟨h1, h2⟩` from `idx_spec k j m`. Simplify using `only [aW, h1, h2]`.
-/
theorem aW_at (k : ℕ) (lam : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    aW p k lam (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖lam j‖ * (p : ℝ) ^ (-m) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [aW, h1, h2]

/- English proof (translation)
Take `⟨h1, h2⟩` from `idx_spec k j m`. Simplify using `only [rW, h1, h2]`.
-/
theorem rW_at (k : ℕ) (π : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    rW p k π (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * m))) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [rW, h1, h2]

end GlobalTheory.PMonE.WinBounds

namespace GlobalTheory.PMonE.WinBounds

open GlobalTheory.PMonE

/- English proof (translation)
Introduce `F _ p _ _ _ k ϖ hϖ lam π hlam hanti hratio hπ hrel1 hrel2 r j n`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hpne : (p : ℝ) ≠ 0` using `hp0.ne'`. Establish `ha : ∀ J, 0 < aW p k lam J`.

Introduce `J`. Unfold `aW`. Conclude with `mul_pos (norm_pos_iff.2 (hlam _)) (zpow_pos hp0 _)`. Establish `hρ : ∀ J, 0 < rW p k π J`. Introduce `J`.

Unfold `rW`. Conclude with `Real.rpow_pos_of_pos (norm_pos_iff.2 (hπ _).1) _`. Establish `hrp : ∀ (x : ℝ), 0 ≤ x → ∀ c d : ℤ, (x ^ ((p : ℝ) ^ c)) ^ ((p : ℝ) ^ d) = x ^ ((p : ℝ) ^ (c + d))`. Introduce `x hx c d`. Rewrite using `[← Real.rpow_mul hx, zpow_add₀ hpne]`.

Establish `hnat : ∀ (x : ℝ) (e : ℕ), x ^ ((p : ℝ) ^ (e : ℤ)) = x ^ (p ^ e)`. Introduce `x e`. Rewrite using `[zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]`. Establish `hstep : ∀ J, aW p k lam (J + 1) ≤ aW p k lam J`. Introduce `J`.

Take `⟨i, m, rfl⟩` from `decomp k J`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Establish `e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1)`. Move the coercions through the operations in `[Fin.val_last, Fin.val_zero]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]`. Establish `h1` using `hratio 0 (Fin.last k)`. Establish `hz` using `zpow_pos hp0 (-m)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[div_le_iff₀ hp0]`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `cast i`. Establish `e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m`. Move the coercions through the operations in `[Fin.coe_castSucc, Fin.val_succ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, aW_at, aW_at]`. Establish `h1 : ‖lam i.succ‖ ≤ ‖lam (Fin.castSucc i)‖` using `hanti (Fin.castSucc_lt_succ (i := i)).le`. Establish `hz` using `zpow_pos hp0 (-m)`. Use `gcongr`.

Establish `hA : Antitone (aW p k lam)` using `antitone_int_of_succ_le hstep`. Establish `hA0 : aW p k lam 0 < (p : ℝ) * aW p k lam (((k + 1 : ℕ) : ℤ) - 1)`. Establish `h1 : aW p k lam 0 = ‖lam 0‖` using `by simpa using aW_at p k lam 0 0`. Establish `h2 : aW p k lam (k : ℤ) = ‖lam (Fin.last k)‖` using `by simpa using aW_at p k lam (Fin.last k) 0`. Rewrite using `[h1, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, h2]`.

Conclude with `hratio 0 (Fin.last k)`. Establish `hperA : ∀ J, aW p k lam (J + ((k + 1 : ℕ) : ℤ)) = aW p k lam J / p`. Introduce `J`. Take `⟨i, m, rfl⟩` from `decomp k J`. Rewrite using `[show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by push_cast; ring, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hperR : ∀ J, rW p k π (J + ((k + 1 : ℕ) : ℤ)) = rW p k π J ^ (((p : ℝ) ^ (k + 1))⁻¹)`. Introduce `J`. Take `⟨i, m, rfl⟩` from `decomp k J`. Rewrite using `[show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by push_cast; ring, rW_at, rW_at]`.

Establish `e3 : ((p : ℝ) ^ (k + 1))⁻¹ = (p : ℝ) ^ (-((k : ℤ) + 1))`. Rewrite using `[zpow_neg]`. Use `norm_cast`. Rewrite using `[e3, hrp _ (norm_nonneg _), show -(((k : ℤ) + 1) * (m + 1)) = -(((k : ℤ) + 1) * m) + -((k : ℤ) + 1) by ring]`. Establish `hrelW : ∀ J, aW p k lam (J + 1) * rW p k π (J + 1) ^ ((p : ℝ) ^ J) = aW p k lam J * rW p k π J ^ ((p : ℝ) ^ J)`.

Introduce `J`. Take `⟨i, m, rfl⟩` from `decomp k J`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Establish `e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1)`.

Move the coercions through the operations in `[Fin.val_last, Fin.val_zero]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]`. Establish `e2 : -(((k : ℤ) + 1) * (m + 1)) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = -1`. Move the coercions through the operations in `[Fin.val_last]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e3 : -(((k : ℤ) + 1) * m) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((k : ℕ) : ℤ)`. Move the coercions through the operations in `[Fin.val_last]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, e3, hnat, zpow_neg_one]`.

Establish `hXY : ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) = ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k`. Establish `hx : 0 ≤ ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹)` using `by positivity`. Establish `hy : 0 ≤ ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k` using `by positivity`. Use `(pow_left_inj₀ hx hy (Fact.out : p.Prime).ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[mul_pow, ← hrel2, ← Real.rpow_natCast (‖π 0‖ ^ ((p : ℝ)⁻¹)) p, ← Real.rpow_mul (norm_nonneg _), inv_mul_cancel₀ hpne, Real.rpow_one]`.

Rewrite using `[neg_add, zpow_add₀ hpne, zpow_neg_one]`. Take the linear combination `(p : ℝ) ^ (-m) * hXY`. Consider the case `cast i`. Establish `e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m`. Move the coercions through the operations in `[Fin.coe_castSucc, Fin.val_succ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]`. Establish `e2 : -(((k : ℤ) + 1) * m) + ((((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((i : ℕ) : ℤ)`. Move the coercions through the operations in `[Fin.coe_castSucc]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2, hnat, hnat]`. Establish `h` using `hrel1 i`. Take the linear combination `(p : ℝ) ^ (-m) * h`. Establish `hJ` using `window_ineq p (k + 1) (by exact_mod_cast (Fact.out : p.Prime).one_lt) (Nat.succ_pos k) (aW p k lam) (rW p k π) ha hρ hA hA0 hperA hperR hrelW (r : ℕ) r.isLt (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * (-n))`. Rewrite `hJ` using `[aW_at p k lam j (-n), rW_at p k π j (-n)]`.

Establish `hR1 : aW p k lam ((r : ℕ) : ℤ) = ‖lam r‖` using `by simpa using aW_at p k lam r 0`. Establish `hR2 : rW p k π ((r : ℕ) : ℤ) = ‖π r‖` using `by simpa using rW_at p k π r 0`. Rewrite `hJ` using `[hR1, hR2]`. Establish `hT : ‖term p ϖ lam π r j n‖ = ‖lam j‖ * (p : ℝ) ^ (-(-n)) * (‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * -n)))) ^ ((p : ℝ) ^ (r : ℕ))`. Rewrite using `[norm_term p k ϖ hϖ, ← zpow_natCast (p : ℝ) (r : ℕ), hrp _ (norm_nonneg _), neg_neg, show -(((k : ℤ) + 1) * -n) + ((r : ℕ) : ℤ) = ((r : ℕ) : ℤ) + n * ((k : ℤ) + 1) by ring]`.

Establish `hRt : ‖lam r * π r ^ p ^ (r : ℕ)‖ = ‖lam r‖ * ‖π r‖ ^ ((p : ℝ) ^ (r : ℕ))`. Rewrite using `[norm_mul, norm_pow, ← Real.rpow_natCast ‖π r‖ (p ^ (r : ℕ)), Nat.cast_pow]`. Rewrite using `[hT, hRt]`. Take `⟨W1, W2, W3, W4⟩` from `hJ`. Establish `hj1 : ((j : ℕ) : ℤ) < (k : ℤ) + 1` using `by exact_mod_cast j.isLt`.

Establish `hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ)` using `by positivity`. Use `⟨W1, fun hn => W2 (by nlinarith), fun hn => ?_⟩` and prove the remaining obligations. Break down `lt_abs.1 hn with hn | hn` into its components or cases. Conclude with `W3 (by push_cast; nlinarith)`. Conclude with `W4 (by push_cast; nlinarith)`.
-/
theorem term_le_bound : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam π : Fin (k + 1) → F, (∀ j, lam j ≠ 0) → Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) → (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) → (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) → (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p → ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧ (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) ∧ (2 < |n| → ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ / p) := by
  intro F _ p _ _ _ k ϖ hϖ lam π hlam hanti hratio hπ hrel1 hrel2 r j n
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  have ha : ∀ J, 0 < aW p k lam J := by
    intro J; unfold aW; exact mul_pos (norm_pos_iff.2 (hlam _)) (zpow_pos hp0 _)
  have hρ : ∀ J, 0 < rW p k π J := by
    intro J; unfold rW; exact Real.rpow_pos_of_pos (norm_pos_iff.2 (hπ _).1) _
  have hrp : ∀ (x : ℝ), 0 ≤ x → ∀ c d : ℤ, (x ^ ((p : ℝ) ^ c)) ^ ((p : ℝ) ^ d) = x ^ ((p : ℝ) ^ (c + d)) := by
    intro x hx c d; rw [← Real.rpow_mul hx, zpow_add₀ hpne]
  have hnat : ∀ (x : ℝ) (e : ℕ), x ^ ((p : ℝ) ^ (e : ℤ)) = x ^ (p ^ e) := by
    intro x e; rw [zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
  have hstep : ∀ J, aW p k lam (J + 1) ≤ aW p k lam J := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    induction i using Fin.lastCases with
    | last =>
      have e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1
          = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) := by
        push_cast [Fin.val_last, Fin.val_zero]; ring
      rw [e1, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]
      have h1 := hratio 0 (Fin.last k)
      have hz := zpow_pos hp0 (-m)
      calc ‖lam 0‖ * ((p : ℝ) ^ (-m) * (p : ℝ)⁻¹) = (‖lam 0‖ / p) * (p : ℝ) ^ (-m) := by ring
        _ ≤ ‖lam (Fin.last k)‖ * (p : ℝ) ^ (-m) := by
          gcongr
          rw [div_le_iff₀ hp0]; linarith
    | cast i =>
      have e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
        push_cast [Fin.coe_castSucc, Fin.val_succ]; ring
      rw [e1, aW_at, aW_at]
      have h1 : ‖lam i.succ‖ ≤ ‖lam (Fin.castSucc i)‖ := hanti (Fin.castSucc_lt_succ (i := i)).le
      have hz := zpow_pos hp0 (-m)
      gcongr
  have hA : Antitone (aW p k lam) := antitone_int_of_succ_le hstep
  have hA0 : aW p k lam 0 < (p : ℝ) * aW p k lam (((k + 1 : ℕ) : ℤ) - 1) := by
    have h1 : aW p k lam 0 = ‖lam 0‖ := by simpa using aW_at p k lam 0 0
    have h2 : aW p k lam (k : ℤ) = ‖lam (Fin.last k)‖ := by simpa using aW_at p k lam (Fin.last k) 0
    rw [h1, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, h2]
    exact hratio 0 (Fin.last k)
  have hperA : ∀ J, aW p k lam (J + ((k + 1 : ℕ) : ℤ)) = aW p k lam J / p := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    rw [show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by
      push_cast; ring, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]
    ring
  have hperR : ∀ J, rW p k π (J + ((k + 1 : ℕ) : ℤ)) = rW p k π J ^ (((p : ℝ) ^ (k + 1))⁻¹) := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    rw [show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by
      push_cast; ring, rW_at, rW_at]
    have e3 : ((p : ℝ) ^ (k + 1))⁻¹ = (p : ℝ) ^ (-((k : ℤ) + 1)) := by
      rw [zpow_neg]; norm_cast
    rw [e3, hrp _ (norm_nonneg _), show -(((k : ℤ) + 1) * (m + 1)) = -(((k : ℤ) + 1) * m) + -((k : ℤ) + 1) by ring]
  have hrelW : ∀ J, aW p k lam (J + 1) * rW p k π (J + 1) ^ ((p : ℝ) ^ J)
      = aW p k lam J * rW p k π J ^ ((p : ℝ) ^ J) := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    induction i using Fin.lastCases with
    | last =>
      have e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1
          = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) := by
        push_cast [Fin.val_last, Fin.val_zero]; ring
      rw [e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]
      have e2 : -(((k : ℤ) + 1) * (m + 1)) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = -1 := by
        push_cast [Fin.val_last]; ring
      have e3 : -(((k : ℤ) + 1) * m) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((k : ℕ) : ℤ) := by
        push_cast [Fin.val_last]; ring
      rw [e2, e3, hnat, zpow_neg_one]
      have hXY : ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) = ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k := by
        have hx : 0 ≤ ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) := by positivity
        have hy : 0 ≤ ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k := by positivity
        refine (pow_left_inj₀ hx hy (Fact.out : p.Prime).ne_zero).1 ?_
        rw [mul_pow, ← hrel2, ← Real.rpow_natCast (‖π 0‖ ^ ((p : ℝ)⁻¹)) p, ← Real.rpow_mul (norm_nonneg _),
          inv_mul_cancel₀ hpne, Real.rpow_one]
      rw [neg_add, zpow_add₀ hpne, zpow_neg_one]
      linear_combination (p : ℝ) ^ (-m) * hXY
    | cast i =>
      have e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
        push_cast [Fin.coe_castSucc, Fin.val_succ]; ring
      rw [e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]
      have e2 : -(((k : ℤ) + 1) * m) + ((((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((i : ℕ) : ℤ) := by
        push_cast [Fin.coe_castSucc]; ring
      rw [e2, hnat, hnat]
      have h := hrel1 i
      linear_combination (p : ℝ) ^ (-m) * h
  have hJ := window_ineq p (k + 1) (by exact_mod_cast (Fact.out : p.Prime).one_lt) (Nat.succ_pos k) (aW p k lam)
    (rW p k π) ha hρ hA hA0 hperA hperR hrelW (r : ℕ) r.isLt (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * (-n))
  rw [aW_at p k lam j (-n), rW_at p k π j (-n)] at hJ
  have hR1 : aW p k lam ((r : ℕ) : ℤ) = ‖lam r‖ := by simpa using aW_at p k lam r 0
  have hR2 : rW p k π ((r : ℕ) : ℤ) = ‖π r‖ := by simpa using rW_at p k π r 0
  rw [hR1, hR2] at hJ
  have hT : ‖term p ϖ lam π r j n‖
      = ‖lam j‖ * (p : ℝ) ^ (-(-n)) * (‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * -n)))) ^ ((p : ℝ) ^ (r : ℕ)) := by
    rw [norm_term p k ϖ hϖ, ← zpow_natCast (p : ℝ) (r : ℕ), hrp _ (norm_nonneg _), neg_neg,
      show -(((k : ℤ) + 1) * -n) + ((r : ℕ) : ℤ) = ((r : ℕ) : ℤ) + n * ((k : ℤ) + 1) by ring]
  have hRt : ‖lam r * π r ^ p ^ (r : ℕ)‖ = ‖lam r‖ * ‖π r‖ ^ ((p : ℝ) ^ (r : ℕ)) := by
    rw [norm_mul, norm_pow, ← Real.rpow_natCast ‖π r‖ (p ^ (r : ℕ)), Nat.cast_pow]
  rw [hT, hRt]
  obtain ⟨W1, W2, W3, W4⟩ := hJ
  have hj1 : ((j : ℕ) : ℤ) < (k : ℤ) + 1 := by exact_mod_cast j.isLt
  have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
  refine ⟨W1, fun hn => W2 (by nlinarith), fun hn => ?_⟩
  rcases lt_abs.1 hn with hn | hn
  · exact W3 (by push_cast; nlinarith)
  · exact W4 (by push_cast; nlinarith)

end GlobalTheory.PMonE.WinBounds

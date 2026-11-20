import Formalism.HermitianCurvature.LowerBlockNormalisedBoundFromComponents

open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.FrameIntegralJacobian

open Formalism.FourierDecayAlt.PairingProductCorollary

/- English proof (translation)
Unfold `FactorsPositive`. Use `⟨fun D h0 h1 => ?_, fun d h1 h2 => ?_, fun D h0 h1 => div_neg_of_pos_of_neg h0 (by linarith)⟩` and prove the remaining obligations. Simplify using `only [div_pos_iff, lt_abs]`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro ⟨⟨ha, hb⟩ | ⟨ha, hb⟩, ⟨hc, hd⟩ | ⟨hc, hd⟩⟩ <;> first | (left; linarith) | (right; linarith) | (exfalso; linarith)`.

Introduce and unpack `(h | h)`. Conclude with `⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩`. Conclude with `⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩`. Simplify using `only [div_pos_iff]`. Prove the components needed by the constructor for the conclusion.

Apply the tactic sequence `rintro ⟨⟨ha, hb⟩ | ⟨ha, hb⟩, ⟨hc, hd⟩ | ⟨hc, hd⟩⟩ <;> first | (left; linarith) | (right; linarith) | (exfalso; linarith)`. Introduce and unpack `(h | h)`. Conclude with `⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩`. Conclude with `⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩`.
-/
theorem factorsPositive_ok : FactorsPositive := by
  unfold FactorsPositive
  refine ⟨fun D h0 h1 => ?_, fun d h1 h2 => ?_, fun D h0 h1 => div_neg_of_pos_of_neg h0 (by linarith)⟩
  · simp only [div_pos_iff, lt_abs]
    constructor
    · rintro ⟨⟨ha, hb⟩ | ⟨ha, hb⟩, ⟨hc, hd⟩ | ⟨hc, hd⟩⟩ <;>
        first | (left; linarith) | (right; linarith) | (exfalso; linarith)
    · rintro (h | h)
      · exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩
      · exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩
  · simp only [div_pos_iff]
    constructor
    · rintro ⟨⟨ha, hb⟩ | ⟨ha, hb⟩, ⟨hc, hd⟩ | ⟨hc, hd⟩⟩ <;>
        first | (left; linarith) | (right; linarith) | (exfalso; linarith)
    · rintro (h | h)
      · exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩
      · exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩

/- English proof (translation)
Unfold `CutRoom`. Introduce `r α β h`. Use `⟨by ring, fun k hk => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `: (0:ℝ) ≤ k` using `Nat.cast_nonneg k`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hk' : ((k:ℝ) + 1) ≤ 6 * ((r:ℝ) + 1) ^ 2`. Conclude with `(show k + 1 ≤ 6 * (r + 1) ^ 2 from hk)` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cutRoom_ok : CutRoom := by
  unfold CutRoom
  intro r α β h
  refine ⟨by ring, fun k hk => ⟨?_, ?_⟩⟩
  · have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  · have hk' : ((k:ℝ) + 1) ≤ 6 * ((r:ℝ) + 1) ^ 2 := by
      exact_mod_cast (show k + 1 ≤ 6 * (r + 1) ^ 2 from hk)
    linarith

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hx : 0 ≤ 1 - x` using `by linarith`. Establish `hm` using `mul_le_mul_of_nonneg_right ih hx`.

Rewrite using `[pow_succ]`. Use `push_cast`. Use polynomial arithmetic with `[mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg h0 h0)]`.
-/
private lemma bern_lemma (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hx : 0 ≤ 1 - x := by linarith
    have hm := mul_le_mul_of_nonneg_right ih hx
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg h0 h0)]

/- English proof (translation)
Unfold `WeightLower`. Introduce `N m f hN hm hf`. Establish `hN4 : (4:ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hN0 : (N:ℝ) ≠ 0` using `by positivity`. Establish `hxN2 : 1 / (N:ℝ) ^ 2 * (N:ℝ) ^ 2 = 1` using `by field_simp`.

Establish `hx0 : 0 ≤ 1 / (N:ℝ) ^ 2` using `by positivity`. Establish `hNx : (N:ℝ) * (1 / (N:ℝ) ^ 2) ≤ 1 / 4`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hx0 (by linarith : (0:ℝ) ≤ N)) (by linarith : (0:ℝ) ≤ (N:ℝ) - 4)]`. Establish `hx1 : 1 / (N:ℝ) ^ 2 ≤ 1`. Use polynomial arithmetic with `[mul_nonneg hx0 (by linarith : (0:ℝ) ≤ (N:ℝ) - 4)]`.

Establish `ht0 : 0 ≤ 1 - 1 / (N:ℝ) ^ 2` using `by linarith`. Establish `ht1 : 1 - 1 / (N:ℝ) ^ 2 ≤ 1` using `by linarith`. Establish `hprod : ∏ _i : Fin m, (1 - 1 / (N:ℝ) ^ 2) ≤ ∏ i, f i` using `Finset.prod_le_prod (fun i _ => ht0) (fun i _ => hf i)`. Rewrite `hprod` using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `hpow : (1 - 1 / (N:ℝ) ^ 2) ^ N ≤ (1 - 1 / (N:ℝ) ^ 2) ^ m` using `pow_le_pow_of_le_one ht0 ht1 hm`.

Establish `hbern` using `bern_lemma (1 / (N:ℝ) ^ 2) hx0 hx1 N`. Establish `hexp : Real.exp (-(1 / 2)) ≤ 3 / 4`. Establish `e1` using `Real.add_one_le_exp (1 / 2 : ℝ)`. Establish `e2 : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1`. Rewrite using `[← Real.exp_add]`.

Simplify using the standard rewrite rules. Establish `e3` using `Real.exp_pos (-(1 / 2))`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weightLower_ok : WeightLower := by
  unfold WeightLower
  intro N m f hN hm hf
  have hN4 : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N:ℝ) ≠ 0 := by positivity
  have hxN2 : 1 / (N:ℝ) ^ 2 * (N:ℝ) ^ 2 = 1 := by field_simp
  have hx0 : 0 ≤ 1 / (N:ℝ) ^ 2 := by positivity
  have hNx : (N:ℝ) * (1 / (N:ℝ) ^ 2) ≤ 1 / 4 := by
    nlinarith [mul_nonneg (mul_nonneg hx0 (by linarith : (0:ℝ) ≤ N)) (by linarith : (0:ℝ) ≤ (N:ℝ) - 4)]
  have hx1 : 1 / (N:ℝ) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx0 (by linarith : (0:ℝ) ≤ (N:ℝ) - 4)]
  have ht0 : 0 ≤ 1 - 1 / (N:ℝ) ^ 2 := by linarith
  have ht1 : 1 - 1 / (N:ℝ) ^ 2 ≤ 1 := by linarith
  have hprod : ∏ _i : Fin m, (1 - 1 / (N:ℝ) ^ 2) ≤ ∏ i, f i :=
    Finset.prod_le_prod (fun i _ => ht0) (fun i _ => hf i)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hpow : (1 - 1 / (N:ℝ) ^ 2) ^ N ≤ (1 - 1 / (N:ℝ) ^ 2) ^ m :=
    pow_le_pow_of_le_one ht0 ht1 hm
  have hbern := bern_lemma (1 / (N:ℝ) ^ 2) hx0 hx1 N
  have hexp : Real.exp (-(1 / 2)) ≤ 3 / 4 := by
    have e1 := Real.add_one_le_exp (1 / 2 : ℝ)
    have e2 : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have e3 := Real.exp_pos (-(1 / 2))
    nlinarith
  linarith

/- English proof (translation)
Unfold `BlockPhase`. Introduce `s x`. Establish `hI : Complex.I ≠ 0` using `Complex.I_ne_zero`. Establish `h1 : Complex.I ^ ((s:ℤ) - 1 - 2 * x) = Complex.I ^ ((s:ℤ) - 1) * ((Complex.I ^ 2) ^ x)⁻¹`. Rewrite using `[sub_eq_add_neg ((s:ℤ) - 1), zpow_add₀ hI, zpow_neg, ← pow_mul]`.

Use `norm_cast`. Rewrite using `[h1, Complex.I_sq, mul_assoc, inv_mul_cancel₀ (pow_ne_zero x (by norm_num : (-1:ℂ) ≠ 0)), mul_one]`.
-/
theorem blockPhase_ok : BlockPhase := by
  unfold BlockPhase
  intro s x
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h1 : Complex.I ^ ((s:ℤ) - 1 - 2 * x) = Complex.I ^ ((s:ℤ) - 1) * ((Complex.I ^ 2) ^ x)⁻¹ := by
    rw [sub_eq_add_neg ((s:ℤ) - 1), zpow_add₀ hI, zpow_neg, ← pow_mul]
    norm_cast
  rw [h1, Complex.I_sq, mul_assoc, inv_mul_cancel₀ (pow_ne_zero x (by norm_num : (-1:ℂ) ≠ 0)), mul_one]

/- English proof (translation)
Unfold `StdFramePhase`. Introduce `ka a b ha hb`. Take `⟨a', rfl⟩ : ∃ a', a = a' + 1` from `⟨a - 1, by omega⟩`. Take `⟨b', rfl⟩ : ∃ b', b = b' + 1` from `⟨b - 1, by omega⟩`. Establish `hab : a' + 1 + (b' + 1) - 2 = b' + a'` using `by omega`.

Establish `hconj : starRingEnd ℂ (Complex.I * ka) = Complex.I⁻¹ * ka`. Rewrite using `[map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.inv_I]`. Establish `hz : Complex.I ^ (((b' + 1 : ℕ) : ℤ) - ((a' + 1 : ℕ) : ℤ)) = Complex.I ^ b' / Complex.I ^ a'`. Rewrite using `[show (((b' + 1 : ℕ) : ℤ) - ((a' + 1 : ℕ) : ℤ)) = (b' : ℤ) - (a' : ℤ) by push_cast; ring, zpow_sub₀ Complex.I_ne_zero, zpow_natCast, zpow_natCast]`. Simplify using `only [Nat.add_sub_cancel]`.

Rewrite using `[hab, hconj, mul_pow, mul_pow, inv_pow, pow_add, hz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stdFramePhase_ok : StdFramePhase := by
  unfold StdFramePhase
  intro ka a b ha hb
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hab : a' + 1 + (b' + 1) - 2 = b' + a' := by omega
  have hconj : starRingEnd ℂ (Complex.I * ka) = Complex.I⁻¹ * ka := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.inv_I]
  have hz : Complex.I ^ (((b' + 1 : ℕ) : ℤ) - ((a' + 1 : ℕ) : ℤ)) = Complex.I ^ b' / Complex.I ^ a' := by
    rw [show (((b' + 1 : ℕ) : ℤ) - ((a' + 1 : ℕ) : ℤ)) = (b' : ℤ) - (a' : ℤ) by push_cast; ring,
      zpow_sub₀ Complex.I_ne_zero, zpow_natCast, zpow_natCast]
  simp only [Nat.add_sub_cancel]
  rw [hab, hconj, mul_pow, mul_pow, inv_pow, pow_add, hz]
  ring

/- English proof (translation)
Unfold `RealFrameEntry`. Introduce `rd r a b i s hrd`. Use `⟨?_, fun h => by omega⟩` and prove the remaining obligations. Rewrite using `[← zpow_add₀ hrd.ne']`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem realFrameEntry_ok : RealFrameEntry := by
  unfold RealFrameEntry
  intro rd r a b i s hrd
  refine ⟨?_, fun h => by omega⟩
  rw [← zpow_add₀ hrd.ne']
  congr 1
  ring

/- English proof (translation)
Unfold `GaExponent`. Use `⟨fun ka l M hM => ?_, fun r k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul]`. Use `congr 1`. Take `⟨M', rfl⟩ : ∃ M', M = M' + 2` from `⟨M - 2, by omega⟩`.

Break down `Nat.eq_zero_or_pos l with hl | hl` into its components or cases. Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Take `⟨l', rfl⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by omega⟩`. Establish `h1 : 2 * (l' + 1) - 2 = 2 * l'` using `by omega`.

Establish `h2 : 2 * (M' + 2 - 2) + 2 = 2 * (M' + 1)` using `by omega`. Establish `h3 : l' + 1 - 1 = l'` using `by omega`. Establish `h4 : M' + 2 - 1 = M' + 1` using `by omega`. Rewrite using `[h1, h2, h3, h4]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Establish `h1 : k' + 1 - 1 = k'` using `by omega`. Establish `h2 : k' + 1 + 1 - 1 = k' + 1` using `by omega`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaExponent_ok : GaExponent := by
  unfold GaExponent
  refine ⟨fun ka l M hM => ?_, fun r k hk => ?_⟩
  · rw [← pow_mul]
    congr 1
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl
      simp
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have h1 : 2 * (l' + 1) - 2 = 2 * l' := by omega
      have h2 : 2 * (M' + 2 - 2) + 2 = 2 * (M' + 1) := by omega
      have h3 : l' + 1 - 1 = l' := by omega
      have h4 : M' + 2 - 1 = M' + 1 := by omega
      rw [h1, h2, h3, h4]
      ring
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h1 : k' + 1 - 1 = k' := by omega
    have h2 : k' + 1 + 1 - 1 = k' + 1 := by omega
    rw [h1, h2]
    ring

/- English proof (translation)
Unfold `RealCharacter`. Introduce `g rd x hg hrd`. Establish `hg' : (g:ℂ) ≠ 0` using `by exact_mod_cast hg.ne'`. Establish `hrd' : (rd:ℂ) ≠ 0` using `by exact_mod_cast hrd.ne'`. Use `congr 1`.

Rewrite using `[map_mul, Complex.conj_ofReal]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.
-/
theorem realCharacter_ok : RealCharacter := by
  unfold RealCharacter
  intro g rd x hg hrd
  have hg' : (g:ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hrd' : (rd:ℂ) ≠ 0 := by exact_mod_cast hrd.ne'
  congr 1
  rw [map_mul, Complex.conj_ofReal]
  push_cast
  field_simp
  try ring

/- English proof (translation)
Unfold `PlacesCombine`. Introduce `ι _ _ K abelian₂ o N S hL hS h`. Establish `hpos : 0 < ∏ v ∈ univ.filter (fun v => abelian₂ v < o v), o v ^ K`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `v hv`.

Establish `hv' : abelian₂ v < o v` using `(Finset.mem_filter.mp hv).2`. Conclude with `pow_pos (lt_of_le_of_lt (hL v) hv') K`. Establish `hprod : ∏ v, minFac (abelian₂ v) (o v) K = (∏ v ∈ univ.filter (fun v => abelian₂ v < o v), abelian₂ v ^ K) / (∏ v ∈ univ.filter (fun v => abelian₂ v < o v), o v ^ K)`. Simplify using `only [minFac, div_pow]`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_div_distrib]`.

Rewrite using `[hprod, div_mul_eq_mul_div, le_div_iff₀ hpos, mul_comm N]`. Conclude with `h`.
-/
theorem placesCombine_ok : PlacesCombine := by
  unfold PlacesCombine
  intro ι _ _ K abelian₂ o N S hL hS h
  have hpos : 0 < ∏ v ∈ univ.filter (fun v => abelian₂ v < o v), o v ^ K := by
    apply Finset.prod_pos
    intro v hv
    have hv' : abelian₂ v < o v := (Finset.mem_filter.mp hv).2
    exact pow_pos (lt_of_le_of_lt (hL v) hv') K
  have hprod : ∏ v, minFac (abelian₂ v) (o v) K =
      (∏ v ∈ univ.filter (fun v => abelian₂ v < o v), abelian₂ v ^ K) /
        (∏ v ∈ univ.filter (fun v => abelian₂ v < o v), o v ^ K) := by
    simp only [minFac, div_pow]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_div_distrib]
  rw [hprod, div_mul_eq_mul_div, le_div_iff₀ hpos, mul_comm N]
  exact h

/- English proof (translation)
Unfold `CorAConstWave`. Use `⟨fun n ell Qw BBs BB hell hn hQ0 hQ hB0 hB => ?_, fun Qw BBs BB hQ0 hQ hB0 hB => ?_⟩` and prove the remaining obligations. Establish `h2 : Real.exp (1 / 2) = Real.exp (1 / 4) ^ 2`. Rewrite using `[sq, ← Real.exp_add]`. Evaluate the numerical expressions.

Establish `hs : Real.sqrt Qw ≤ Real.exp (1 / 4)`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : 0 ≤ 4 / ell` using `div_nonneg (by norm_num) hell.le`. Establish `hP : 0 ≤ (1 / 2 : ℝ) * (4 / ell) ^ n` using `mul_nonneg (by norm_num) (pow_nonneg h4 n)`. Establish `hm : Real.sqrt Qw * BBs ≤ Real.exp (1 / 4) * BB` using `mul_le_mul hs hB hB0 (Real.exp_pos _).le`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Real.exp 2 = Real.exp 1 ^ 2`. Rewrite using `[sq, ← Real.exp_add]`. Evaluate the numerical expressions. Establish `hs : Real.sqrt Qw ≤ Real.exp 1`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul hs hB hB0 (Real.exp_pos _).le`.
-/
theorem corAConstWave_ok : CorAConstWave := by
  unfold CorAConstWave
  refine ⟨fun n ell Qw BBs BB hell hn hQ0 hQ hB0 hB => ?_, fun Qw BBs BB hQ0 hQ hB0 hB => ?_⟩
  · have h2 : Real.exp (1 / 2) = Real.exp (1 / 4) ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    have hs : Real.sqrt Qw ≤ Real.exp (1 / 4) := by
      calc Real.sqrt Qw ≤ Real.sqrt (Real.exp (1 / 4) ^ 2) := Real.sqrt_le_sqrt (by rw [← h2]; exact hQ)
        _ = Real.exp (1 / 4) := Real.sqrt_sq (Real.exp_pos _).le
    have h4 : 0 ≤ 4 / ell := div_nonneg (by norm_num) hell.le
    have hP : 0 ≤ (1 / 2 : ℝ) * (4 / ell) ^ n := mul_nonneg (by norm_num) (pow_nonneg h4 n)
    have hm : Real.sqrt Qw * BBs ≤ Real.exp (1 / 4) * BB :=
      mul_le_mul hs hB hB0 (Real.exp_pos _).le
    calc (1 / 2) * (4 / ell) ^ n * Real.sqrt Qw * BBs
        = ((1 / 2) * (4 / ell) ^ n) * (Real.sqrt Qw * BBs) := by ring
      _ ≤ ((1 / 2) * (4 / ell) ^ n) * (Real.exp (1 / 4) * BB) := mul_le_mul_of_nonneg_left hm hP
      _ = Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ n * BB := by ring
  · have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    have hs : Real.sqrt Qw ≤ Real.exp 1 := by
      calc Real.sqrt Qw ≤ Real.sqrt (Real.exp 1 ^ 2) := Real.sqrt_le_sqrt (by rw [← h2]; exact hQ)
        _ = Real.exp 1 := Real.sqrt_sq (Real.exp_pos _).le
    exact mul_le_mul hs hB hB0 (Real.exp_pos _).le

/- English proof (translation)
Unfold `WeightedKernelPSD`. Introduce `H _ Kn n hK hn`. Establish `hst : ∀ h : H, star (((Real.sqrt (n h) : ℝ)) : ℂ) = ((Real.sqrt (n h) : ℝ) : ℂ)` using `fun h => Complex.conj_ofReal _`. Establish `hB` using `hK.conjTranspose_mul_mul_same (Matrix.diagonal fun h => ((Real.sqrt (n h) : ℝ) : ℂ))`. Use `hB using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Pi.star_apply, hst, Matrix.of_apply, Complex.ofReal_mul]`. Apply the tactic sequence `try ring`.
-/
theorem weightedKernelPSD_ok : WeightedKernelPSD := by
  unfold WeightedKernelPSD
  intro H _ Kn n hK hn
  classical
  have hst : ∀ h : H, star (((Real.sqrt (n h) : ℝ)) : ℂ) = ((Real.sqrt (n h) : ℝ) : ℂ) :=
    fun h => Complex.conj_ofReal _
  have hB := hK.conjTranspose_mul_mul_same (Matrix.diagonal fun h => ((Real.sqrt (n h) : ℝ) : ℂ))
  convert hB using 1
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Pi.star_apply,
    hst, Matrix.of_apply, Complex.ofReal_mul]
  try ring

/- English proof (translation)
Unfold `ScaleBeta`. Introduce `ka Pp q r hka hq hP`. Establish `hk0 : ka ≠ 0` using `hka.ne'`. Establish `e1 : Pp / (ka ^ (4 * r) * q) = Pp / q / (ka ^ (2 * r)) ^ 2`. Rewrite using `[← pow_mul, div_div, mul_comm q, show 2 * r * 2 = 4 * r by ring]`.

Establish `e2 : ka ^ (-(1 + 2 * r : ℤ)) = (ka * ka ^ (2 * r))⁻¹`. Rewrite using `[zpow_neg, ← pow_succ', show (1 + 2 * (r:ℤ)) = ((2 * r + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]`. Rewrite using `[e1, Real.sqrt_div (div_nonneg hP hq.le), Real.sqrt_sq (pow_nonneg hka.le (2 * r)), e2, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hk0, one_mul, div_eq_inv_mul]`.
-/
theorem scaleBeta_ok : ScaleBeta := by
  unfold ScaleBeta
  intro ka Pp q r hka hq hP
  have hk0 : ka ≠ 0 := hka.ne'
  have e1 : Pp / (ka ^ (4 * r) * q) = Pp / q / (ka ^ (2 * r)) ^ 2 := by
    rw [← pow_mul, div_div, mul_comm q, show 2 * r * 2 = 4 * r by ring]
  have e2 : ka ^ (-(1 + 2 * r : ℤ)) = (ka * ka ^ (2 * r))⁻¹ := by
    rw [zpow_neg, ← pow_succ', show (1 + 2 * (r:ℤ)) = ((2 * r + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
  rw [e1, Real.sqrt_div (div_nonneg hP hq.le), Real.sqrt_sq (pow_nonneg hka.le (2 * r)), e2, mul_inv,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hk0, one_mul, div_eq_inv_mul]

/- English proof (translation)
Unfold `FrameIntegral`. Introduce `ka de Cst ph pht Rt R hka hde hph hRt hR`. Establish `hk0 : ka ≠ 0` using `hka.ne'`. Establish `hcv : ∫ x : ℂ, pht (ka • x) = |(ka ^ 2)⁻¹| • ∫ x : ℂ, pht x`. Establish `h` using `MeasureTheory.Measure.integral_comp_smul (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ)) pht ka`.

Rewrite `h` using `[Complex.finrank_real_complex]`. Conclude with `h`. Establish `hfun : ∀ c : ℂ, ph c * (de : ℂ) = (Cst * ka ^ 2 : ℝ) • pht (ka • c)`. Introduce `c`. Rewrite using `[hph c, Complex.real_smul, Complex.real_smul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hfun]`. Rewrite using `[MeasureTheory.integral_smul, hcv, smul_smul, hRt, hR, abs_of_pos (inv_pos.mpr (pow_pos hka 2)), Complex.real_smul, mul_assoc Cst, mul_inv_cancel₀ (pow_ne_zero 2 hk0), mul_one]`.
-/
theorem frameIntegral_ok : FrameIntegral := by
  unfold FrameIntegral
  intro ka de Cst ph pht Rt R hka hde hph hRt hR
  have hk0 : ka ≠ 0 := hka.ne'
  have hcv : ∫ x : ℂ, pht (ka • x) = |(ka ^ 2)⁻¹| • ∫ x : ℂ, pht x := by
    have h := MeasureTheory.Measure.integral_comp_smul
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ)) pht ka
    rw [Complex.finrank_real_complex] at h
    exact h
  have hfun : ∀ c : ℂ, ph c * (de : ℂ) = (Cst * ka ^ 2 : ℝ) • pht (ka • c) := by
    intro c
    rw [hph c, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  simp_rw [hfun]
  rw [MeasureTheory.integral_smul, hcv, smul_smul, hRt, hR, abs_of_pos (inv_pos.mpr (pow_pos hka 2)),
    Complex.real_smul, mul_assoc Cst, mul_inv_cancel₀ (pow_ne_zero 2 hk0), mul_one]

/- English proof (translation)
Unfold `FrameJacobian`. Introduce `ka m g hka`. Establish `hk0 : ka ≠ 0` using `hka.ne'`. Establish `hk0c : (ka : ℂ) ≠ 0` using `by exact_mod_cast hk0`. Establish `hcv : ∫ x : ℂ, ((‖ka • x‖ ^ (2 * m) : ℝ) : ℂ) * g (ka • x) = |(ka ^ 2)⁻¹| • ∫ x : ℂ, ((‖x‖ ^ (2 * m) : ℝ) : ℂ) * g x`.

Establish `h` using `MeasureTheory.Measure.integral_comp_smul (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ)) (fun z : ℂ => ((‖z‖ ^ (2 * m) : ℝ) : ℂ) * g z) ka`. Rewrite `h` using `[Complex.finrank_real_complex]`. Conclude with `h`. Establish `hpt : ∀ c : ℂ, ((‖c‖ ^ (2 * m) : ℝ) : ℂ) * g ((ka : ℂ) * c) = ((ka ^ (2 * m))⁻¹ : ℝ) • (((‖ka • c‖ ^ (2 * m) : ℝ) : ℂ) * g (ka • c))`. Introduce `c`.

Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_pos hka, mul_pow, Complex.real_smul, Complex.real_smul]`. Use `push_cast`. Rewrite using `[← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hk0c), one_mul]`. Establish `hreal : ka ^ (2 * m + 2) * ((ka ^ (2 * m))⁻¹ * (ka ^ 2)⁻¹) = 1`. Rewrite using `[pow_add, mul_mul_mul_comm, mul_inv_cancel₀ (pow_ne_zero _ hk0), mul_inv_cancel₀ (pow_ne_zero _ hk0), one_mul]`.

Repeatedly rewrite using `[hpt]`. Rewrite using `[MeasureTheory.integral_smul, hcv, smul_smul, abs_of_pos (inv_pos.mpr (pow_pos hka 2)), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hreal, Complex.ofReal_one, one_mul]`.
-/
theorem frameJacobian_ok : FrameJacobian := by
  unfold FrameJacobian
  intro ka m g hka
  have hk0 : ka ≠ 0 := hka.ne'
  have hk0c : (ka : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hcv : ∫ x : ℂ, ((‖ka • x‖ ^ (2 * m) : ℝ) : ℂ) * g (ka • x)
      = |(ka ^ 2)⁻¹| • ∫ x : ℂ, ((‖x‖ ^ (2 * m) : ℝ) : ℂ) * g x := by
    have h := MeasureTheory.Measure.integral_comp_smul
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
      (fun z : ℂ => ((‖z‖ ^ (2 * m) : ℝ) : ℂ) * g z) ka
    rw [Complex.finrank_real_complex] at h
    exact h
  have hpt : ∀ c : ℂ, ((‖c‖ ^ (2 * m) : ℝ) : ℂ) * g ((ka : ℂ) * c)
      = ((ka ^ (2 * m))⁻¹ : ℝ) • (((‖ka • c‖ ^ (2 * m) : ℝ) : ℂ) * g (ka • c)) := by
    intro c
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hka, mul_pow, Complex.real_smul, Complex.real_smul]
    push_cast
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hk0c), one_mul]
  have hreal : ka ^ (2 * m + 2) * ((ka ^ (2 * m))⁻¹ * (ka ^ 2)⁻¹) = 1 := by
    rw [pow_add, mul_mul_mul_comm, mul_inv_cancel₀ (pow_ne_zero _ hk0),
      mul_inv_cancel₀ (pow_ne_zero _ hk0), one_mul]
  simp_rw [hpt]
  rw [MeasureTheory.integral_smul, hcv, smul_smul, abs_of_pos (inv_pos.mpr (pow_pos hka 2)), Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul, hreal, Complex.ofReal_one, one_mul]

end Formalism.FourierDecayAlt.P.FrameIntegralJacobian

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.factorsPositive_ok`.
-/
theorem Formalism.FourierDecayAlt.P.local_factors_positive : Formalism.FourierDecayAlt.PairingProductCorollary.FactorsPositive := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.factorsPositive_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.cutRoom_ok`.
-/
theorem Formalism.FourierDecayAlt.P.truncation_room_estimate : Formalism.FourierDecayAlt.PairingProductCorollary.CutRoom := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.cutRoom_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.weightLower_ok`.
-/
theorem Formalism.FourierDecayAlt.P.weight_lower_bound : Formalism.FourierDecayAlt.PairingProductCorollary.WeightLower := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.weightLower_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.blockPhase_ok`.
-/
theorem Formalism.FourierDecayAlt.P.block_phase_identity : Formalism.FourierDecayAlt.PairingProductCorollary.BlockPhase := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.blockPhase_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.stdFramePhase_ok`.
-/
theorem Formalism.FourierDecayAlt.P.standard_frame_phase_alt : Formalism.FourierDecayAlt.PairingProductCorollary.StdFramePhase := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.stdFramePhase_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.realFrameEntry_ok`.
-/
theorem Formalism.FourierDecayAlt.P.real_frame_entry_alt : Formalism.FourierDecayAlt.PairingProductCorollary.RealFrameEntry := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.realFrameEntry_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.gaExponent_ok`.
-/
theorem Formalism.FourierDecayAlt.P.gamma_exponent_formula : Formalism.FourierDecayAlt.PairingProductCorollary.GaExponent := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.gaExponent_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.realCharacter_ok`.
-/
theorem Formalism.FourierDecayAlt.P.real_character_identity : Formalism.FourierDecayAlt.PairingProductCorollary.RealCharacter := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.realCharacter_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.placesCombine_ok`.
-/
theorem Formalism.FourierDecayAlt.P.local_places_combine : Formalism.FourierDecayAlt.PairingProductCorollary.PlacesCombine := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.placesCombine_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.corAConstWave_ok`.
-/
theorem Formalism.FourierDecayAlt.P.constant_wave_corollary : Formalism.FourierDecayAlt.PairingProductCorollary.CorAConstWave := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.corAConstWave_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.weightedKernelPSD_ok`.
-/
theorem Formalism.FourierDecayAlt.P.weighted_kernel_posSemidef : Formalism.FourierDecayAlt.PairingProductCorollary.WeightedKernelPSD := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.weightedKernelPSD_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.scaleBeta_ok`.
-/
theorem Formalism.FourierDecayAlt.P.scaling_beta_identity : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleBeta := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.scaleBeta_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameIntegral_ok`.
-/
theorem Formalism.FourierDecayAlt.P.frame_integral_formula_alt : Formalism.FourierDecayAlt.PairingProductCorollary.FrameIntegral := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameIntegral_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameJacobian_ok`.
-/
theorem Formalism.FourierDecayAlt.P.frame_jacobian_formula : Formalism.FourierDecayAlt.PairingProductCorollary.FrameJacobian := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameJacobian_ok

end

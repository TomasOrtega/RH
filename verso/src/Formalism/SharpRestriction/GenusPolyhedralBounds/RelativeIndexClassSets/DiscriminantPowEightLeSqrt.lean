import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LargeConstantLeParamCube
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SubsingletonQuotientOfIdealEqTop
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

def q0N (T : ParamsT D L P) : ℕ := ⌈L.sc.b / (T.TO : ℝ)⌉₊

/- English proof (translation)
Establish `he : 2 ≤ D.R.toFrame.e` using `D.host.two_le_e`. Establish `hU : Nat.card (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ = 2 ^ (D.R.toFrame.e + 1)`. Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, show D.R.toFrame.e + 2 = (D.R.toFrame.e + 1) + 1 by ring, Nat.totient_prime_pow_succ Nat.prime_two]`. Simplify using the standard rewrite rules. Establish `hH : Nat.card (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)) ≤ 2`.

Rewrite using `[Nat.card_zpowers]`. Conclude with `orderOf_le_of_pow_eq_one (by norm_num) (by simp)`. Establish `hmul` using `Subgroup.card_mul_index (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ))`. Rewrite `hmul` using `[hU]`. Establish `hidx : 2 ^ D.R.toFrame.e ≤ (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)).index`.

Establish `h2 : 2 ^ (D.R.toFrame.e + 1) = 2 * 2 ^ D.R.toFrame.e` using `by ring`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsurj` using `Nat.card_le_card_of_surjective _ D.R.toFrame.projection_surjective_field`. Establish `hcard : Nat.card (Additive (Formalism.FrobeniusOrbits.HGrp D.R.toFrame.e)) = (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)).index` using `rfl`. Establish `hfin : Nat.card (Formalism.HC.Idx D.R.toFrame.ord) = D.R.toFrame.ord`.

Unfold `Formalism.HC.Idx`. Simplify using the standard rewrite rules. Rewrite `hsurj` using `[hcard, hfin]`. Establish `h4 : 4 ≤ 2 ^ D.R.toFrame.e`. Combine the equalities or inequalities in the displayed calculation.

Unfold `Ranks.f Ranks.n`. Use linear arithmetic over natural numbers and integers.
-/
theorem f_ge (D : D7) : 8 ≤ D.R.f := by
  have he : 2 ≤ D.R.toFrame.e := D.host.two_le_e
  have hU : Nat.card (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ = 2 ^ (D.R.toFrame.e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      show D.R.toFrame.e + 2 = (D.R.toFrame.e + 1) + 1 by ring, Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  have hH : Nat.card (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by simp)
  have hmul := Subgroup.card_mul_index (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ))
  rw [hU] at hmul
  have hidx : 2 ^ D.R.toFrame.e ≤ (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)).index := by
    have h2 : 2 ^ (D.R.toFrame.e + 1) = 2 * 2 ^ D.R.toFrame.e := by ring
    nlinarith
  have hsurj := Nat.card_le_card_of_surjective _ D.R.toFrame.projection_surjective_field
  have hcard : Nat.card (Additive (Formalism.FrobeniusOrbits.HGrp D.R.toFrame.e)) =
      (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)).index := rfl
  have hfin : Nat.card (Formalism.HC.Idx D.R.toFrame.ord) = D.R.toFrame.ord := by
    unfold Formalism.HC.Idx
    simp
  rw [hcard, hfin] at hsurj
  have h4 : 4 ≤ 2 ^ D.R.toFrame.e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ D.R.toFrame.e := Nat.pow_le_pow_right (by norm_num) he
  unfold Ranks.f Ranks.n
  omega

/- English proof (translation)
Unfold `Ranks.r`. Use `D.R.two_le_m` as an intermediate fact. Use `D.R.m_add_three_le_k` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem r_ge (D : D7) : 6 ≤ D.R.r := by
  unfold Ranks.r
  have := D.R.two_le_m
  have := D.R.m_add_three_le_k
  omega

/- English proof (translation)
Unfold `Ranks.r`. Use `D.R.m_add_three_le_k` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem r_le_2k (D : D7) : D.R.r ≤ 2 * D.R.k := by
  unfold Ranks.r
  have := D.R.m_add_three_le_k
  omega

/- English proof (translation)
Unfold `Ranks.f Ranks.n`. Conclude with `D.R.f_le_k`.
-/
theorem f_le_k (D : D7) : D.R.f ≤ D.R.k := by
  unfold Ranks.f Ranks.n
  exact D.R.f_le_k

/- English proof (translation)
Unfold `Scale.L`. Conclude with `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`.
-/
theorem one_le_L (L : SizeData₂ D) : 1 ≤ L.sc.L := by
  unfold Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

/- English proof (translation)
Unfold `Scale.b`. Conclude with `Real.exp_pos _`.
-/
theorem b_pos (L : SizeData₂ D) : 0 < L.sc.b := by
  unfold Scale.b
  exact Real.exp_pos _

/- English proof (translation)
Unfold `zBase`. Conclude with `le_mul_of_one_le_right (by positivity) (one_le_L L)`.
-/
theorem A_le_Z (L : SizeData₂ D) : (D.R.f : ℝ) * D.R.r ≤ zBase L := by
  unfold zBase
  exact le_mul_of_one_le_right (by positivity) (one_le_L L)

/- English proof (translation)
Rewrite using `[T.PP_eq]`. Establish `h1 : zBase L ^ (12 : ℕ) = zBase L ^ (12 : ℝ)`. Rewrite using `[show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Establish `h2 : zBase L ^ (12 : ℝ) ≤ zBase L ^ T.eP` using `Real.rpow_le_rpow_of_exponent_le hZ T.eP_ge`. Establish `h3 : 0 ≤ zBase L ^ T.eP` using `Real.rpow_nonneg (by linarith) _`.

Establish `h4 : 1 * zBase L ^ T.eP ≤ T.CP * zBase L ^ T.eP` using `mul_le_mul_of_nonneg_right T.one_le_CP h3`. Rewrite using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem zBase_pow_twelve_le (T : ParamsT D L P) (hZ : 1 ≤ zBase L) : zBase L ^ 12 ≤ T.PP := by
  rw [T.PP_eq]
  have h1 : zBase L ^ (12 : ℕ) = zBase L ^ (12 : ℝ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2 : zBase L ^ (12 : ℝ) ≤ zBase L ^ T.eP := Real.rpow_le_rpow_of_exponent_le hZ T.eP_ge
  have h3 : 0 ≤ zBase L ^ T.eP := Real.rpow_nonneg (by linarith) _
  have h4 : 1 * zBase L ^ T.eP ≤ T.CP * zBase L ^ T.eP := mul_le_mul_of_nonneg_right T.one_le_CP h3
  rw [h1]
  linarith

/- English proof (translation)
Take `⟨-, -, -, -, ⟨ht1, -⟩, -, hQD, -⟩` from `S`. Take `⟨-, -, -, -, -, -, hrd1, hrd2⟩` from `hQD`. Establish `hc` using `P.condE_le`. Simplify using `only [Formalism.BasicNotions.LevelStarExponents.condE] at hc`. Move the coercions through the operations in `at hc`.

Establish `hq : (1 : ℝ) ≤ D.host.q`. Use `D.host.qd_big.1` as an intermediate fact. Conclude with `(by omega : 1 ≤ D.host.q)` after adjusting the coercions. Establish `hd : (1 : ℝ) ≤ D.host.d`. Use `D.host.qd_big.2` as an intermediate fact.

Conclude with `(by omega : 1 ≤ D.host.d)` after adjusting the coercions. Establish `hQS : (1 : ℝ) ≤ D.host.QS` using `by exact_mod_cast D.host.QS_pos`. Establish `hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d` using `by nlinarith`. Establish `hs0 : 0 ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d)` using `Real.sqrt_nonneg _`. Establish `hsq : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d`.

Rewrite using `[Real.sqrt_le_iff]`. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Establish `hC1 : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q * D.host.d` using `by nlinarith`.

Establish `hrdC : D.host.rdE ≤ (D.host.QS : ℝ) * D.host.q * D.host.d`. Establish `h1 : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d)` using `by nlinarith`. Establish `h2 : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d)` using `mul_le_mul_of_nonneg_left hsq (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Establish `h8 : D.host.rdE ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8` using `pow_le_pow_left₀ (by linarith) hrdC 8`.

Establish `h36 : ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36` using `pow_le_pow_right₀ hC1 (by norm_num)`. Establish `ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150` using `one_le_pow₀ ht1`. Establish `hpos : 0 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem discriminant_pow_eight_le_sqrt (P : ParameterChoice' D L) (S : SizesAt L) : D.host.rdE ^ 8 ≤ L.sc.b ^ ((1 : ℝ) / 2) := by
  obtain ⟨-, -, -, -, ⟨ht1, -⟩, -, hQD, -⟩ := S
  obtain ⟨-, -, -, -, -, -, hrd1, hrd2⟩ := hQD
  have hc := P.condE_le
  simp only [Formalism.BasicNotions.LevelStarExponents.condE] at hc
  push_cast at hc
  have hq : (1 : ℝ) ≤ D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 1 ≤ D.host.q)
  have hd : (1 : ℝ) ≤ D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 1 ≤ D.host.d)
  have hQS : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs0 : 0 ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hC1 : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by nlinarith
  have hrdC : D.host.rdE ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by
    have h1 : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) := by nlinarith
    have h2 : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hsq (by linarith)
    nlinarith
  have h8 : D.host.rdE ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 :=
    pow_le_pow_left₀ (by linarith) hrdC 8
  have h36 : ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 :=
    pow_le_pow_right₀ hC1 (by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht1
  have hpos : 0 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 := by positivity
  nlinarith

/- English proof (translation)
Establish `hf8 : (8 : ℝ) ≤ D.R.f` using `by exact_mod_cast f_ge D`. Establish `hr6 : (6 : ℝ) ≤ D.R.r` using `by exact_mod_cast r_ge D`. Establish `hfk : (D.R.f : ℝ) ≤ D.R.k` using `by exact_mod_cast f_le_k D`. Establish `hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k` using `by exact_mod_cast r_le_2k D`. Establish `hz1 : (1 : ℝ) ≤ zBase L` using `le_trans (by norm_num) hZ`.

Establish `hz12` using `zBase_pow_twelve_le T hz1`. Establish `hAZ` using `A_le_Z L`. Establish `hzz2 : zBase L ^ 2 ≤ zBase L ^ 12` using `by first`. Consider the case `exact pow_le_pow_right₀ hz1 (by norm_num)`. Consider the case `exact pow_le_pow_right hz1 (by norm_num)`.

Establish `hPPA : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ T.PP`. Establish `h1 : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ zBase L * zBase L` using `mul_le_mul hZ hAZ (by positivity) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hTO40` using `T.TO_40`. Establish `hTOpos : (0 : ℝ) < T.TO` using `by exact_mod_cast (by omega : 0 < T.TO)`.

Establish `hb` using `b_pos L`. Establish `hrd1 : (1 : ℝ) ≤ D.host.rdE`. Establish `hd : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)|`. Establish `h` using `NumberField.discr_ne_zero D.host.E`. Establish `h' : (1 : ℤ) ≤ |NumberField.discr D.host.E|` using `Int.one_le_abs h`.

Conclude with `h'` after adjusting the coercions. Unfold `Host.rdE`. Conclude with `Real.one_le_rpow hd (by positivity)`. Establish `hnW : 40 ≤ T.nWn`. Establish `h1` using `T.nW_lo.1`.

Establish `h2` using `f_ge D`. Establish `h3` using `r_ge D`. Establish `h4 : 8 * 6 ≤ D.R.f * D.R.r` using `Nat.mul_le_mul h2 h3`. Establish `h5 : D.R.f * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1)` using `by first`. Consider the case `exact Nat.le_mul_of_pos_right _ (by omega)`.

Consider the case `exact Nat.le_mul_of_pos_right (by omega)`. Generalize the expression as in `D.R.f * D.R.r * (D.R.r + 1) = X at *`. Generalize the expression as in `D.R.f * D.R.r = Y at *`. Use linear arithmetic over natural numbers and integers. Establish `hq0lo : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℕ)`.

Unfold `q0N`. Establish `h` using `Nat.le_ceil (L.sc.b / T.TO)`. Establish `e : (T.TO : ℝ) * (L.sc.b / T.TO) = L.sc.b`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation.

Establish `hq0hi : (T.TO : ℝ) * (q0N T : ℕ) ≤ L.sc.b + T.TO`. Unfold `q0N`. Establish `h` using `Nat.ceil_lt_add_one (div_nonneg hb.le hTOpos.le)`. Establish `e : (T.TO : ℝ) * (L.sc.b / T.TO + 1) = L.sc.b + T.TO`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Use `mul_le_mul_of_nonneg_left h.le hTOpos.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `{ forty_eight_le_constant := by nlinarith k8 := by linarith Ak := by nlinarith [mul_le_mul hfk hr2k (Nat.cast_nonneg _) (Nat.cast_nonneg _)] sb_sq := by`. Rewrite using `[← Real.sqrt_eq_rpow]`.

Conclude with `Real.mul_self_sqrt hb.le`. Use `PPA := hPPA`. Use `h32 := T.precision_cube_order_sq_le_sqrt`. Use `hTP := T.TO_PP'`. Use `one_le_order_alt := by exact_mod_cast (by omega : 1 ≤ T.TO)`.

Use `rd1 := hrd1`. Use `rd8 := discriminant_pow_eight_le_sqrt P S`. Use `r6 := hr6`. Use `rA := by nlinarith`. Use `two_le_degree_alt := by have : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _; linarith`.

Use `W := by exact_mod_cast T.TO_nW`. Use `forty_mul_degree_le_order := by exact_mod_cast T.TO_40`. Use `forty_le_weight_count := by exact_mod_cast hnW`. Use `projectivePointSizes := Nat.cast_nonneg _`. Use `nPW := by exact_mod_cast T.nW_lo.2.2`.

Use `q0lo := hq0lo`. Use `q0hi := hq0hi }`.
-/
theorem rn_of (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) :
    Rn ((D.R.f : ℝ) * D.R.r) D.R.k L.sc.b (L.sc.b ^ ((1 : ℝ) / 2)) T.PP T.TO D.host.rdE D.R.r ((T.Dp : ℝ) + 2) T.nWn T.nP
      (q0N T) := by
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
  have hr6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast r_ge D
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast r_le_2k D
  have hz1 : (1 : ℝ) ≤ zBase L := le_trans (by norm_num) hZ
  have hz12 := zBase_pow_twelve_le T hz1
  have hAZ := A_le_Z L
  have hzz2 : zBase L ^ 2 ≤ zBase L ^ 12 := by
    first
    | exact pow_le_pow_right₀ hz1 (by norm_num)
    | exact pow_le_pow_right hz1 (by norm_num)
  have hPPA : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ T.PP := by
    have h1 : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ zBase L * zBase L :=
      mul_le_mul hZ hAZ (by positivity) (by linarith)
    nlinarith
  have hTO40 := T.TO_40
  have hTOpos : (0 : ℝ) < T.TO := by exact_mod_cast (by omega : 0 < T.TO)
  have hb := b_pos L
  have hrd1 : (1 : ℝ) ≤ D.host.rdE := by
    have hd : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
      have h := NumberField.discr_ne_zero D.host.E
      have h' : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h
      exact_mod_cast h'
    unfold Host.rdE
    exact Real.one_le_rpow hd (by positivity)
  have hnW : 40 ≤ T.nWn := by
    have h1 := T.nW_lo.1
    have h2 := f_ge D
    have h3 := r_ge D
    have h4 : 8 * 6 ≤ D.R.f * D.R.r := Nat.mul_le_mul h2 h3
    have h5 : D.R.f * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := by
      first
      | exact Nat.le_mul_of_pos_right _ (by omega)
      | exact Nat.le_mul_of_pos_right (by omega)
    generalize D.R.f * D.R.r * (D.R.r + 1) = X at *
    generalize D.R.f * D.R.r = Y at *
    omega
  have hq0lo : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℕ) := by
    unfold q0N
    have h := Nat.le_ceil (L.sc.b / T.TO)
    have e : (T.TO : ℝ) * (L.sc.b / T.TO) = L.sc.b := by
      field_simp
    calc L.sc.b = (T.TO : ℝ) * (L.sc.b / T.TO) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h hTOpos.le
  have hq0hi : (T.TO : ℝ) * (q0N T : ℕ) ≤ L.sc.b + T.TO := by
    unfold q0N
    have h := Nat.ceil_lt_add_one (div_nonneg hb.le hTOpos.le)
    have e : (T.TO : ℝ) * (L.sc.b / T.TO + 1) = L.sc.b + T.TO := by
      field_simp
      try ring
    have := mul_le_mul_of_nonneg_left h.le hTOpos.le
    linarith
  exact
    { forty_eight_le_constant := by nlinarith
      k8 := by linarith
      Ak := by nlinarith [mul_le_mul hfk hr2k (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      sb_sq := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.mul_self_sqrt hb.le
      PPA := hPPA
      h32 := T.precision_cube_order_sq_le_sqrt
      hTP := T.TO_PP'
      one_le_order_alt := by exact_mod_cast (by omega : 1 ≤ T.TO)
      rd1 := hrd1
      rd8 := discriminant_pow_eight_le_sqrt P S
      r6 := hr6
      rA := by nlinarith
      two_le_degree_alt := by have : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _; linarith
      W := by exact_mod_cast T.TO_nW
      forty_mul_degree_le_order := by exact_mod_cast T.TO_40
      forty_le_weight_count := by exact_mod_cast hnW
      projectivePointSizes := Nat.cast_nonneg _
      nPW := by exact_mod_cast T.nW_lo.2.2
      q0lo := hq0lo
      q0hi := hq0hi }

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end

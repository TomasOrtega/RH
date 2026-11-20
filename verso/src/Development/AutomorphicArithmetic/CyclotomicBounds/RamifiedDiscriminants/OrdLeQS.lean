import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.FrobeniusLocalisation.inertQ
import Development.AutomorphicArithmetic.FrobeniusLocalisation.InertD

open UpperTheory.HF
open Formalism.HC
open scoped Pointwise

/- English proof (translation)
Simplify using `[Nat.factorization_eq_zero_of_not_dvd h]`.
-/
private theorem ordCompl_eq_self_of_not_dvd {n p : ℕ} (h : ¬p ∣ n) : ordCompl[p] n = n := by
  simp [Nat.factorization_eq_zero_of_not_dvd h]

/- English proof (translation)
Establish `hq` using `H.q_prime`. Establish `h1 : ¬H.q ∣ H.QS` using `(Nat.Prime.coprime_iff_not_dvd hq).1 H.coprime_QS_q.symm`. Establish `h2 : ¬H.q ∣ H.d` using `(Nat.Prime.coprime_iff_not_dvd hq).1 (Nat.Coprime.coprime_dvd_left (dvd_mul_left H.d H.QS) H.coprime_QSd_q).symm`. Establish `h3 : ordCompl[H.q] H.q = 1`. Simplify using `using Nat.ordCompl_self_pow (k := 1) hq`.

Simplify using `only [HostRaw.condN, Nat.ordCompl_mul, h3, ordCompl_eq_self_of_not_dvd h1, ordCompl_eq_self_of_not_dvd h2, mul_one]`.
-/
private theorem ordCompl_q' {φ : Frame} (H : HostRaw φ) : ordCompl[H.q] H.condN = H.QS * H.d := by
  have hq := H.q_prime
  have h1 : ¬H.q ∣ H.QS := (Nat.Prime.coprime_iff_not_dvd hq).1 H.coprime_QS_q.symm
  have h2 : ¬H.q ∣ H.d := (Nat.Prime.coprime_iff_not_dvd hq).1
    (Nat.Coprime.coprime_dvd_left (dvd_mul_left H.d H.QS) H.coprime_QSd_q).symm
  have h3 : ordCompl[H.q] H.q = 1 := by
    simpa using Nat.ordCompl_self_pow (k := 1) hq
  simp only [HostRaw.condN, Nat.ordCompl_mul, h3, ordCompl_eq_self_of_not_dvd h1, ordCompl_eq_self_of_not_dvd h2, mul_one]

/- English proof (translation)
Establish `hd` using `H.d_prime`. Establish `h3 : ordCompl[H.d] H.d = 1`. Simplify using `using Nat.ordCompl_self_pow (k := 1) hd`. Simplify using `only [HostRaw.condN]`. Rewrite using `[Nat.ordCompl_mul, h3, mul_one, ordCompl_eq_self_of_not_dvd H.d_not_dvd_QSq]`.
-/
private theorem ordCompl_d' {φ : Frame} (H : HostRaw φ) : ordCompl[H.d] H.condN = H.QS * H.q := by
  have hd := H.d_prime
  have h3 : ordCompl[H.d] H.d = 1 := by
    simpa using Nat.ordCompl_self_pow (k := 1) hd
  simp only [HostRaw.condN]
  rw [Nat.ordCompl_mul, h3, mul_one, ordCompl_eq_self_of_not_dvd H.d_not_dvd_QSq]

/- English proof (translation)
Take `⟨x, hxa, hxb⟩` from `Nat.chineseRemainder hab 1 (u : ZMod H.condN).val`. Establish `hu : Nat.Coprime (u : ZMod H.condN).val H.condN` using `ZMod.val_coe_unit_coprime u`. Establish `hxa' : Nat.Coprime x a`. Use `Nat.ModEq.gcd_eq hxa` as an intermediate fact. Rewrite using `[Nat.Coprime, this]`.

Simplify using the standard rewrite rules. Establish `hxb' : Nat.Coprime x b`. Use `Nat.ModEq.gcd_eq hxb` as an intermediate fact. Rewrite using `[Nat.Coprime, this]`. Conclude with `Nat.Coprime.coprime_dvd_right (hN ▸ dvd_mul_left b a) hu`.

Establish `hx : Nat.Coprime x H.condN`. Rewrite using `[hN]`. Conclude with `Nat.Coprime.mul_right hxa' hxb'`. Use `⟨ZMod.unitOfCoprime x hx, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((H.val_unitOfCoprime hx).of_dvd (hN ▸ dvd_mul_right a b)).trans hxa`.

Conclude with `((H.val_unitOfCoprime hx).of_dvd (hN ▸ dvd_mul_left b a)).trans hxb`.
-/
private theorem crt_unit {φ : Frame} (H : HostRaw φ) {a b : ℕ} (hab : a.Coprime b) (hN : H.condN = a * b)
    (u : (ZMod H.condN)ˣ) : ∃ v : (ZMod H.condN)ˣ, (v : ZMod H.condN).val ≡ 1 [MOD a] ∧
      (v : ZMod H.condN).val ≡ (u : ZMod H.condN).val [MOD b] := by
  obtain ⟨x, hxa, hxb⟩ := Nat.chineseRemainder hab 1 (u : ZMod H.condN).val
  have hu : Nat.Coprime (u : ZMod H.condN).val H.condN := ZMod.val_coe_unit_coprime u
  have hxa' : Nat.Coprime x a := by
    have := Nat.ModEq.gcd_eq hxa
    rw [Nat.Coprime, this]
    simp
  have hxb' : Nat.Coprime x b := by
    have := Nat.ModEq.gcd_eq hxb
    rw [Nat.Coprime, this]
    exact Nat.Coprime.coprime_dvd_right (hN ▸ dvd_mul_left b a) hu
  have hx : Nat.Coprime x H.condN := by
    rw [hN]
    exact Nat.Coprime.mul_right hxa' hxb'
  refine ⟨ZMod.unitOfCoprime x hx, ?_, ?_⟩
  · exact ((H.val_unitOfCoprime hx).of_dvd (hN ▸ dvd_mul_right a b)).trans hxa
  · exact ((H.val_unitOfCoprime hx).of_dvd (hN ▸ dvd_mul_left b a)).trans hxb

/- English proof (translation)
Introduce `g hg`. Rewrite `hg` using `[SetLike.mem_coe, HostRaw.mem_imgOne H H.QS_dvd_condN]`. Take `⟨u, hu1, rfl⟩` from `hg`. Establish `hN : H.condN = H.QS * H.d * H.q` using `by simp only [HostRaw.condN]; ring`. Take `⟨v, hv1, hv2⟩` from `crt_unit H H.coprime_QSd_q hN u`.

Use `set w : (ZMod H.condN)ˣ := v⁻¹ * u with hw`. Establish `hvw : ((v : ZMod H.condN) * (w : ZMod H.condN)) = (u : ZMod H.condN)`. Rewrite using `[← Units.val_mul, hw, mul_inv_cancel_left]`. Establish `hmod : (u : ZMod H.condN).val ≡ (v : ZMod H.condN).val * (w : ZMod H.condN).val [MOD H.condN]`. Rewrite using `[← hvw, ZMod.val_mul]`.

Conclude with `Nat.mod_modEq _ _`. Establish `hQSN : H.QS ∣ H.condN` using `H.QS_dvd_condN`. Establish `hqN : H.q ∣ H.condN` using `by rw [hN]; exact dvd_mul_left _ _`. Establish `hwQS : (w : ZMod H.condN).val ≡ 1 [MOD H.QS]`. Establish `e1` using `hmod.of_dvd hQSN`.

Establish `e2 : (v : ZMod H.condN).val ≡ 1 [MOD H.QS]` using `hv1.of_dvd (dvd_mul_right _ _)`. Establish `e3 : (v : ZMod H.condN).val * (w : ZMod H.condN).val ≡ 1 * (w : ZMod H.condN).val [MOD H.QS]` using `e2.mul_right _`. Rewrite `e3` using `[one_mul]`. Conclude with `e3.symm.trans (e1.symm.trans hu1)`. Establish `hwq : (w : ZMod H.condN).val ≡ 1 [MOD H.q]`.

Establish `e1` using `hmod.of_dvd hqN`. Establish `hcop : Nat.Coprime H.q (v : ZMod H.condN).val` using `(Nat.Coprime.coprime_dvd_right hqN (ZMod.val_coe_unit_coprime v)).symm`. Apply `Nat.ModEq.cancel_left_of_coprime hcop` to reduce the goal to its premises. Rewrite using `[mul_one]`. Conclude with `e1.symm.trans hv2.symm`.

Establish `hw1 : (w : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q]` using `(Nat.modEq_and_modEq_iff_modEq_mul H.coprime_QS_q).1 ⟨hwQS, hwq⟩`. Use `Set.mem_mul.2 ⟨H.art v, ?_, H.art w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, HostRaw.mem_inertG]`. Use `⟨v, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[ordCompl_q' H]`.

Conclude with `hv1`. Rewrite using `[SetLike.mem_coe, HostRaw.mem_inertG]`. Use `⟨w, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[ordCompl_d' H]`. Conclude with `hw1`.

Rewrite using `[← map_mul, hw, mul_inv_cancel_left]`.
-/
private theorem img_sub {φ : Frame} (H : HostRaw φ) :
    (H.imgOne H.QS : Set φ.GG) ⊆ (H.inertG H.q : Set φ.GG) * (H.inertG H.d : Set φ.GG) := by
  intro g hg
  rw [SetLike.mem_coe, HostRaw.mem_imgOne H H.QS_dvd_condN] at hg
  obtain ⟨u, hu1, rfl⟩ := hg
  have hN : H.condN = H.QS * H.d * H.q := by simp only [HostRaw.condN]; ring
  obtain ⟨v, hv1, hv2⟩ := crt_unit H H.coprime_QSd_q hN u
  set w : (ZMod H.condN)ˣ := v⁻¹ * u with hw
  have hvw : ((v : ZMod H.condN) * (w : ZMod H.condN)) = (u : ZMod H.condN) := by
    rw [← Units.val_mul, hw, mul_inv_cancel_left]
  have hmod : (u : ZMod H.condN).val ≡ (v : ZMod H.condN).val * (w : ZMod H.condN).val [MOD H.condN] := by
    rw [← hvw, ZMod.val_mul]
    exact Nat.mod_modEq _ _
  have hQSN : H.QS ∣ H.condN := H.QS_dvd_condN
  have hqN : H.q ∣ H.condN := by rw [hN]; exact dvd_mul_left _ _
  have hwQS : (w : ZMod H.condN).val ≡ 1 [MOD H.QS] := by
    have e1 := hmod.of_dvd hQSN
    have e2 : (v : ZMod H.condN).val ≡ 1 [MOD H.QS] := hv1.of_dvd (dvd_mul_right _ _)
    have e3 : (v : ZMod H.condN).val * (w : ZMod H.condN).val ≡ 1 * (w : ZMod H.condN).val [MOD H.QS] :=
      e2.mul_right _
    rw [one_mul] at e3
    exact e3.symm.trans (e1.symm.trans hu1)
  have hwq : (w : ZMod H.condN).val ≡ 1 [MOD H.q] := by
    have e1 := hmod.of_dvd hqN
    have hcop : Nat.Coprime H.q (v : ZMod H.condN).val :=
      (Nat.Coprime.coprime_dvd_right hqN (ZMod.val_coe_unit_coprime v)).symm
    apply Nat.ModEq.cancel_left_of_coprime hcop
    rw [mul_one]
    exact e1.symm.trans hv2.symm
  have hw1 : (w : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul H.coprime_QS_q).1 ⟨hwQS, hwq⟩
  refine Set.mem_mul.2 ⟨H.art v, ?_, H.art w, ?_, ?_⟩
  · rw [SetLike.mem_coe, HostRaw.mem_inertG]
    refine ⟨v, ?_, rfl⟩
    rw [ordCompl_q' H]
    exact hv1
  · rw [SetLike.mem_coe, HostRaw.mem_inertG]
    refine ⟨w, ?_, rfl⟩
    rw [ordCompl_d' H]
    exact hw1
  · rw [← map_mul, hw, mul_inv_cancel_left]

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Take `⟨m, rfl⟩` from `h`. Break down `Nat.eq_zero_or_pos m with hm | hm` into its components or cases. Substitute `hm` using the available equality.

Simplify using the standard rewrite rules. Distinguish the cases in `h2 : 2 ∣ m`. Rewrite using `[Nat.totient_mul_of_prime_of_dvd Nat.prime_two h2]`. Use `ih m (by omega) h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Nat.totient_mul_of_prime_of_not_dvd Nat.prime_two h2]`. Use `Nat.totient_le m` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem two_totient_le {n : ℕ} (h : 2 ∣ n) : 2 * Nat.totient n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨m, rfl⟩ := h
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    by_cases h2 : 2 ∣ m
    · rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two h2]
      have := ih m (by omega) h2
      omega
    · rw [Nat.totient_mul_of_prime_of_not_dvd Nat.prime_two h2]
      have := Nat.totient_le m
      omega

/- English proof (translation)
Introduce `φ H`. Use `set R := H.toHostRaw with hR`. Establish `hsurj : Function.Surjective R.art` using `Der.art_surj R`. Establish `hQS0 : R.QS ≠ 0` using `R.QS_ne_zero`. Use `haveI : NeZero R.QS := ⟨hQS0⟩`.

Establish `hcard : Nat.card φ.GG = 4 * φ.ord` using `φ.natCard_GG`. Establish `h1 : φ.ord ≤ Nat.totient R.QS`. Break down `Nat.eq_zero_or_pos φ.ord with h0 | hpos` into its components or cases. Rewrite using `[h0]`. Conclude with `Nat.zero_le _`.

Use `haveI : Finite φ.GG := Nat.finite_of_card_ne_zero (by omega)`. Use `set I := HostRaw.imgOne R R.QS with hI`. Establish `hidx : I.index ≤ Nat.totient R.QS`. Establish `hdvd : I.index ∣ (HostRaw.unitsOne R R.QS).index` using `Subgroup.index_map_dvd (HostRaw.unitsOne R R.QS) hsurj`. Establish `key : ∀ n : ℕ, n = R.QS → Nat.card (ZMod n)ˣ ≤ Nat.totient R.QS`.

Introduce and unpack `n rfl`. Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]`. Establish `hg : R.QS.gcd R.condN = R.QS` using `Nat.gcd_eq_left R.QS_dvd_condN`. Establish `hK : (HostRaw.unitsOne R R.QS).index ≤ Nat.totient R.QS`. Simplify using `only [HostRaw.unitsOne]`.

Rewrite using `[Subgroup.index_ker]`. Conclude with `(Subgroup.card_le_card_group _).trans (key _ hg)`. Establish `hpos' : 0 < (HostRaw.unitsOne R R.QS).index` using `Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite`. Conclude with `(Nat.le_of_dvd hpos' hdvd).trans hK`. Establish `hI4 : Nat.card I ≤ 4`.

Establish `hsub` using `img_sub R`. Establish `hm : Nat.card ((I : Set φ.GG)) ≤ Nat.card ((HostRaw.inertG R R.q : Set φ.GG) * (HostRaw.inertG R R.d : Set φ.GG))` using `Nat.card_mono (Set.toFinite _) hsub`. Establish `hmul` using `Set.natCard_mul_le (s := (HostRaw.inertG R R.q : Set φ.GG)) (t := (HostRaw.inertG R R.d : Set φ.GG))`. Establish `hq2 : Nat.card (HostRaw.inertG R R.q) ≤ 2` using `(inert_q H).1`. Establish `hd2 : Nat.card (HostRaw.inertG R R.d) = 2` using `(inert_d H).2.1`.

Establish `e1 : Nat.card I = Nat.card ((I : Set φ.GG))` using `rfl`. Establish `e2 : Nat.card (HostRaw.inertG R R.q) = Nat.card ((HostRaw.inertG R R.q : Set φ.GG))` using `rfl`. Establish `e3 : Nat.card (HostRaw.inertG R R.d) = Nat.card ((HostRaw.inertG R R.d : Set φ.GG))` using `rfl`. Rewrite using `[e1]`. Rewrite `hmul` using `[← e2, ← e3, hd2]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hci` using `Subgroup.card_mul_index I`. Rewrite `hci` using `[hcard]`. Establish `: 4 * φ.ord ≤ 4 * Nat.totient R.QS`. Rewrite using `[← hci]`.

Conclude with `Nat.mul_le_mul hI4 hidx`. Use linear arithmetic over natural numbers and integers. Establish `h2 : 2 * φ.ord ≤ R.QS` using `(Nat.mul_le_mul_left 2 h1).trans (two_totient_le R.two_dvd_QS)`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Establish `hqd : R.q * R.d ≤ (R.q * R.d) ^ 2` using `Nat.le_self_pow (by norm_num) _`.

Establish `hsq : (2 * φ.ord) ^ 2 ≤ R.QS ^ 2` using `Nat.pow_le_pow_left h2 2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.KR.two_ord_le_QS :
    ∀ {φ : Frame} (H : HostAx φ), φ.ord ≤ Nat.totient H.QS ∧ 2 * φ.ord ≤ H.QS ∧ 4 * φ.ord ^ 2 * H.q * H.d ≤ (H.QS * H.q * H.d) ^ 2 := by
  intro φ H
  set R := H.toHostRaw with hR
  have hsurj : Function.Surjective R.art := Der.art_surj R
  have hQS0 : R.QS ≠ 0 := R.QS_ne_zero
  haveI : NeZero R.QS := ⟨hQS0⟩
  have hcard : Nat.card φ.GG = 4 * φ.ord := φ.natCard_GG
  have h1 : φ.ord ≤ Nat.totient R.QS := by
    rcases Nat.eq_zero_or_pos φ.ord with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    haveI : Finite φ.GG := Nat.finite_of_card_ne_zero (by omega)
    set I := HostRaw.imgOne R R.QS with hI
    have hidx : I.index ≤ Nat.totient R.QS := by
      have hdvd : I.index ∣ (HostRaw.unitsOne R R.QS).index :=
        Subgroup.index_map_dvd (HostRaw.unitsOne R R.QS) hsurj
      have key : ∀ n : ℕ, n = R.QS → Nat.card (ZMod n)ˣ ≤ Nat.totient R.QS := by
        rintro n rfl
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      have hg : R.QS.gcd R.condN = R.QS := Nat.gcd_eq_left R.QS_dvd_condN
      have hK : (HostRaw.unitsOne R R.QS).index ≤ Nat.totient R.QS := by
        simp only [HostRaw.unitsOne]
        rw [Subgroup.index_ker]
        exact (Subgroup.card_le_card_group _).trans (key _ hg)
      have hpos' : 0 < (HostRaw.unitsOne R R.QS).index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      exact (Nat.le_of_dvd hpos' hdvd).trans hK
    have hI4 : Nat.card I ≤ 4 := by
      have hsub := img_sub R
      have hm : Nat.card ((I : Set φ.GG)) ≤ Nat.card ((HostRaw.inertG R R.q : Set φ.GG) * (HostRaw.inertG R R.d : Set φ.GG)) :=
        Nat.card_mono (Set.toFinite _) hsub
      have hmul := Set.natCard_mul_le (s := (HostRaw.inertG R R.q : Set φ.GG)) (t := (HostRaw.inertG R R.d : Set φ.GG))
      have hq2 : Nat.card (HostRaw.inertG R R.q) ≤ 2 := (inert_q H).1
      have hd2 : Nat.card (HostRaw.inertG R R.d) = 2 := (inert_d H).2.1
      have e1 : Nat.card I = Nat.card ((I : Set φ.GG)) := rfl
      have e2 : Nat.card (HostRaw.inertG R R.q) = Nat.card ((HostRaw.inertG R R.q : Set φ.GG)) := rfl
      have e3 : Nat.card (HostRaw.inertG R R.d) = Nat.card ((HostRaw.inertG R R.d : Set φ.GG)) := rfl
      rw [e1]
      rw [← e2, ← e3, hd2] at hmul
      nlinarith
    have hci := Subgroup.card_mul_index I
    rw [hcard] at hci
    have : 4 * φ.ord ≤ 4 * Nat.totient R.QS := by
      rw [← hci]
      exact Nat.mul_le_mul hI4 hidx
    omega
  have h2 : 2 * φ.ord ≤ R.QS :=
    (Nat.mul_le_mul_left 2 h1).trans (two_totient_le R.two_dvd_QS)
  refine ⟨h1, h2, ?_⟩
  have hqd : R.q * R.d ≤ (R.q * R.d) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq : (2 * φ.ord) ^ 2 ≤ R.QS ^ 2 := Nat.pow_le_pow_left h2 2
  calc 4 * φ.ord ^ 2 * H.q * H.d = (2 * φ.ord) ^ 2 * (R.q * R.d) := by rw [hR]; ring
    _ ≤ R.QS ^ 2 * (R.q * R.d) ^ 2 := Nat.mul_le_mul hsq hqd
    _ = (H.QS * H.q * H.d) ^ 2 := by rw [hR]; ring

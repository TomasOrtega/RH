import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomicAlt
import Development.AutomorphicArithmetic.ResidueCharacters.FiniteRoots

open Formalism Formalism.MainNotions

namespace UpperTheory.N.LocNum

/- English proof (translation)
Establish `hn0 : LocalSituation.n0 l (h + h) ≤ Nat.log l (2 * h) + 1`. Use `Nat.sInf_le ?_` and prove the remaining obligations. Establish `h1` using `Nat.lt_pow_succ_log_self hl.one_lt (2 * h)`. Establish `h2 : 1 ≤ l - 1` using `by have := hl.two_le; omega`. Use `show h + h ≤ l ^ (Nat.log l (2 * h) + 1) * (l - 1)`.

Combine the equalities or inequalities in the displayed calculation. Unfold `LocalSituation.mN`. Use linear arithmetic over natural numbers and integers.
-/
theorem mN_le (l s h : ℕ) (hl : l.Prime) : LocalSituation.mN l s (h + h) ≤ 2 * s + Nat.log l (2 * h) + 2 := by
  have hn0 : LocalSituation.n0 l (h + h) ≤ Nat.log l (2 * h) + 1 := by
    refine Nat.sInf_le ?_
    have h1 := Nat.lt_pow_succ_log_self hl.one_lt (2 * h)
    have h2 : 1 ≤ l - 1 := by have := hl.two_le; omega
    show h + h ≤ l ^ (Nat.log l (2 * h) + 1) * (l - 1)
    calc h + h = 2 * h := by ring
      _ ≤ l ^ (Nat.log l (2 * h) + 1) := h1.le
      _ ≤ _ := Nat.le_mul_of_pos_right _ h2
  unfold LocalSituation.mN; omega

/- English proof (translation)
Establish `hfin : U'.Finite` using `(U.finite_toSet).subset hU`. Unfold `LocalSituation.rI`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`. Establish `hsub : hfin.toFinset ⊆ U`. Introduce `x hx`.

Conclude with `hU ((Set.Finite.mem_toFinset hfin).1 hx)`. Establish `hcard : hfin.toFinset.card ≤ n` using `(Finset.card_le_card hsub).trans hn`. Establish `hterm : ∀ u ∈ hfin.toFinset, (∑ᶠ (_ : u ≠ i), (m + LocalSituation.vZ l (u - i))) ≤ m + Nat.log l (2 * h)`. Introduce `u hu`. Rewrite using `[finsum_eq_if]`.

Use `split_ifs with hui`. Establish `huU` using `hsub hu`. Take `⟨hb1, hb2⟩` from `hb u huU`. Establish `hz : (u - i).natAbs ≤ 2 * h` using `by omega`. Establish `hv : LocalSituation.vZ l (u - i) ≤ Nat.log l (2 * h)`.

Unfold `LocalSituation.vZ padicValInt`. Conclude with `(padicValNat_le_nat_log _).trans (Nat.log_mono_right hz)`. Use linear arithmetic over natural numbers and integers. Conclude with `Nat.zero_le _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rI_le (l m h n : ℕ) (hl : l.Prime) (U : Finset ℤ) (U' : Set ℤ) (hU : U' ⊆ U) (hn : U.card ≤ n)
    (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (i : ℤ) (hi : 0 ≤ i) (hi' : i ≤ h) :
    LocalSituation.rI l m U' i ≤ n * (m + Nat.log l (2 * h)) := by
  classical
  have hfin : U'.Finite := (U.finite_toSet).subset hU
  unfold LocalSituation.rI
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : hfin.toFinset ⊆ U := by
    intro x hx
    exact hU ((Set.Finite.mem_toFinset hfin).1 hx)
  have hcard : hfin.toFinset.card ≤ n := (Finset.card_le_card hsub).trans hn
  have hterm : ∀ u ∈ hfin.toFinset, (∑ᶠ (_ : u ≠ i), (m + LocalSituation.vZ l (u - i))) ≤ m + Nat.log l (2 * h) := by
    intro u hu
    rw [finsum_eq_if]
    split_ifs with hui
    · have huU := hsub hu
      obtain ⟨hb1, hb2⟩ := hb u huU
      have hz : (u - i).natAbs ≤ 2 * h := by omega
      have hv : LocalSituation.vZ l (u - i) ≤ Nat.log l (2 * h) := by
        unfold LocalSituation.vZ padicValInt
        exact (padicValNat_le_nat_log _).trans (Nat.log_mono_right hz)
      omega
    · exact Nat.zero_le _
  calc ∑ u ∈ hfin.toFinset, (∑ᶠ (_ : u ≠ i), (m + LocalSituation.vZ l (u - i)))
      ≤ hfin.toFinset.card • (m + Nat.log l (2 * h)) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = hfin.toFinset.card * (m + Nat.log l (2 * h)) := by rw [smul_eq_mul]
    _ ≤ n * (m + Nat.log l (2 * h)) := Nat.mul_le_mul_right _ hcard

/- English proof (translation)
Use `set M := LocalSituation.mN l (sN l N) (h + h) with hM`. Establish `hMle : M ≤ 2 * sN l N + Nat.log l (2 * h) + 2` using `mN_le l (sN l N) h hl`. Establish `hs : 1 ≤ sN l N` using `le_max_left _ _`. Establish `hL : lamN l N h = sN l N + Nat.log l (2 * h) + Nat.log l N + 1` using `rfl`. Establish `hterm : ∀ i ∈ Finset.Ico (0 : ℤ) (k : ℤ), 2 + max 1 (LocalSituation.rI l M U' i) ≤ 3 * (n + 1) * lamN l N h`.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Ico]`. Establish `hr` using `rI_le l M h n hl U U' hU hn hb i hi.1 (by omega)`. Establish `hr2 : n * (M + Nat.log l (2 * h)) ≤ n * (2 * lamN l N h)` using `Nat.mul_le_mul_left _ (by omega)`. Establish `hmax : max 1 (LocalSituation.rI l M U' i) ≤ 1 + LocalSituation.rI l M U' i` using `max_le (by omega) (by omega)`.

Establish `hL1 : 1 ≤ lamN l N h` using `by omega`. Use the polynomial consequences of the given equalities and inequalities. Unfold `LocalSituation.cLL`. Establish `hsum` using `Finset.sum_le_card_nsmul _ _ _ hterm`. Rewrite `hsum` using `[Int.card_Ico, smul_eq_mul]`.

Simplify using `only [sub_zero, Int.toNat_natCast] at hsum`. Establish `hvd2 : vd ≤ 2 * lamN l N h` using `by omega`. Use linear arithmetic over natural numbers and integers.
-/
theorem cLL_le (l N h n k vd : ℕ) (hl : l.Prime) (U : Finset ℤ) (U' : Set ℤ) (hU : U' ⊆ U) (hn : U.card ≤ n)
    (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (hk : k ≤ h + 1) (hvd : vd ≤ LocalSituation.mN l (sN l N) (h + h)) :
    LocalSituation.cLL l (LocalSituation.mN l (sN l N) (h + h)) vd U' 0 (k : ℤ) ≤ 2 * lamN l N h + k * (3 * (n + 1) * lamN l N h) := by
  set M := LocalSituation.mN l (sN l N) (h + h) with hM
  have hMle : M ≤ 2 * sN l N + Nat.log l (2 * h) + 2 := mN_le l (sN l N) h hl
  have hs : 1 ≤ sN l N := le_max_left _ _
  have hL : lamN l N h = sN l N + Nat.log l (2 * h) + Nat.log l N + 1 := rfl
  have hterm : ∀ i ∈ Finset.Ico (0 : ℤ) (k : ℤ), 2 + max 1 (LocalSituation.rI l M U' i) ≤ 3 * (n + 1) * lamN l N h := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hr := rI_le l M h n hl U U' hU hn hb i hi.1 (by omega)
    have hr2 : n * (M + Nat.log l (2 * h)) ≤ n * (2 * lamN l N h) :=
      Nat.mul_le_mul_left _ (by omega)
    have hmax : max 1 (LocalSituation.rI l M U' i) ≤ 1 + LocalSituation.rI l M U' i := max_le (by omega) (by omega)
    have hL1 : 1 ≤ lamN l N h := by omega
    nlinarith
  unfold LocalSituation.cLL
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [Int.card_Ico, smul_eq_mul] at hsum
  simp only [sub_zero, Int.toNat_natCast] at hsum
  have hvd2 : vd ≤ 2 * lamN l N h := by omega
  omega

/- English proof (translation)
Establish `h3` using `cLL_le l N h n 1 vd hl U U' hU hn hb (by omega) hvd`. Simplify using `only [Nat.cast_one, one_mul] at h3`. Unfold `c0L`. Establish `hL1 : 1 ≤ lamN l N h` using `by unfold lamN; omega`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem latticeExponent_one_le_invariantsKillingExponent (l N h n vd : ℕ) (hl : l.Prime) (U : Finset ℤ) (U' : Set ℤ) (hU : U' ⊆ U) (hn : U.card ≤ n)
    (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (hvd : vd ≤ LocalSituation.mN l (sN l N) (h + h)) :
    LocalSituation.cLL l (LocalSituation.mN l (sN l N) (h + h)) vd U' 0 1 ≤ c0L l N h n := by
  have h3 := cLL_le l N h n 1 vd hl U U' hU hn hb (by omega) hvd
  simp only [Nat.cast_one, one_mul] at h3
  unfold c0L
  have hL1 : 1 ≤ lamN l N h := by unfold lamN; omega
  nlinarith

/- English proof (translation)
Establish `h3` using `cLL_le l N h n (e + 1) vd hl U U' hU hn hb (by omega) hvd`. Move the coercions through the operations in `at h3`. Establish `hs : 1 ≤ sN l N` using `le_max_left _ _`. Establish `hL : lamN l N h = sN l N + Nat.log l (2 * h) + Nat.log l N + 1` using `rfl`. Establish `hv1 : padicValNat l e ≤ e` using `(padicValNat_le_nat_log e).trans (Nat.log_le_self _ _)`.

Establish `hv2 : padicValNat l (e + 1) ≤ e + 1` using `(padicValNat_le_nat_log _).trans (Nat.log_le_self _ _)`. Establish `hd : e / (l - 1) ≤ e` using `Nat.div_le_self _ _`. Unfold `LocalSituation.cTB cBL`. Use `set L := lamN l N h`. Use `set c := LocalSituation.cLL l (LocalSituation.mN l (sN l N) (h + h)) vd U' 0 ((e : ℤ) + 1)`.

Establish `hL1 : 1 ≤ L` using `by omega`. Establish `hsL : sN l N ≤ L` using `by omega`. Establish `hgL : g ≤ L` using `by omega`. Establish `hm1 : (e + 1) * (3 * (n + 1) * L) ≤ t * (3 * (n + 1) * L)` using `Nat.mul_le_mul_right _ (by omega)`. Establish `hm2 : (e + 2) * sN l N ≤ (t + 1) * L` using `Nat.mul_le_mul (by omega) hsL`.

Establish `hX : (t + 1) * L ≤ (t + 1) * (n + 1) * L`. Combine the equalities or inequalities in the displayed calculation. Establish `hY : t + 1 ≤ (t + 1) * L`. Combine the equalities or inequalities in the displayed calculation. Establish `hV : L ≤ (t + 1) * L`.

Combine the equalities or inequalities in the displayed calculation. Establish `hZ : t * (3 * (n + 1) * L) ≤ 3 * ((t + 1) * (n + 1) * L)`. Establish `: t * (3 * (n + 1) * L) = 3 * (t * (n + 1) * L)` using `by ring`. Rewrite using `[this]`. Apply `Nat.mul_le_mul_left` to reduce the goal to its premises.

Apply `Nat.mul_le_mul_right` to reduce the goal to its premises. Conclude with `Nat.mul_le_mul_right _ (by omega)`. Establish `hW : 40 * (t + 1) * (n + 1) * L = 40 * ((t + 1) * (n + 1) * L)` using `by ring`. Rewrite using `[hW]`. Use linear arithmetic over natural numbers and integers.
-/
theorem cTB_le (l N h n t e vd g : ℕ) (hl : l.Prime) (U : Finset ℤ) (U' : Set ℤ) (hU : U' ⊆ U) (hn : U.card ≤ n)
    (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (he : e < t) (ht : t ≤ h) (hvd : vd ≤ LocalSituation.mN l (sN l N) (h + h))
    (hg : g ≤ Nat.log l N + 1) :
    LocalSituation.cTB l (sN l N) e 0 (LocalSituation.cLL l (LocalSituation.mN l (sN l N) (h + h)) vd U' 0 ((e : ℤ) + 1)) + g ≤ cBL l N h n t := by
  have h3 := cLL_le l N h n (e + 1) vd hl U U' hU hn hb (by omega) hvd
  push_cast at h3
  have hs : 1 ≤ sN l N := le_max_left _ _
  have hL : lamN l N h = sN l N + Nat.log l (2 * h) + Nat.log l N + 1 := rfl
  have hv1 : padicValNat l e ≤ e := (padicValNat_le_nat_log e).trans (Nat.log_le_self _ _)
  have hv2 : padicValNat l (e + 1) ≤ e + 1 := (padicValNat_le_nat_log _).trans (Nat.log_le_self _ _)
  have hd : e / (l - 1) ≤ e := Nat.div_le_self _ _
  unfold LocalSituation.cTB cBL
  set L := lamN l N h
  set c := LocalSituation.cLL l (LocalSituation.mN l (sN l N) (h + h)) vd U' 0 ((e : ℤ) + 1)
  have hL1 : 1 ≤ L := by omega
  have hsL : sN l N ≤ L := by omega
  have hgL : g ≤ L := by omega
  have hm1 : (e + 1) * (3 * (n + 1) * L) ≤ t * (3 * (n + 1) * L) := Nat.mul_le_mul_right _ (by omega)
  have hm2 : (e + 2) * sN l N ≤ (t + 1) * L := Nat.mul_le_mul (by omega) hsL
  have hX : (t + 1) * L ≤ (t + 1) * (n + 1) * L := by
    calc (t + 1) * L = 1 * ((t + 1) * L) := by ring
      _ ≤ (n + 1) * ((t + 1) * L) := Nat.mul_le_mul_right _ (by omega)
      _ = (t + 1) * (n + 1) * L := by ring
  have hY : t + 1 ≤ (t + 1) * L := by
    calc t + 1 = (t + 1) * 1 := by ring
      _ ≤ (t + 1) * L := Nat.mul_le_mul_left _ hL1
  have hV : L ≤ (t + 1) * L := by
    calc L = 1 * L := by ring
      _ ≤ (t + 1) * L := Nat.mul_le_mul_right _ (by omega)
  have hZ : t * (3 * (n + 1) * L) ≤ 3 * ((t + 1) * (n + 1) * L) := by
    have : t * (3 * (n + 1) * L) = 3 * (t * (n + 1) * L) := by ring
    rw [this]
    apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul_right
    exact Nat.mul_le_mul_right _ (by omega)
  have hW : 40 * (t + 1) * (n + 1) * L = 40 * ((t + 1) * (n + 1) * L) := by ring
  rw [hW]
  omega

open Formalism.BasicNotions Formalism.BasicNotions.Loc in

/- English proof (translation)
Assemble the required witnesses or components as `⟨Cyc.Kc l (Nat.lcm l N) (Cyc.lcm_pos hC.pos), hC.le, Cyc.good_lcm' hC.pos hC.lvl LL hC.coef, Cyc.Ks_lcm hC.pos, Cyc.GK_normal _, Cyc.val_index_le hC.pos _⟩`.
-/
theorem exists_up {l : ℕ} [Fact l.Prime] {N : ℕ} {K LL : FinExt l} (hC : Cyc N K LL) :
    ∃ K' : FinExt l, K.1 ≤ K'.1 ∧ Good K' (sN l N) LL ∧ Ks K' (sN l N) = K'.1 ∧ (GK K').Normal ∧
      padicValNat l (Module.finrank ℚ_[l] ↥K'.1 / Module.finrank ℚ_[l] ↥K.1) ≤ Nat.log l N + 1 :=
  ⟨Cyc.Kc l (Nat.lcm l N) (Cyc.lcm_pos hC.pos), hC.le, Cyc.good_lcm' hC.pos hC.lvl LL hC.coef, Cyc.Ks_lcm hC.pos,
    Cyc.GK_normal _, Cyc.val_index_le hC.pos _⟩

end UpperTheory.N.LocNum

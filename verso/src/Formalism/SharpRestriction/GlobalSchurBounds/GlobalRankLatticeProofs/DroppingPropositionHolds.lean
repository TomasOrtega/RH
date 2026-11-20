import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory

/- English proof (translation)
The claim follows from `Int.eq_zero_of_abs_lt_dvd (addOrderOf_dvd_iff_zsmul_eq_zero.mpr hk) hlt`.
-/
private theorem eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf {G : Type*} [AddCommGroup G] (a : G) (k : ℤ)
    (hk : k • a = 0) (hlt : |k| < (addOrderOf a : ℤ)) : k = 0 :=
  Int.eq_zero_of_abs_lt_dvd (addOrderOf_dvd_iff_zsmul_eq_zero.mpr hk) hlt

/- English proof (translation)
Rewrite using `[sub_zsmul, sub_zsmul, natCast_zsmul, natCast_zsmul, ← sub_eq_add_neg, ← sub_eq_add_neg]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem sub_zsmul_eq_of_two_eqs {G : Type*} [AddCommGroup G] (a h t u₀ : G) (i j : ℤ) (s s' : ℕ)
    (e : t + i • h = s • a + u₀) (e' : t + j • h = s' • a + u₀) :
    (j - i) • h = ((s' : ℤ) - s) • a := by
  rw [sub_zsmul, sub_zsmul, natCast_zsmul, natCast_zsmul, ← sub_eq_add_neg, ← sub_eq_add_neg]
  calc j • h - i • h = (t + j • h) - (t + i • h) := by abel
    _ = (s' • a + u₀) - (s • a + u₀) := by rw [e, e']
    _ = s' • a - s • a := by abel

/- English proof (translation)
Establish `hL : (4 * L : ℤ) < addOrderOf h` using `by exact_mod_cast hh`. Establish `hdist : ∀ (i j : ℤ) (s s' : ℕ), i₀ ≤ i → i < i₀ + L → i₀ ≤ j → j < i₀ + L → i ≠ j → (j - i) • h = ((s' : ℤ) - s) • a → s ≠ s'`. Introduce `i j s s' hi hi' hj hj' hij e hss`. Substitute `hss` using the available equality. Rewrite `e` using `[sub_self, zero_zsmul]`.

Apply the tactic sequence `have h0 := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf h (j - i) e (by rw [abs_lt]; constructor <;> omega)`. Use linear arithmetic over natural numbers and integers. Establish `k2` using `sub_zsmul_eq_of_two_eqs a h t u₀ i1 i2 s1 s2 e1 e2`. Establish `k3` using `sub_zsmul_eq_of_two_eqs a h t u₀ i1 i3 s1 s3 e1 e3`. Establish `k23` using `sub_zsmul_eq_of_two_eqs a h t u₀ i2 i3 s2 s3 e2 e3`.

Establish `n12` using `hdist i1 i2 s1 s2 a1 b1 a2 b2 h12 k2`. Establish `n13` using `hdist i1 i3 s1 s3 a1 b1 a3 b3 h13 k3`. Establish `n23` using `hdist i2 i3 s2 s3 a2 b2 a3 b3 h23 k23`. Establish `hD : ((i3 - i1) * ((s2 : ℤ) - s1) - (i2 - i1) * ((s3 : ℤ) - s1)) • a = 0`. Rewrite using `[sub_zsmul, ← sub_eq_add_neg, ← smul_smul, ← smul_smul, ← k2, ← k3, smul_smul, smul_smul, mul_comm (i3 - i1), sub_self]`.

Establish `hN : ∀ s ∈ T, 4 * (L : ℤ) * s < addOrderOf a` using `fun s hs => by exact_mod_cast hT s hs`. Establish `hb1` using `hN s1 hs1`. Establish `hb2` using `hN s2 hs2`. Establish `hb3` using `hN s3 hs3`. Establish `hLn : (0 : ℤ) ≤ L` using `by positivity`.

Establish `hs1n : (0 : ℤ) ≤ s1` using `by positivity`. Establish `hs2n : (0 : ℤ) ≤ s2` using `by positivity`. Establish `hs3n : (0 : ℤ) ≤ s3` using `by positivity`. Establish `hy2 : 4 * (L : ℤ) * |(s2 : ℤ) - s1| < addOrderOf a`. Apply the tactic sequence `rcases abs_cases ((s2 : ℤ) - s1) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>`.

Use polynomial arithmetic with `[mul_nonneg hLn hs1n, mul_nonneg hLn hs2n]`. Establish `hy3 : 4 * (L : ℤ) * |(s3 : ℤ) - s1| < addOrderOf a`. Apply the tactic sequence `rcases abs_cases ((s3 : ℤ) - s1) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>`. Use polynomial arithmetic with `[mul_nonneg hLn hs1n, mul_nonneg hLn hs3n]`. Apply the tactic sequence `have hx : |i3 - i1| ≤ L := by rw [abs_le]; constructor <;> omega`.

Apply the tactic sequence `have hu : |i2 - i1| ≤ L := by rw [abs_le]; constructor <;> omega`. Establish `hxy : 4 * |(i3 - i1) * ((s2 : ℤ) - s1)| < addOrderOf a`. Rewrite using `[abs_mul]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hx (abs_nonneg ((s2 : ℤ) - s1))]`. Establish `huv : 4 * |(i2 - i1) * ((s3 : ℤ) - s1)| < addOrderOf a`.

Rewrite using `[abs_mul]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hu (abs_nonneg ((s3 : ℤ) - s1))]`. Establish `hDb : |(i3 - i1) * ((s2 : ℤ) - s1) - (i2 - i1) * ((s3 : ℤ) - s1)| < addOrderOf a`. Rewrite using `[abs_lt]`. Apply the tactic sequence `constructor <;>`.

Combine the linear relations using `[le_abs_self ((i3 - i1) * ((s2 : ℤ) - s1)), neg_abs_le ((i3 - i1) * ((s2 : ℤ) - s1)), le_abs_self ((i2 - i1) * ((s3 : ℤ) - s1)), neg_abs_le ((i2 - i1) * ((s3 : ℤ) - s1)), abs_nonneg ((i3 - i1) * ((s2 : ℤ) - s1)), abs_nonneg ((i2 - i1) * ((s3 : ℤ) - s1))]`. Establish `hD0` using `eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf a _ hD hDb`. Conclude with `hR s1 hs1 s2 hs2 s3 hs3 n12 n13 n23 (i2 - i1) (i3 - i1) (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h12))) hu (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h13))) hx (fun hc => h23 (by omega)) (sub_eq_zero.mp hD0)`.
-/
private theorem false_of_three_distinct_in_window {G : Type*} [AddCommGroup G] (a t h u₀ : G) (T : Finset ℕ) (L : ℕ)
    (hT : ∀ s ∈ T, 4 * L * s < addOrderOf a) (hR : Formalism.FrobeniusOrbits.NoRel T L)
    (hh : 4 * L < addOrderOf h) (i₀ i1 i2 i3 : ℤ) (s1 s2 s3 : ℕ)
    (a1 : i₀ ≤ i1) (b1 : i1 < i₀ + L) (a2 : i₀ ≤ i2) (b2 : i2 < i₀ + L)
    (a3 : i₀ ≤ i3) (b3 : i3 < i₀ + L)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) (hs1 : s1 ∈ T) (hs2 : s2 ∈ T) (hs3 : s3 ∈ T)
    (e1 : t + i1 • h = s1 • a + u₀) (e2 : t + i2 • h = s2 • a + u₀)
    (e3 : t + i3 • h = s3 • a + u₀) : False := by
  have hL : (4 * L : ℤ) < addOrderOf h := by exact_mod_cast hh
  have hdist : ∀ (i j : ℤ) (s s' : ℕ), i₀ ≤ i → i < i₀ + L → i₀ ≤ j → j < i₀ + L → i ≠ j →
      (j - i) • h = ((s' : ℤ) - s) • a → s ≠ s' := by
    intro i j s s' hi hi' hj hj' hij e hss
    subst hss
    rw [sub_self, zero_zsmul] at e
    have h0 := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf h (j - i) e (by rw [abs_lt]; constructor <;> omega)
    omega
  have k2 := sub_zsmul_eq_of_two_eqs a h t u₀ i1 i2 s1 s2 e1 e2
  have k3 := sub_zsmul_eq_of_two_eqs a h t u₀ i1 i3 s1 s3 e1 e3
  have k23 := sub_zsmul_eq_of_two_eqs a h t u₀ i2 i3 s2 s3 e2 e3
  have n12 := hdist i1 i2 s1 s2 a1 b1 a2 b2 h12 k2
  have n13 := hdist i1 i3 s1 s3 a1 b1 a3 b3 h13 k3
  have n23 := hdist i2 i3 s2 s3 a2 b2 a3 b3 h23 k23
  have hD : ((i3 - i1) * ((s2 : ℤ) - s1) - (i2 - i1) * ((s3 : ℤ) - s1)) • a = 0 := by
    rw [sub_zsmul, ← sub_eq_add_neg, ← smul_smul, ← smul_smul, ← k2, ← k3, smul_smul, smul_smul,
      mul_comm (i3 - i1), sub_self]
  have hN : ∀ s ∈ T, 4 * (L : ℤ) * s < addOrderOf a := fun s hs => by exact_mod_cast hT s hs
  have hb1 := hN s1 hs1
  have hb2 := hN s2 hs2
  have hb3 := hN s3 hs3
  have hLn : (0 : ℤ) ≤ L := by positivity
  have hs1n : (0 : ℤ) ≤ s1 := by positivity
  have hs2n : (0 : ℤ) ≤ s2 := by positivity
  have hs3n : (0 : ℤ) ≤ s3 := by positivity
  have hy2 : 4 * (L : ℤ) * |(s2 : ℤ) - s1| < addOrderOf a := by
    rcases abs_cases ((s2 : ℤ) - s1) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hs1n, mul_nonneg hLn hs2n]
  have hy3 : 4 * (L : ℤ) * |(s3 : ℤ) - s1| < addOrderOf a := by
    rcases abs_cases ((s3 : ℤ) - s1) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hs1n, mul_nonneg hLn hs3n]
  have hx : |i3 - i1| ≤ L := by rw [abs_le]; constructor <;> omega
  have hu : |i2 - i1| ≤ L := by rw [abs_le]; constructor <;> omega
  have hxy : 4 * |(i3 - i1) * ((s2 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_right hx (abs_nonneg ((s2 : ℤ) - s1))]
  have huv : 4 * |(i2 - i1) * ((s3 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_right hu (abs_nonneg ((s3 : ℤ) - s1))]
  have hDb : |(i3 - i1) * ((s2 : ℤ) - s1) - (i2 - i1) * ((s3 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_lt]
    constructor <;>
      linarith [le_abs_self ((i3 - i1) * ((s2 : ℤ) - s1)), neg_abs_le ((i3 - i1) * ((s2 : ℤ) - s1)),
        le_abs_self ((i2 - i1) * ((s3 : ℤ) - s1)), neg_abs_le ((i2 - i1) * ((s3 : ℤ) - s1)),
        abs_nonneg ((i3 - i1) * ((s2 : ℤ) - s1)), abs_nonneg ((i2 - i1) * ((s3 : ℤ) - s1))]
  have hD0 := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf a _ hD hDb
  exact hR s1 hs1 s2 hs2 s3 hs3 n12 n13 n23 (i2 - i1) (i3 - i1)
    (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h12))) hu
    (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h13))) hx
    (fun hc => h23 (by omega)) (sub_eq_zero.mp hD0)

/- English proof (translation)
Establish `k` using `sub_zsmul_eq_of_two_eqs a h t u₀ i j s s' e e'`. Establish `hm : ((addOrderOf h : ℤ) * ((s' : ℤ) - s)) • a = 0`. Rewrite using `[← smul_smul, ← k, smul_smul, mul_comm, ← smul_smul, natCast_zsmul, addOrderOf_nsmul_eq_zero, zsmul_zero]`. Establish `hm0 : (0 : ℤ) ≤ (addOrderOf h : ℤ)` using `by positivity`. Establish `hmL : (addOrderOf h : ℤ) ≤ 4 * L` using `by exact_mod_cast hh`.

Establish `hLn : (0 : ℤ) ≤ L` using `by positivity`. Establish `hsn : (0 : ℤ) ≤ s` using `by positivity`. Establish `hsn' : (0 : ℤ) ≤ s'` using `by positivity`. Establish `hb` using `(show 4 * (L : ℤ) * s < addOrderOf a by exact_mod_cast hT s hs)`. Establish `hb'` using `(show 4 * (L : ℤ) * s' < addOrderOf a by exact_mod_cast hT s' hs')`.

Establish `hy : 4 * (L : ℤ) * |(s' : ℤ) - s| < addOrderOf a`. Apply the tactic sequence `rcases abs_cases ((s' : ℤ) - s) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>`. Use polynomial arithmetic with `[mul_nonneg hLn hsn, mul_nonneg hLn hsn']`. Establish `hz` using `eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf a _ hm (by`. Rewrite using `[abs_mul, abs_of_nonneg hm0]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hmL (abs_nonneg ((s' : ℤ) - s))])`. Apply the tactic sequence `rcases mul_eq_zero.mp hz with h0 | h0 <;> omega`.
-/
private theorem eq_of_zsmul_eqs_of_small_orders {G : Type*} [AddCommGroup G] (a t h u₀ : G) (T : Finset ℕ) (L : ℕ)
    (hT : ∀ s ∈ T, 4 * L * s < addOrderOf a) (hpos : 0 < addOrderOf h)
    (hh : addOrderOf h ≤ 4 * L) (i j : ℤ) (s s' : ℕ) (hs : s ∈ T) (hs' : s' ∈ T)
    (e : t + i • h = s • a + u₀) (e' : t + j • h = s' • a + u₀) : s = s' := by
  have k := sub_zsmul_eq_of_two_eqs a h t u₀ i j s s' e e'
  have hm : ((addOrderOf h : ℤ) * ((s' : ℤ) - s)) • a = 0 := by
    rw [← smul_smul, ← k, smul_smul, mul_comm, ← smul_smul, natCast_zsmul,
      addOrderOf_nsmul_eq_zero, zsmul_zero]
  have hm0 : (0 : ℤ) ≤ (addOrderOf h : ℤ) := by positivity
  have hmL : (addOrderOf h : ℤ) ≤ 4 * L := by exact_mod_cast hh
  have hLn : (0 : ℤ) ≤ L := by positivity
  have hsn : (0 : ℤ) ≤ s := by positivity
  have hsn' : (0 : ℤ) ≤ s' := by positivity
  have hb := (show 4 * (L : ℤ) * s < addOrderOf a by exact_mod_cast hT s hs)
  have hb' := (show 4 * (L : ℤ) * s' < addOrderOf a by exact_mod_cast hT s' hs')
  have hy : 4 * (L : ℤ) * |(s' : ℤ) - s| < addOrderOf a := by
    rcases abs_cases ((s' : ℤ) - s) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hsn, mul_nonneg hLn hsn']
  have hz := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf a _ hm (by
    rw [abs_mul, abs_of_nonneg hm0]
    nlinarith [mul_le_mul_of_nonneg_right hmL (abs_nonneg ((s' : ℤ) - s))])
  rcases mul_eq_zero.mp hz with h0 | h0 <;> omega

/- English proof (translation)
Take `⟨C, -, hT⟩` from `Formalism.FrobeniusOrbits.hostThickExists`. Use `⟨C, fun D Lw hLw => ?_⟩` and prove the remaining obligations. Take `⟨T, hTs, hTR, hTc⟩` from `hT D.R.n0 Lw hLw`. Use `⟨T, ?_, hTc, hTR, ?_⟩` and prove the remaining obligations. Introduce `s hs`.

Establish `h1 : ((4 * Lw * s : ℕ) : ℝ) < (D.R.n0 : ℝ)` using `by exact_mod_cast hTs s hs`. Establish `hL : (2 : ℝ) ≤ Lw` using `by exact_mod_cast hLw`. Rewrite using `[lt_div_iff₀ (by linarith)]`. Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `u₀ t h`. Use `⟨fun hh i₀ => ?_, fun hh => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc push_neg at hc`. Take `⟨i1, hi1, i2, hi2, i3, hi3, h12, h13, h23⟩` from `Finset.two_lt_card.mp hc`. Simplify using `only [Finset.mem_filter, Finset.mem_Ico, transl, Set.mem_setOf_eq] at hi1 hi2 hi3`.

Take `⟨⟨a1, b1⟩, s1, hs1, e1⟩` from `hi1`. Take `⟨⟨a2, b2⟩, s2, hs2, e2⟩` from `hi2`. Take `⟨⟨a3, b3⟩, s3, hs3, e3⟩` from `hi3`. Conclude with `false_of_three_distinct_in_window _ t h u₀ T Lw hTs hTR hh i₀ i1 i2 i3 s1 s2 s3 a1 b1 a2 b2 a3 b3 h12 h13 h23 hs1 hs2 hs3 e1 e2 e3`. Use `haveI hfin : Finite (HH D) := by show Finite (Fin _) infer_instance`.

Establish `hpos : 0 < addOrderOf h` using `addOrderOf_pos h`. Establish `hsub : (coset t h ∩ transl T u₀).Subsingleton`. Introduce and unpack `x ⟨⟨i, rfl⟩, s, hs, ex⟩ y ⟨⟨j, rfl⟩, s', hs', ey⟩`. Establish `hss` using `eq_of_zsmul_eqs_of_small_orders _ t h u₀ T Lw hTs hpos hh i j s s' hs hs' ex ey`. Substitute `hss` using the available equality.

Rewrite using `[ex, ey]`. Break down `hsub.eq_empty_or_singleton with hE | ⟨x, hx⟩` into its components or cases. Rewrite using `[hE, Set.ncard_empty]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hx, Set.ncard_singleton]`.
-/
theorem dropping_proposition_holds : ∃ C : ℝ, ∀ D : D7, Conclusion5 D C := by
  obtain ⟨C, -, hT⟩ := Formalism.FrobeniusOrbits.hostThickExists
  refine ⟨C, fun D Lw hLw => ?_⟩
  obtain ⟨T, hTs, hTR, hTc⟩ := hT D.R.n0 Lw hLw
  refine ⟨T, ?_, hTc, hTR, ?_⟩
  · intro s hs
    have h1 : ((4 * Lw * s : ℕ) : ℝ) < (D.R.n0 : ℝ) := by exact_mod_cast hTs s hs
    have hL : (2 : ℝ) ≤ Lw := by exact_mod_cast hLw
    rw [lt_div_iff₀ (by linarith)]
    push_cast at h1
    linarith
  · intro u₀ t h
    refine ⟨fun hh i₀ => ?_, fun hh => ?_⟩
    · by_contra hc
      push_neg at hc
      obtain ⟨i1, hi1, i2, hi2, i3, hi3, h12, h13, h23⟩ := Finset.two_lt_card.mp hc
      simp only [Finset.mem_filter, Finset.mem_Ico, transl, Set.mem_setOf_eq] at hi1 hi2 hi3
      obtain ⟨⟨a1, b1⟩, s1, hs1, e1⟩ := hi1
      obtain ⟨⟨a2, b2⟩, s2, hs2, e2⟩ := hi2
      obtain ⟨⟨a3, b3⟩, s3, hs3, e3⟩ := hi3
      exact false_of_three_distinct_in_window _ t h u₀ T Lw hTs hTR hh i₀ i1 i2 i3 s1 s2 s3 a1 b1 a2 b2 a3 b3
        h12 h13 h23 hs1 hs2 hs3 e1 e2 e3
    · haveI hfin : Finite (HH D) := by
        show Finite (Fin _)
        infer_instance
      have hpos : 0 < addOrderOf h := addOrderOf_pos h
      have hsub : (coset t h ∩ transl T u₀).Subsingleton := by
        rintro x ⟨⟨i, rfl⟩, s, hs, ex⟩ y ⟨⟨j, rfl⟩, s', hs', ey⟩
        have hss := eq_of_zsmul_eqs_of_small_orders _ t h u₀ T Lw hTs hpos hh i j s s' hs hs' ex ey
        subst hss
        rw [ex, ey]
      rcases hsub.eq_empty_or_singleton with hE | ⟨x, hx⟩
      · rw [hE, Set.ncard_empty]
        omega
      · rw [hx, Set.ncard_singleton]

end Formalism.MainNotions.UnusedSlot33

end

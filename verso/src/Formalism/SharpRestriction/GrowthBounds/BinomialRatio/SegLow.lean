import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptFin
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Finset

/- English proof (translation)
Establish `hFs : ∀ d, ∑ᶠ b, F d b = ∑ b ∈ hfin.toFinset, F d b` using `fun d => by`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `b hb`. Rewrite `hb` using `[Function.mem_support]`. Rewrite using `[Finset.mem_coe, Set.Finite.mem_toFinset]`.

Assume the negation of the conclusion as `hK`. Conclude with `hb (hF0 d b (fun h => hK h.1))`. Establish `hGs : ∑ᶠ b, G b = ∑ b ∈ hfin.toFinset, G b`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `b hb`.

Rewrite `hb` using `[Function.mem_support]`. Rewrite using `[Finset.mem_coe, Set.Finite.mem_toFinset]`. Assume the negation of the conclusion as `hK`. Conclude with `hb (hG0 b hK)`. Rewrite using `[hGs, Finset.sum_congr rfl (fun d _ => hFs d), Finset.sum_comm]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `b hb`. Establish `hK : K b` using `(Set.Finite.mem_toFinset hfin).mp hb`. Rewrite using `[hG1 b hK]`. Establish `hcl : ∀ d ∈ DC, F d b = if d = key b then f b else 0` using `fun d _ => by`.

Distinguish the cases in `hd : d = key b`. Rewrite using `[if_pos hd, hF1 d b hK hd.symm]`. Rewrite using `[if_neg hd, hF0 d b (fun h => hd h.2.symm)]`. Rewrite using `[Finset.sum_congr rfl hcl, Finset.sum_ite_eq']`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem finsum_classes {β γ : Type*} [DecidableEq γ] (K : β → Prop) (hfin : {b | K b}.Finite) (f : β → ℕ)
    (key : β → γ) (DC : Finset γ) (F : γ → β → ℕ) (G : β → ℕ)
    (hF1 : ∀ d b, K b → key b = d → F d b = f b) (hF0 : ∀ d b, ¬ (K b ∧ key b = d) → F d b = 0)
    (hG1 : ∀ b, K b → G b = f b) (hG0 : ∀ b, ¬ K b → G b = 0) :
    ∑ d ∈ DC, ∑ᶠ b, F d b ≤ ∑ᶠ b, G b := by
  classical
  have hFs : ∀ d, ∑ᶠ b, F d b = ∑ b ∈ hfin.toFinset, F d b := fun d => by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    rw [Function.mem_support] at hb
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hK
    exact hb (hF0 d b (fun h => hK h.1))
  have hGs : ∑ᶠ b, G b = ∑ b ∈ hfin.toFinset, G b := by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    rw [Function.mem_support] at hb
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hK
    exact hb (hG0 b hK)
  rw [hGs, Finset.sum_congr rfl (fun d _ => hFs d), Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  have hK : K b := (Set.Finite.mem_toFinset hfin).mp hb
  rw [hG1 b hK]

  have hcl : ∀ d ∈ DC, F d b = if d = key b then f b else 0 := fun d _ => by
    by_cases hd : d = key b
    · rw [if_pos hd, hF1 d b hK hd.symm]
    · rw [if_neg hd, hF0 d b (fun h => hd h.2.symm)]
  rw [Finset.sum_congr rfl hcl, Finset.sum_ite_eq']
  split_ifs <;> omega

def dset (m P g : ℕ) : Finset (Fin (m + 1) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (m + 1) => Finset.range P).filter fun ρ => ∑ c, ρ c ≤ g ∧ P ∣ g - ∑ c, ρ c

/- English proof (translation)
Establish `h` using `card_tuples (m + 1) n (Nat.succ_pos m)`. Establish `e : {P : Fin (m + 1) → ℕ // ∑ i, P i = n} ≃ (Finset.Nat.antidiagonalTuple (m + 1) n)` using `Equiv.subtypeEquivRight fun P => Finset.Nat.mem_antidiagonalTuple.symm`. Rewrite `h` using `[Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]`. Rewrite using `[h]`. Unfold `sdXi sd`.

Use `congr 1`.
-/
theorem card_tuple (m n : ℕ) : (Finset.Nat.antidiagonalTuple (m + 1) n).card = sd m n := by
  have h := card_tuples (m + 1) n (Nat.succ_pos m)
  have e : {P : Fin (m + 1) → ℕ // ∑ i, P i = n} ≃ (Finset.Nat.antidiagonalTuple (m + 1) n) :=
    Equiv.subtypeEquivRight fun P => Finset.Nat.mem_antidiagonalTuple.symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe] at h
  rw [h]
  unfold sdXi sd
  congr 1

/- English proof (translation)
Simplify using `only [← card_tuple]`. Establish `hdec : ∀ e : Fin (m + 1) → ℕ, ∑ c, e c = ∑ c, e c % P + P * ∑ c, e c / P` using `fun e => by`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl (fun c _ => (Nat.mod_add_div (e c) P).symm)`. Establish `hmap : ∀ e ∈ Finset.Nat.antidiagonalTuple (m + 1) g, (fun c => e c % P) ∈ dset m P g`.

Introduce `e he`. Rewrite `he` using `[Finset.Nat.mem_antidiagonalTuple]`. Establish `h` using `hdec e`. Rewrite `h` using `[he]`. Simplify using `only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]`.

Use `⟨fun c => Nat.mod_lt _ hP, le_of_le_of_eq (Nat.le_add_right _ _) h.symm, ?_⟩` and prove the remaining obligations. Conclude with `⟨∑ c, e c / P, by rw [h, Nat.add_sub_cancel_left]⟩`. Use `symm`. Rewrite using `[Finset.card_eq_sum_card_fiberwise (s := Finset.Nat.antidiagonalTuple (m + 1) g) hmap]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `ρ hρ`. Simplify using `only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hρ`. Take `⟨hρP, hρle, hρdvd⟩` from `hρ`. Apply `Finset.card_nbij' (fun e c => e c / P) (fun q c => ρ c + P * q c)` to reduce the goal to its premises. Introduce `e he`.

Rewrite `he` using `[Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]`. Take `⟨hsum, hmod⟩` from `he`. Rewrite using `[Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple]`. Establish `h` using `hdec e`. Rewrite `h` using `[hsum]`.

Establish `hr : ∑ c, e c % P = ∑ c, ρ c` using `by rw [← hmod]`. Use `show ∑ c, e c / P = (g - ∑ c, ρ c) / P`. Rewrite using `[h, hr, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hP]`. Introduce `q hq`. Rewrite `hq` using `[Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple]`.

Rewrite using `[Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Finset.sum_add_distrib, ← Finset.mul_sum, hq, Nat.mul_div_cancel' hρdvd]`. Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `c`.

Rewrite using `[Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hρP c)]`. Introduce `e he`. Rewrite `he` using `[Finset.mem_coe, Finset.mem_filter]`. Use function extensionality and compare the values at `c`. Establish `h : e c % P = ρ c` using `congrFun he.2 c`.

Use `show ρ c + P * (e c / P) = e c`. Rewrite using `[← h, Nat.mod_add_div]`. Introduce `q _`. Use function extensionality and compare the values at `c`. Use `show (ρ c + P * q c) / P = q c`.

Rewrite using `[Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt (hρP c), zero_add]`.
-/
theorem digit_sum (m P g : ℕ) (hP : 0 < P) : ∑ ρ ∈ dset m P g, sd m ((g - ∑ c, ρ c) / P) = sd m g := by
  classical
  simp only [← card_tuple]

  have hdec : ∀ e : Fin (m + 1) → ℕ, ∑ c, e c = ∑ c, e c % P + P * ∑ c, e c / P := fun e => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => (Nat.mod_add_div (e c) P).symm)
  have hmap : ∀ e ∈ Finset.Nat.antidiagonalTuple (m + 1) g, (fun c => e c % P) ∈ dset m P g := by
    intro e he
    rw [Finset.Nat.mem_antidiagonalTuple] at he
    have h := hdec e
    rw [he] at h
    simp only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun c => Nat.mod_lt _ hP, le_of_le_of_eq (Nat.le_add_right _ _) h.symm, ?_⟩
    exact ⟨∑ c, e c / P, by rw [h, Nat.add_sub_cancel_left]⟩
  symm
  rw [Finset.card_eq_sum_card_fiberwise (s := Finset.Nat.antidiagonalTuple (m + 1) g) hmap]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hρ
  obtain ⟨hρP, hρle, hρdvd⟩ := hρ
  apply Finset.card_nbij' (fun e c => e c / P) (fun q c => ρ c + P * q c)
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at he
    obtain ⟨hsum, hmod⟩ := he
    rw [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple]
    have h := hdec e
    rw [hsum] at h
    have hr : ∑ c, e c % P = ∑ c, ρ c := by rw [← hmod]
    show ∑ c, e c / P = (g - ∑ c, ρ c) / P
    rw [h, hr, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hP]
  · intro q hq
    rw [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    constructor
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq, Nat.mul_div_cancel' hρdvd]
      omega
    · funext c
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hρP c)]
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    funext c
    have h : e c % P = ρ c := congrFun he.2 c
    show ρ c + P * (e c / P) = e c
    rw [← h, Nat.mod_add_div]
  · intro q _
    funext c
    show (ρ c + P * q c) / P = q c
    rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt (hρP c), zero_add]

/- English proof (translation)
Unfold `symDim sd`. Establish `h1 : ¬ ((g : ℤ) < 0)` using `by omega`. Rewrite using `[if_neg h1]`. Use `first`. Consider the case `rw [Int.toNat_natCast]`.

Consider the case `rw [Int.toNat_coe_nat]`. Consider the case `simp only [Int.toNat_ofNat]`. Apply the tactic sequence `congr 1 <;> omega`.
-/
theorem symDim_nat (m g : ℕ) : symDim (m + 1) (g : ℤ) = sd m g := by
  unfold symDim sd
  have h1 : ¬ ((g : ℤ) < 0) := by omega
  rw [if_neg h1]
  first
    | rw [Int.toNat_natCast]
    | rw [Int.toNat_coe_nat]
    | simp only [Int.toNat_ofNat]
  congr 1 <;> omega

/- English proof (translation)
Rewrite using `[Finset.sum_product]`. Simplify using `only [Finset.prod_mul_distrib]`. Rewrite using `[← Finset.sum_mul_sum]`. Use `congr 1`. Conclude with `(Finset.prod_univ_sum (fun i => dset m (P i) (bTop i)) (fun i ρ => sd m ((bTop i - ∑ c, ρ c) / P i))).symm.trans (Finset.prod_congr rfl fun i _ => digit_sum m (P i) (bTop i) (hP i))`.

Conclude with `(Finset.prod_univ_sum (fun i => dset m (P i) (aTop i)) (fun i ρ => sd m ((aTop i - ∑ c, ρ c) / P i))).symm.trans (Finset.prod_congr rfl fun i _ => digit_sum m (P i) (aTop i) (hP i))`.
-/
private theorem sum_prod_sd_digits_eq_prod_sd (m s : ℕ) (P bTop aTop : Fin s → ℕ) (hP : ∀ i, 0 < P i) :
    ∑ d ∈ (Fintype.piFinset fun i => dset m (P i) (bTop i)) ×ˢ (Fintype.piFinset fun i => dset m (P i) (aTop i)),
      ∏ i, sd m ((bTop i - ∑ c, d.1 i c) / P i) * sd m ((aTop i - ∑ c, d.2 i c) / P i) =
    ∏ i, sd m (bTop i) * sd m (aTop i) := by
  rw [Finset.sum_product]
  simp only [Finset.prod_mul_distrib]
  rw [← Finset.sum_mul_sum]
  congr 1
  · exact (Finset.prod_univ_sum (fun i => dset m (P i) (bTop i))
      (fun i ρ => sd m ((bTop i - ∑ c, ρ c) / P i))).symm.trans
      (Finset.prod_congr rfl fun i _ => digit_sum m (P i) (bTop i) (hP i))
  · exact (Finset.prod_univ_sum (fun i => dset m (P i) (aTop i))
      (fun i ρ => sd m ((aTop i - ∑ c, ρ c) / P i))).symm.trans
      (Finset.prod_congr rfl fun i _ => digit_sum m (P i) (aTop i) (hP i))

/- English proof (translation)
Unfold `SegLowAt`. Introduce `X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC j m hm hmc`. Establish `hp : 0 < X.p`. Take `⟨⟨hY, hkY, -⟩, -⟩` from `hH`. Establish `hk : (1 : ℝ) ≤ X.k`.

Unfold `Loc.k`. Use `(Nat.cast_nonneg X.m : (0 : ℝ) ≤ X.m)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : 1 ≤ X.k ^ 2 * X.Y ^ 2` using `one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk) (one_le_pow₀ hY)`. Conclude with `Nat.cast_pos.mp (show (0 : ℝ) < X.p by linarith)`.

Establish `hP : ∀ i, 0 < (X.seg C0 CE1 CE2 j).P X.p i` using `fun i => by`. Unfold `SegData.P`. Conclude with `pow_pos hp _`. Establish `hdig : ∀ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock d …`. Introduce `d hd`.

Rewrite `hd` using `[Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]`. Take `⟨h1, h2⟩` from `hd`. Simplify using `only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at h1 h2`. Conclude with `⟨fun i c => ⟨(h1 i).1 c, (h2 i).1 c⟩, fun i => (h1 i).2, fun i => (h2 i).2⟩`. Establish `hmm : ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ, mmB C0 CE1 CE2 X j rz ry = symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) * (∏ i, sd X.m (((X.seg C0 CE1 CE2 j).bTop i - ∑ c, rz i c) / (X.seg C0 CE1 CE2 j).P X.p i) * sd X.m (((segATop X.TT X.aT j) i - ∑ c, ry i c) / (X.seg …`.

Introduce `rz ry`. Simplify using `only [mmB, dimMM, coarseA, coarseC, digitBlock, symDim_nat]`. Establish `hsum : ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), mmB C0 CE1 CE2 X j d.1 d.2 = symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A …`. Rewrite using `[Finset.sum_congr rfl (fun d _ => hmm d.1 d.2), ← Finset.sum_mul, ← Finset.mul_sum, sum_prod_sd_digits_eq_prod_sd X.m (segS X.TT j) (fun i => (X.seg C0 CE1 CE2 j).P X.p i) (X.seg C0 CE1 CE2 j).bTop (segATop X.TT X.aT j) hP]`. Both sides reduce to the same expression.

Establish `hcls : ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), rankOnDigits O C0 CE1 CE2 X j m d.1 d.2 ≤ segRank O X.p X.m (X.seg C0 …`. Establish `hfin` using `kf_kept_finite X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j)`. Conclude with `finsum_classes (fun b => Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) hfin (fun b => blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b) (fun b : SegBlock (segS X.TT j) X.m => (b.rz, b.ry)) ((Fintype.piFinset fun i => dset X.m …`. Rewrite using `[← hsum, Nat.cast_sum, Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem segLow_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (h : LowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    SegLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  unfold SegLowAt
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC j m hm hmc
  classical
  have hp : 0 < X.p := by
    obtain ⟨⟨hY, hkY, -⟩, -⟩ := hH
    have hk : (1 : ℝ) ≤ X.k := by
      unfold Loc.k
      have := (Nat.cast_nonneg X.m : (0 : ℝ) ≤ X.m)
      linarith
    have h3 : 1 ≤ X.k ^ 2 * X.Y ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk) (one_le_pow₀ hY)
    exact Nat.cast_pos.mp (show (0 : ℝ) < X.p by linarith)
  have hP : ∀ i, 0 < (X.seg C0 CE1 CE2 j).P X.p i := fun i => by
    unfold SegData.P
    exact pow_pos hp _
  have hdig : ∀ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock d.1 d.2) := by
    intro d hd
    rw [Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset] at hd
    obtain ⟨h1, h2⟩ := hd
    simp only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at h1 h2
    exact ⟨fun i c => ⟨(h1 i).1 c, (h2 i).1 c⟩, fun i => (h1 i).2, fun i => (h2 i).2⟩
  have hmm : ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ, mmB C0 CE1 CE2 X j rz ry =
      symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) *
        (∏ i, sd X.m (((X.seg C0 CE1 CE2 j).bTop i - ∑ c, rz i c) / (X.seg C0 CE1 CE2 j).P X.p i) *
          sd X.m (((segATop X.TT X.aT j) i - ∑ c, ry i c) / (X.seg C0 CE1 CE2 j).P X.p i)) * sd X.m (X.seg C0 CE1 CE2 j).bPlus := by
    intro rz ry
    simp only [mmB, dimMM, coarseA, coarseC, digitBlock, symDim_nat]
  have hsum : ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), mmB C0 CE1 CE2 X j d.1 d.2 =
      symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) *
        (∏ i, sd X.m (X.bT (segPos X.TT j i)) * sd X.m (X.aT (segPos X.TT j i))) *
          sd X.m (X.bT (segNext X.TT j)) := by
    rw [Finset.sum_congr rfl (fun d _ => hmm d.1 d.2), ← Finset.sum_mul, ← Finset.mul_sum,
      sum_prod_sd_digits_eq_prod_sd X.m (segS X.TT j) (fun i => (X.seg C0 CE1 CE2 j).P X.p i) (X.seg C0 CE1 CE2 j).bTop (segATop X.TT X.aT j) hP]
    rfl
  have hcls : ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), rankOnDigits O C0 CE1 CE2 X j m d.1 d.2 ≤
      segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m := by
    have hfin := kf_kept_finite X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j)
    exact finsum_classes (fun b => Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) hfin
      (fun b => blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b)
      (fun b : SegBlock (segS X.TT j) X.m => (b.rz, b.ry)) ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i)))
      (fun d b => if Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ∧ b.rz = d.1 ∧ b.ry = d.2 then
        blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b else 0)
      (fun b => if Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b then
        blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b else 0)
      (fun d b hK hk => by subst hk; exact if_pos ⟨hK, rfl, rfl⟩)
      (fun d b hn => if_neg fun ⟨hK, h1, h2⟩ => hn ⟨hK, Prod.ext h1 h2⟩)
      (fun b hK => if_pos hK) (fun b hK => if_neg hK)
  rw [← hsum, Nat.cast_sum, Finset.mul_sum]
  calc ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), lowFac C0 CE1 CE2 X j ⌈m⌉₊ * (mmB C0 CE1 CE2 X j d.1 d.2 : ℝ)
      ≤ ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), (rankOnDigits O C0 CE1 CE2 X j m d.1 d.2 : ℝ) :=
        Finset.sum_le_sum fun d hd => h X W Qq O Kf ι σ jO w hS hH hC j m hm hmc d.1 d.2 (hdig d hd)
    _ = ((∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), rankOnDigits O C0 CE1 CE2 X j m d.1 d.2 : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m : ℝ) := Nat.cast_le.mpr hcls

/- English proof (translation)
Unfold `RestSegLow`. Unfold `RestLow at h`. Conclude with `TransportedAlt.mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hh => segLow_of hh) h`.
-/
theorem restSegLow_of (h : RestLow) : RestSegLow := by
  unfold RestSegLow
  unfold RestLow at h
  exact TransportedAlt.mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hh => segLow_of hh) h

end Formalism.MainNotions.ColumnSystems.Pf

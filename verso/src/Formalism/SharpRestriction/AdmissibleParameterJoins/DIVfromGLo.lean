import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm
import Formalism.SharpRestriction.GlobalSchurBounds.AlcoveOf

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

/- English proof (translation)
Rewrite using `[(D.fm u).lam_eq i hi τ a]`. Unfold `flipTwoThree.lamLiftN flipTwoThree.lamCol flipTwoThree.wJ`. Distinguish the cases in `h : a.1 < D.R.k`. Simplify using `[h]`. Establish `hj : (a.1 - D.R.k) / (D.R.t + 1) < D.R.m` using `D.R.blk_lt hi a h`.

Simplify using `[h, hj]`.
-/
theorem lam_entry (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N i)) :
    ((((D.fm u).lam i τ).w a : ℤ) : ℚ) = flipTwoThree.lamLiftN D u τ a.1 := by
  rw [(D.fm u).lam_eq i hi τ a]
  unfold flipTwoThree.lamLiftN flipTwoThree.lamCol flipTwoThree.wJ
  by_cases h : a.1 < D.R.k
  · simp [h]
  · have hj : (a.1 - D.R.k) / (D.R.t + 1) < D.R.m := D.R.blk_lt hi a h
    simp [h, hj]

/- English proof (translation)
Apply the tactic sequence `rw [← lam_entry D u i hi τ a]`. Use `norm_cast`.
-/
theorem lam_entryR (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N i)) :
    ((((D.fm u).lam i τ).w a : ℤ) : ℝ) = ((flipTwoThree.lamLiftN D u τ a.1 : ℚ) : ℝ) := by
  rw [← lam_entry D u i hi τ a]
  norm_cast

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero => exact le_refl _`. Consider the case `succ n ih => exact le_trans (ih (by omega)) (h n hc)`.
-/
theorem wJ_mono {D : D7} {u : D.what₂.Word} {τ : D.what₂.Tau}
    (h : ∀ j, j + 1 < D.R.m → flipTwoThree.wJ D u τ j ≤ flipTwoThree.wJ D u τ (j + 1)) (c : ℕ) (hc : c < D.R.m) :
    flipTwoThree.wJ D u τ 0 ≤ flipTwoThree.wJ D u τ c := by
  induction c with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (ih (by omega)) (h n hc)

/- English proof (translation)
Unfold `flipTwoThree.IsTop at h`. Unfold `flipTwoThree.IsThick`. Unfold `Host.topPlaces at h`. Unfold `Host.thickPlaces`. Introduce `h2`.

Rewrite `h`, `h2` using `[Finset.mem_image]`. Take `⟨a, ha, hae⟩` from `h`. Take `⟨s, hs, hse⟩` from `h2`. Rewrite `hae` using `[← hse]`. Simplify using `only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, Prod.mk.injEq] at hae`.

Conclude with `absurd hae.1.1 (by decide)`.
-/
theorem top_not_thick (D : D7) (τ : D.what₂.Tau) (h : flipTwoThree.IsTop D τ) : ¬ flipTwoThree.IsThick D τ := by
  unfold flipTwoThree.IsTop at h
  unfold flipTwoThree.IsThick
  unfold Host.topPlaces at h
  unfold Host.thickPlaces
  intro h2
  rw [Finset.mem_image] at h h2
  obtain ⟨a, ha, hae⟩ := h
  obtain ⟨s, hs, hse⟩ := h2
  rw [← hse] at hae
  simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, Prod.mk.injEq] at hae
  exact absurd hae.1.1 (by decide)

/- English proof (translation)
Take `⟨n1, _, _, _, _, n6, n7, n8, n9, _, n11, _, _, n14, _, _⟩` from `hN u`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hL1 : 1 ≤ L.sc.L` using `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`. Establish `hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ)` using `Real.log_natCast_nonneg _`. Establish `hNn : (0 : ℝ) ≤ D.R.N D.R.m` using `Nat.cast_nonneg _`.

Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `ht : (11 : ℝ) ≤ D.R.t`. Establish `h1` using `D.R.rank_add_five_le`. Establish `h2` using `D.R.m_add_three_le_k`. Establish `h3` using `D.R.two_le_m`.

Establish `: 11 ≤ D.R.t` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hmt : (22 : ℝ) ≤ D.R.m * D.R.t` using `by nlinarith`. Establish `hq : 24 ≤ L.sc.b' / L.sc.x` using `by linarith`. Establish `hb24 : 24 * L.sc.x ≤ L.sc.b'` using `by rwa [le_div_iff₀ hx0] at hq`.

Establish `hb0 : 0 < L.sc.b'` using `by nlinarith`. Establish `hdiv : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb0.le (by linarith)`. Establish `hbb : L.sc.b' ≤ L.sc.b`. Rewrite `n6` using `[mul_div_assoc, mul_comm, div_mul_cancel₀ _ hx0.ne']`. Then use the resulting hypothesis. Use `⟨by nlinarith, ?_, hb0, hbb, hb24⟩` and prove the remaining obligations.

Establish `h1 : (D.R.N D.R.m : ℝ) * 1 ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L)` using `mul_le_mul_of_nonneg_left (by nlinarith) hNn`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nums_basic {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (u : D.what₂.Word) (hN : NumsL D L Cn cL) :
    L.Sc ≤ L.sc.b' ∧ (D.R.N D.R.m : ℝ) ≤ L.sc.b' ∧ 0 < L.sc.b' ∧ L.sc.b' ≤ L.sc.b ∧ 24 * L.sc.x ≤ L.sc.b' := by
  obtain ⟨n1, _, _, _, _, n6, n7, n8, n9, _, n11, _, _, n14, _, _⟩ := hN u
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hNn : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (11 : ℝ) ≤ D.R.t := by
    have h1 := D.R.rank_add_five_le
    have h2 := D.R.m_add_three_le_k
    have h3 := D.R.two_le_m
    have : 11 ≤ D.R.t := by omega
    exact_mod_cast this
  have hmt : (22 : ℝ) ≤ D.R.m * D.R.t := by nlinarith
  have hq : 24 ≤ L.sc.b' / L.sc.x := by linarith
  have hb24 : 24 * L.sc.x ≤ L.sc.b' := by rwa [le_div_iff₀ hx0] at hq
  have hb0 : 0 < L.sc.b' := by nlinarith
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb0.le (by linarith)
  have hbb : L.sc.b' ≤ L.sc.b := by
    rwa [mul_div_assoc, mul_comm, div_mul_cancel₀ _ hx0.ne'] at n6
  refine ⟨by nlinarith, ?_, hb0, hbb, hb24⟩
  have h1 : (D.R.N D.R.m : ℝ) * 1 ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hNn
  linarith

/- English proof (translation)
Establish `htop : flipTwoThree.IsTop D τ`. Unfold `topsOf at hτ`. Conclude with `(Finset.mem_filter.mp hτ).2`. Take `⟨hScb, -, hb'pos, -, -⟩` from `nums_basic hcL u hN`. Take `⟨-, hTop, -, hmono, hthin, -, hk1, -⟩` from `hW u τ`.

Take `⟨-, -, hb1, hb2, hmid⟩` from `hTop htop`. Establish `hthick : ¬ flipTwoThree.IsThick D τ` using `top_not_thick D τ htop`. Rewrite using `[lam_entryR D u i hi' τ a]`. Unfold `flipTwoThree.lamLiftN`. Use `split_ifs with hak`.

Distinguish the cases in `hlast : a.1 = D.R.k - 1`. Rewrite using `[hlast]`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `h0 : 0 < a.1` using `Nat.pos_of_ne_zero ha0`.

Establish `hlt : a.1 < D.R.k - 1` using `by omega`. Take `⟨hl, hu⟩` from `hmid a.1 h0 hlt`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Use `set j := (a.1 - D.R.k) / (D.R.t + 1) with hj`.

Establish `hjm : j < D.R.m` using `D.R.blk_lt hi' a hak`. Establish `hup : (flipTwoThree.wJ D u τ j : ℝ) ≤ 2 * L.sc.b'` using `hthin hthick j hjm`. Establish `hmon : flipTwoThree.wJ D u τ 0 ≤ flipTwoThree.wJ D u τ j` using `wJ_mono hmono j hjm`. Establish `hlowR : ((-(flipTwoThree.lamCol D u τ (D.R.k - 1)) : ℚ) : ℝ) ≤ (flipTwoThree.wJ D u τ j : ℝ)`. Conclude with `hk1.trans hmon` after adjusting the coercions.

Move the coercions through the operations in `at hlowR ⊢`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem entry_top_le {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : NumsL D L Cn cL) (hW : WtsL D L Cn)
    (u : D.what₂.Word) (τ : D.what₂.Tau) (hτ : τ ∈ topsOf D.host D.eTau) (i : ℕ) (hi' : i ≤ D.R.m) (a : Fin (D.R.N i))
    (ha0 : a.1 ≠ 0) : |((((D.fm u).lam i τ).w a : ℤ) : ℝ)| ≤ 2 * L.sc.b' := by
  have htop : flipTwoThree.IsTop D τ := by
    unfold topsOf at hτ
    exact (Finset.mem_filter.mp hτ).2
  obtain ⟨hScb, -, hb'pos, -, -⟩ := nums_basic hcL u hN
  obtain ⟨-, hTop, -, hmono, hthin, -, hk1, -⟩ := hW u τ
  obtain ⟨-, -, hb1, hb2, hmid⟩ := hTop htop
  have hthick : ¬ flipTwoThree.IsThick D τ := top_not_thick D τ htop
  rw [lam_entryR D u i hi' τ a]
  unfold flipTwoThree.lamLiftN
  split_ifs with hak
  · by_cases hlast : a.1 = D.R.k - 1
    · rw [hlast]
      rw [abs_le]
      constructor <;> linarith
    · have h0 : 0 < a.1 := Nat.pos_of_ne_zero ha0
      have hlt : a.1 < D.R.k - 1 := by omega
      obtain ⟨hl, hu⟩ := hmid a.1 h0 hlt
      rw [abs_le]
      constructor <;> linarith
  · set j := (a.1 - D.R.k) / (D.R.t + 1) with hj
    have hjm : j < D.R.m := D.R.blk_lt hi' a hak
    have hup : (flipTwoThree.wJ D u τ j : ℝ) ≤ 2 * L.sc.b' := hthin hthick j hjm
    have hmon : flipTwoThree.wJ D u τ 0 ≤ flipTwoThree.wJ D u τ j := wJ_mono hmono j hjm
    have hlowR : ((-(flipTwoThree.lamCol D u τ (D.R.k - 1)) : ℚ) : ℝ) ≤ (flipTwoThree.wJ D u τ j : ℝ) := by
      exact_mod_cast hk1.trans hmon
    push_cast at hlowR ⊢
    rw [abs_le]
    constructor <;> linarith

/- English proof (translation)
Establish `h1 : i * (D.R.t + 1) / 2 ≤ D.R.N D.R.m`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) ≤ (D.R.N D.R.m : ℝ)` using `by exact_mod_cast h1`. Conclude with `h2.trans (nums_basic hcL u hN).2.1`.
-/
theorem shift_le {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : NumsL D L Cn cL) (u : D.what₂.Word) (i : ℕ)
    (hi : i ≤ D.R.m) : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) ≤ L.sc.b' := by
  have h1 : i * (D.R.t + 1) / 2 ≤ D.R.N D.R.m :=
    calc i * (D.R.t + 1) / 2 ≤ i * (D.R.t + 1) := Nat.div_le_self _ _
      _ ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_right _ hi
      _ ≤ D.R.k + D.R.m * (D.R.t + 1) := Nat.le_add_left _ _
      _ = D.R.N D.R.m := rfl
  have h2 : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast h1
  exact h2.trans (nums_basic hcL u hN).2.1

/- English proof (translation)
Take `⟨-, -, hb'pos, -, -⟩` from `nums_basic hcL u hN`. Establish `habs : ∀ z : ℤ, ∀ n : ℕ, |(z : ℝ)| ≤ 2 * L.sc.b' → (n : ℝ) ≤ L.sc.b' → (((z - (n : ℤ)).natAbs : ℕ) : ℝ) ≤ 3 * L.sc.b'`. Introduce `z n hz hn`. Simplify using `only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast]`. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`.

Rewrite `hz`, the goal using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith [hz.1, hz.2]`. Establish `key : product_first_zeroth_parts.Wt D u τ ≤ ⌊3 * L.sc.b'⌋₊`. Unfold `product_first_zeroth_parts.Wt Wtau`. Apply `Finset.sup_le` to reduce the goal to its premises.

Introduce `i hi`. Apply `Finset.sup_le` to reduce the goal to its premises. Introduce `a _`. Establish `hi' : i ≤ D.R.m`. Use `Finset.mem_range.mp hi` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `split_ifs with h0`. Conclude with `Nat.zero_le _`. Establish `ha0 : a.1 ≠ 0` using `fun h => h0 ⟨h, hτ⟩`. Apply `Nat.le_floor` to reduce the goal to its premises.

Conclude with `habs _ _ (entry_top_le hcL hN hW u τ hτ i hi' a ha0) (shift_le hcL hN u i hi')`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Wt_top_le {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : NumsL D L Cn cL) (hW : WtsL D L Cn)
    (u : D.what₂.Word) (τ : D.what₂.Tau) (hτ : τ ∈ topsOf D.host D.eTau) : (product_first_zeroth_parts.Wt D u τ : ℝ) ≤ 3 * L.sc.b' := by
  obtain ⟨-, -, hb'pos, -, -⟩ := nums_basic hcL u hN
  have habs : ∀ z : ℤ, ∀ n : ℕ, |(z : ℝ)| ≤ 2 * L.sc.b' → (n : ℝ) ≤ L.sc.b' →
      (((z - (n : ℤ)).natAbs : ℕ) : ℝ) ≤ 3 * L.sc.b' := by
    intro z n hz hn
    simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [abs_le] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  have key : product_first_zeroth_parts.Wt D u τ ≤ ⌊3 * L.sc.b'⌋₊ := by
    unfold product_first_zeroth_parts.Wt Wtau
    apply Finset.sup_le
    intro i hi
    apply Finset.sup_le
    intro a _
    have hi' : i ≤ D.R.m := by
      have := Finset.mem_range.mp hi
      omega
    split_ifs with h0
    · exact Nat.zero_le _
    · have ha0 : a.1 ≠ 0 := fun h => h0 ⟨h, hτ⟩
      apply Nat.le_floor
      exact habs _ _ (entry_top_le hcL hN hW u τ hτ i hi' a ha0) (shift_le hcL hN u i hi')
  calc (product_first_zeroth_parts.Wt D u τ : ℝ) ≤ (⌊3 * L.sc.b'⌋₊ : ℝ) := by exact_mod_cast key
    _ ≤ 3 * L.sc.b' := Nat.floor_le (by linarith)

/- English proof (translation)
Simplify using `[Ranks.N]`.
-/
theorem N_zero (R : Ranks) : R.N 0 = R.k := by
  simp [Ranks.N]

/- English proof (translation)
Establish `hk : 0 < D.R.k`. Establish `h0` using `D.R.N_pos 0`. Rewrite `h0` using `[N_zero]`. Then use the resulting hypothesis. Establish `h` using `lam_entryR D u 0 (Nat.zero_le _) τ ⟨0, D.R.N_pos 0⟩`. Simplify using `only [flipTwoThree.lamLiftN, Fin.val_mk, hk, ↓reduceIte] at h`.

Unfold `MemberForms.aTop`. Conclude with `h`.
-/
theorem aTop_eq (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (((D.fm u).aTop τ : ℤ) : ℝ) = ((flipTwoThree.lamCol D u τ 0 : ℚ) : ℝ) := by
  have hk : 0 < D.R.k := by
    have h0 := D.R.N_pos 0
    rwa [N_zero] at h0
  have h := lam_entryR D u 0 (Nat.zero_le _) τ ⟨0, D.R.N_pos 0⟩
  simp only [flipTwoThree.lamLiftN, Fin.val_mk, hk, ↓reduceIte] at h
  unfold MemberForms.aTop
  exact h

/- English proof (translation)
Establish `hN : 0 < D.R.N 0` using `D.R.N_pos 0`. Establish `hk : D.R.N 0 - 1 < D.R.k`. Establish `h0` using `hN`. Rewrite `h0`, the goal using `[N_zero]`. Use linear arithmetic over natural numbers and integers.

Establish `h` using `lam_entryR D u 0 (Nat.zero_le _) τ ⟨D.R.N 0 - 1, by omega⟩`. Simplify using `only [flipTwoThree.lamLiftN, Fin.val_mk, hk, ↓reduceIte] at h`. Unfold `MemberForms.bTop DomWeight.detShift`. Rewrite using `[dif_pos hN]`. Use `push_cast`.

Rewrite using `[h, N_zero]`.
-/
theorem bTop_eq (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (((D.fm u).bTop τ : ℤ) : ℝ) = -((flipTwoThree.lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) := by
  have hN : 0 < D.R.N 0 := D.R.N_pos 0
  have hk : D.R.N 0 - 1 < D.R.k := by
    have h0 := hN
    rw [N_zero] at h0 ⊢
    omega
  have h := lam_entryR D u 0 (Nat.zero_le _) τ ⟨D.R.N 0 - 1, by omega⟩
  simp only [flipTwoThree.lamLiftN, Fin.val_mk, hk, ↓reduceIte] at h
  unfold MemberForms.bTop DomWeight.detShift
  rw [dif_pos hN]
  push_cast
  rw [h, N_zero]

/- English proof (translation)
Establish `key : product_first_zeroth_parts.amax D u ≤ ⌊2 * L.sc.a⌋`. Unfold `product_first_zeroth_parts.amax`. Rewrite using `[Finset.fold_max_le]`. Use `⟨?_, fun τ hτ => ?_⟩` and prove the remaining obligations. Rewrite using `[Int.le_floor]`.

Use `push_cast`. Unfold `Scale.a`. Conclude with `mul_nonneg (by norm_num) (mul_nonneg (by linarith [L.sc.one_lt_alt]) (Real.exp_pos _).le)`. Establish `htop : flipTwoThree.IsTop D τ`. Unfold `product_first_zeroth_parts.tops topsOf at hτ`.

Conclude with `(Finset.mem_filter.mp hτ).2`. Rewrite using `[Int.le_floor, aTop_eq]`. Establish `h` using `((hW u τ).2.1 htop).2.1`. Unfold `Scale.a`. Conclude with `h`.

Conclude with `Int.le_floor.mp key`.
-/
theorem amax_le {D : D7} {L : SizeData₂ D} {Cn : ℝ} (hW : WtsL D L Cn) (u : D.what₂.Word) :
    (product_first_zeroth_parts.amax D u : ℝ) ≤ 2 * L.sc.a := by
  have key : product_first_zeroth_parts.amax D u ≤ ⌊2 * L.sc.a⌋ := by
    unfold product_first_zeroth_parts.amax
    rw [Finset.fold_max_le]
    refine ⟨?_, fun τ hτ => ?_⟩
    · rw [Int.le_floor]
      push_cast
      unfold Scale.a
      exact mul_nonneg (by norm_num) (mul_nonneg (by linarith [L.sc.one_lt_alt]) (Real.exp_pos _).le)
    · have htop : flipTwoThree.IsTop D τ := by
        unfold product_first_zeroth_parts.tops topsOf at hτ
        exact (Finset.mem_filter.mp hτ).2
      rw [Int.le_floor, aTop_eq]
      have h := ((hW u τ).2.1 htop).2.1
      unfold Scale.a
      exact h
  exact Int.le_floor.mp key

/- English proof (translation)
Unfold `product_first_zeroth_parts.VV LT.VVT`. Use `split_ifs with hs`. Use `le_trans (Finset.card_le_card_of_injOn (t := topsOf D.host D.eTau) ((D.fm u).tauOf w) (fun v hv => ?_) (fun a _ b _ hab => ((D.fm u).tauOf w).injective hab)) ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_coe, Finset.mem_filter] at hv ⊢`. Conclude with `hv.2`.

Use `le_trans (Finset.card_le_card_of_injOn (t := D.host.topPlaces) (fun τ => ((D.eTau τ : D.R.Psi) : D.R.GG)) (fun τ hτ => ?_) (fun a _ b _ hab => D.eTau.injective (Subtype.ext hab))) ?_` and prove the remaining obligations. Unfold `topsOf at hτ`. Simplify using `only [Finset.mem_coe, Finset.mem_filter] at hτ ⊢`. Conclude with `hτ.2`. Unfold `Host.topPlaces`.

Conclude with `Finset.card_image_le`. Simplify using the standard rewrite rules.
-/
theorem card_VV_le (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : (product_first_zeroth_parts.VV D u w).card ≤ D.host.TT.card := by
  classical
  unfold product_first_zeroth_parts.VV LT.VVT
  split_ifs with hs
  · refine le_trans (Finset.card_le_card_of_injOn (t := topsOf D.host D.eTau) ((D.fm u).tauOf w)
      (fun v hv => ?_) (fun a _ b _ hab => ((D.fm u).tauOf w).injective hab)) ?_
    · simp only [Finset.mem_coe, Finset.mem_filter] at hv ⊢
      exact hv.2
    · refine le_trans (Finset.card_le_card_of_injOn (t := D.host.topPlaces)
        (fun τ => ((D.eTau τ : D.R.Psi) : D.R.GG)) (fun τ hτ => ?_)
        (fun a _ b _ hab => D.eTau.injective (Subtype.ext hab))) ?_
      · unfold topsOf at hτ
        simp only [Finset.mem_coe, Finset.mem_filter] at hτ ⊢
        exact hτ.2
      · unfold Host.topPlaces
        exact Finset.card_image_le
  · simp

/- English proof (translation)
Unfold `product_first_zeroth_parts.VV LT.VVT at hv`. Use `split_ifs at hv with hs`. Conclude with `(Finset.mem_filter.mp hv).2`. Simplify using `at hv`.
-/
theorem mem_VV_top (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) (hv : v ∈ product_first_zeroth_parts.VV D u w) :
    (D.fm u).tauOf w v ∈ topsOf D.host D.eTau := by
  classical
  unfold product_first_zeroth_parts.VV LT.VVT at hv
  split_ifs at hv with hs
  · exact (Finset.mem_filter.mp hv).2
  · simp at hv

/- English proof (translation)
Unfold `LevelPrimeSizeBounds`. Introduce `u w _`. Take `⟨-, hNb, hb'pos, -, -⟩` from `nums_basic hcL u hN`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `ha0 : 0 ≤ L.sc.a`.

Unfold `Scale.a`. Conclude with `mul_nonneg (by linarith) (Real.exp_pos _).le`. Establish `hk0 : (0 : ℝ) ≤ (D.R.k : ℝ)⁻¹` using `inv_nonneg.mpr (Nat.cast_nonneg _)`. Establish `hak : 0 ≤ L.sc.a / D.R.k` using `div_nonneg ha0 (Nat.cast_nonneg _)`. Establish `hkN : (D.R.k : ℝ) ≤ L.sc.b'`.

Establish `h1 : D.R.k ≤ D.R.N D.R.m` using `Nat.le_add_right _ _`. Establish `h2 : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ)` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hamax : (product_first_zeroth_parts.amax D u : ℝ) / D.R.k ≤ 2 * (L.sc.a / D.R.k)`. Rewrite using `[div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_right (amax_le hW u) hk0`. Establish `hterm : ∀ v ∈ product_first_zeroth_parts.VV D u w, ((product_first_zeroth_parts.amax D u : ℝ) / D.R.k + 2 * product_first_zeroth_parts.Wt D u ((D.fm u).tauOf w v) + D.R.k + (D.fm u).bTop ((D.fm u).tauOf w v)) ≤ 9 * (L.sc.a / D.R.k + L.sc.b')`. Introduce `v hv`. Establish `htops` using `mem_VV_top D u w v hv`. Establish `hWt` using `Wt_top_le hcL hN hW u _ htops`.

Establish `htop : flipTwoThree.IsTop D ((D.fm u).tauOf w v)`. Unfold `topsOf at htops`. Conclude with `(Finset.mem_filter.mp htops).2`. Establish `hb2` using `((hW u ((D.fm u).tauOf w v)).2.1 htop).2.2.2.1`. Establish `hbt` using `bTop_eq D u ((D.fm u).tauOf w v)`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_right ?_ (by linarith)` and prove the remaining obligations. Conclude with `card_VV_le D u w` after adjusting the coercions. Use `_ = 9 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b') := by`.

Unfold `LocalQuadraticParts.nTT`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fifthLevelSizes_of_weights {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : NumsL D L Cn cL) (hW : WtsL D L Cn) :
    LevelPrimeSizeBounds D L 9 := by
  unfold LevelPrimeSizeBounds
  intro u w _
  obtain ⟨-, hNb, hb'pos, -, -⟩ := nums_basic hcL u hN
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have ha0 : 0 ≤ L.sc.a := by
    unfold Scale.a
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hak : 0 ≤ L.sc.a / D.R.k := div_nonneg ha0 (Nat.cast_nonneg _)
  have hkN : (D.R.k : ℝ) ≤ L.sc.b' := by
    have h1 : D.R.k ≤ D.R.N D.R.m := Nat.le_add_right _ _
    have h2 : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast h1
    linarith
  have hamax : (product_first_zeroth_parts.amax D u : ℝ) / D.R.k ≤ 2 * (L.sc.a / D.R.k) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (amax_le hW u) hk0
  have hterm : ∀ v ∈ product_first_zeroth_parts.VV D u w, ((product_first_zeroth_parts.amax D u : ℝ) / D.R.k + 2 * product_first_zeroth_parts.Wt D u ((D.fm u).tauOf w v) + D.R.k +
        (D.fm u).bTop ((D.fm u).tauOf w v)) ≤ 9 * (L.sc.a / D.R.k + L.sc.b') := by
    intro v hv
    have htops := mem_VV_top D u w v hv
    have hWt := Wt_top_le hcL hN hW u _ htops
    have htop : flipTwoThree.IsTop D ((D.fm u).tauOf w v) := by
      unfold topsOf at htops
      exact (Finset.mem_filter.mp htops).2
    have hb2 := ((hW u ((D.fm u).tauOf w v)).2.1 htop).2.2.2.1
    have hbt := bTop_eq D u ((D.fm u).tauOf w v)
    linarith
  calc _ ≤ (product_first_zeroth_parts.VV D u w).card • (9 * (L.sc.a / D.R.k + L.sc.b')) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((product_first_zeroth_parts.VV D u w).card : ℝ) * (9 * (L.sc.a / D.R.k + L.sc.b')) := nsmul_eq_mul _ _
    _ ≤ (D.host.TT.card : ℝ) * (9 * (L.sc.a / D.R.k + L.sc.b')) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        exact_mod_cast card_VV_le D u w
    _ = 9 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b') := by
        unfold LocalQuadraticParts.nTT
        ring

/- English proof (translation)
Take `⟨_, s2, s3, s4, s5⟩` from `nums_basic (by linarith) u hN`. Establish `hx1` using `L.sc.one_lt_alt`. Establish `hb24 : 24 ≤ L.sc.b` using `by linarith`. Establish `hb1 : 1 ≤ L.sc.b` using `by linarith`. Establish `hbb : L.sc.b ^ 2 = L.sc.b * L.sc.b` using `sq _`.

Establish `h24 : 24 * L.sc.b ≤ L.sc.b * L.sc.b` using `mul_le_mul_of_nonneg_right hb24 (by linarith)`. Establish `hb2 : L.sc.b ^ 2 ≤ ((D.mem u).A.T : ℝ)`. Use `le_trans ?_ (hT u)` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast]`. Use `Real.rpow_le_rpow_of_exponent_le hb1 ?_` and prove the remaining obligations.

Establish `: (4 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨?_, ⟨?_, GlobalTheoryTheory.Alc.alcove_of (by linarith) hN hW hT hm u⟩, fun τ hτ => ?_⟩` and prove the remaining obligations. Establish `hf : (D.R.f : ℝ) ≤ D.R.N D.R.m`.

Establish `h1` using `D.R.f_le_k`. Establish `: D.R.f ≤ D.R.N D.R.m` using `by unfold Ranks.f Ranks.n Ranks.N; omega`. Conclude with `this` after adjusting the coercions. Establish `hf0 : (0 : ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`. Establish `hN0 : (0 : ℝ) ≤ D.R.N D.R.m` using `Nat.cast_nonneg _`.

Establish `h3 : 3 * (D.R.N D.R.m : ℝ) ≤ L.sc.b`. Take `⟨_, _, _, _, _, _, _, _, _, _, n11, _⟩` from `hN u`. Establish `hL1 : 1 ≤ L.sc.L` using `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`. Establish `hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ)` using `Real.log_natCast_nonneg _`. Establish `h1 : (D.R.N D.R.m : ℝ) * 3 ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L)` using `mul_le_mul_of_nonneg_left (by nlinarith) hN0`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfN : (D.R.f : ℝ) * D.R.N D.R.m ≤ (D.R.N D.R.m : ℝ) * D.R.N D.R.m` using `mul_le_mul_of_nonneg_right hf hN0`. Establish `h9 : (3 * (D.R.N D.R.m : ℝ)) * (3 * (D.R.N D.R.m : ℝ)) ≤ L.sc.b * L.sc.b` using `mul_le_mul h3 h3 (by linarith) (by linarith)`. Establish `: (2 * D.R.f * D.R.N D.R.m + 1 : ℝ) < ((D.mem u).A.T : ℝ)` using `by nlinarith`. Conclude with `this` after adjusting the coercions.

Establish `h1` using `amax_le hW u`. Establish `ha : L.sc.a = L.sc.x * L.sc.b` using `rfl`. Establish `h8 : 24 * L.sc.x * L.sc.b ≤ L.sc.b * L.sc.b` using `mul_le_mul_of_nonneg_right (s5.trans s4) (by linarith)`. Establish `: (4 * (product_first_zeroth_parts.amax D u : ℝ)) < ((D.mem u).A.T : ℝ)` using `by nlinarith`. Conclude with `this` after adjusting the coercions.

Establish `hTp : flipTwoThree.IsTop D τ` using `(Finset.mem_filter.1 hτ).2`. Take `⟨_, w2, _⟩` from `hW u τ`. Establish `e3` using `(w2 hTp).2.2.1`. Establish `: (0 : ℝ) ≤ ((D.fm u).bTop τ : ℤ)` using `by rw [bTop_eq]; linarith`. Conclude with `this` after adjusting the coercions.
-/
theorem levelPrime_setting_of_sizes {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 3 ≤ cL) (hN : NumsL D L Cn cL) (hW : WtsL D L Cn)
    (hT : L.TuGe) (hm : 4 ≤ D.R.m) (u : D.what₂.Word) : product_first_zeroth_parts.HidaSetting D u := by
  obtain ⟨_, s2, s3, s4, s5⟩ := nums_basic (by linarith) u hN
  have hx1 := L.sc.one_lt_alt
  have hb24 : 24 ≤ L.sc.b := by linarith
  have hb1 : 1 ≤ L.sc.b := by linarith
  have hbb : L.sc.b ^ 2 = L.sc.b * L.sc.b := sq _
  have h24 : 24 * L.sc.b ≤ L.sc.b * L.sc.b := mul_le_mul_of_nonneg_right hb24 (by linarith)
  have hb2 : L.sc.b ^ 2 ≤ ((D.mem u).A.T : ℝ) := by
    refine le_trans ?_ (hT u)
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have : (4 : ℝ) ≤ D.R.m := by exact_mod_cast hm
    push_cast
    linarith
  refine ⟨?_, ⟨?_, GlobalTheoryTheory.Alc.alcove_of (by linarith) hN hW hT hm u⟩, fun τ hτ => ?_⟩
  · have hf : (D.R.f : ℝ) ≤ D.R.N D.R.m := by
      have h1 := D.R.f_le_k
      have : D.R.f ≤ D.R.N D.R.m := by unfold Ranks.f Ranks.n Ranks.N; omega
      exact_mod_cast this
    have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
    have h3 : 3 * (D.R.N D.R.m : ℝ) ≤ L.sc.b := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, n11, _⟩ := hN u
      have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
      have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
      have h1 : (D.R.N D.R.m : ℝ) * 3 ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hN0
      linarith
    have hfN : (D.R.f : ℝ) * D.R.N D.R.m ≤ (D.R.N D.R.m : ℝ) * D.R.N D.R.m := mul_le_mul_of_nonneg_right hf hN0
    have h9 : (3 * (D.R.N D.R.m : ℝ)) * (3 * (D.R.N D.R.m : ℝ)) ≤ L.sc.b * L.sc.b :=
      mul_le_mul h3 h3 (by linarith) (by linarith)
    have : (2 * D.R.f * D.R.N D.R.m + 1 : ℝ) < ((D.mem u).A.T : ℝ) := by nlinarith
    exact_mod_cast this
  · have h1 := amax_le hW u
    have ha : L.sc.a = L.sc.x * L.sc.b := rfl
    have h8 : 24 * L.sc.x * L.sc.b ≤ L.sc.b * L.sc.b := mul_le_mul_of_nonneg_right (s5.trans s4) (by linarith)
    have : (4 * (product_first_zeroth_parts.amax D u : ℝ)) < ((D.mem u).A.T : ℝ) := by nlinarith
    exact_mod_cast this
  · have hTp : flipTwoThree.IsTop D τ := (Finset.mem_filter.1 hτ).2
    obtain ⟨_, w2, _⟩ := hW u τ
    have e3 := (w2 hTp).2.2.1
    have : (0 : ℝ) ≤ ((D.fm u).bTop τ : ℤ) := by rw [bTop_eq]; linarith
    exact_mod_cast this

/- English proof (translation)
Take `⟨Cn, hN⟩` from `numsL_wtsL_fam Fm hT hDl`. Take `⟨x0, hN⟩` from `hN Cn le_rfl 3 le_rfl`. Take `⟨x1, hT⟩` from `hT`. Take `⟨x2, hE⟩` from `hE`. Take `⟨x3, h3⟩` from `flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4`.

Use `family_levelPrime_summary_simple Fm C 9 (by norm_num) ⟨max (max x0 x1) (max (max x2 x3) (max 4 (Fm.x1 + 1))), fun x hx i => ?_⟩` and prove the remaining obligations. Establish `e0 : x ≥ x0` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `e1 : x ≥ x1` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `e2 : x ≥ x2` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx`. Establish `e3 : x3 ≤ x` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx`.

Establish `e4 : 4 ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx`. Establish `e5 : Fm.x1 < x`. Use `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsx : (Fm.L x i).sc.x = x` using `Fm.L_x x i e5`.

Establish `hm : 4 ≤ (Fm.D x i).R.m`. Establish `z1` using `(flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x e5 i) (by rw [hsx]; exact e4)).1`. Rewrite `z1` using `[hsx]`. Establish `: (4 : ℝ) ≤ (Fm.D x i).R.m` using `le_trans (h3 x e3) z1`. Conclude with `this` after adjusting the coercions.

Conclude with `⟨(hE x e2 i).1, (hE x e2 i).2, fifthLevelSizes_of_weights (by norm_num) (hN x e0 i).1 (hN x e0 i).2, levelPrime_setting_of_sizes le_rfl (hN x e0 i).1 (hN x e0 i).2 (hT x e1 i).1 hm⟩`.
-/
theorem family_levelPrime_summary_closed {eps : ℝ} (Fm : FamP eps) (C : ℝ) (hT : TuSize Fm) (hDl : DlSize Fm)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∀ u, product_first_zeroth_parts.Conclusion2 (Fm.D x i) u) ∧ (∀ u, product_first_zeroth_parts.Conclusion5 (Fm.D x i) u C)) :
    LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨Cn, hN⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨x1, hT⟩ := hT
  obtain ⟨x2, hE⟩ := hE
  obtain ⟨x3, h3⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4
  refine family_levelPrime_summary_simple Fm C 9 (by norm_num)
    ⟨max (max x0 x1) (max (max x2 x3) (max 4 (Fm.x1 + 1))), fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have e1 : x ≥ x1 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e2 : x ≥ x2 := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have e3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have e4 : 4 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have e5 : Fm.x1 < x := by
    have := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
    linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i e5
  have hm : 4 ≤ (Fm.D x i).R.m := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x e5 i) (by rw [hsx]; exact e4)).1
    rw [hsx] at z1
    have : (4 : ℝ) ≤ (Fm.D x i).R.m := le_trans (h3 x e3) z1
    exact_mod_cast this
  exact ⟨(hE x e2 i).1, (hE x e2 i).2, fifthLevelSizes_of_weights (by norm_num) (hN x e0 i).1 (hN x e0 i).2,
    levelPrime_setting_of_sizes le_rfl (hN x e0 i).1 (hN x e0 i).2 (hT x e1 i).1 hm⟩

end Formalism.MainNotions.J

end

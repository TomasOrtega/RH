import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `D u w hg hT Y hF ht v s i hi r`. Establish `hk : (D.gat u w hg).P.m + 1 = D.R.k` using `hT.gat_k u w hg`. Establish `hw : ∀ b (hb : b < D.R.m), (((Y.Fl u w hg).w v (b + 1) s : ℤ) : ℝ) = ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩ : ℝ) - kaJ D (b + 1)`. Introduce `b hb`. Rewrite using `[hF u w hg v s (b + 1) (by simp [SizeData₂.lifts]; omega)]`.

Simplify using `[wj, hb, D.hcW_e]`. Establish `hwS : DV.wSz D (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) = ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨i, hi⟩ : ℝ)`. Simplify using `[DV.wSz, show 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m by omega, D.hcW_e]`. Unfold `FormalGroupSystem.nu FormalGroupSystem.NN`. Rewrite using `[ht]`.

Distinguish the cases in `h1 : r < D.R.k`. Rewrite using `[if_pos (by omega), if_pos (show r < D.R.N i by simp [Ranks.N]; omega)]`. Unfold `FormalGroupSystem.lamI`. Rewrite using `[dif_pos (by omega)]`. Unfold `DV.nuRow DV.srcPar`.

Rewrite using `[dif_pos h1, hwS]`. Establish `hl : (((D.gat u w hg).P.lam0 v s ⟨r + 1 - 1, by omega⟩ : ℤ) : ℚ) = (D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).u ⟨r, h1⟩ - ((D.R.k : ℚ) - 1) / 2 + r`. Rewrite using `[hT.gat_lam, (D.fm u).lam_eq 0 (Nat.zero_le _)]`. Simplify using `[hcToWeightQ, rhoVec, Ranks.N, h1]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hlR` using `congrArg (Rat.cast : ℚ → ℝ) hl`. Move the coercions through the operations in `at hlR ⊢`. Rewrite using `[hlR, hw i hi]`. Simplify using `only [kaJ, Ranks.N, Nat.add_sub_cancel]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (by omega)]`. Take `⟨q, rfl⟩ : ∃ q, r = D.R.k + q` from `⟨r - D.R.k, by omega⟩`. Establish `hrk : D.R.k + q + 1 - ((D.gat u w hg).P.m + 2) = q` using `by omega`. Rewrite using `[hrk]`.

Establish `ht1 : 0 < D.R.t + 1` using `Nat.succ_pos _`. Establish `hM : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + (D.R.t + 1)` using `by ring`. Establish `hNi : D.R.N i = D.R.k + i * (D.R.t + 1)` using `rfl`. Distinguish the cases in `h2 : q < i * (D.R.t + 1)`. Establish `hb : q / (D.R.t + 1) < i`.

Rewrite using `[Nat.div_lt_iff_lt_mul ht1]`. Conclude with `h2`. Rewrite using `[if_pos (by omega), if_pos (by omega)]`. Unfold `DV.nuRow DV.srcPar`. Rewrite using `[dif_neg h1]`.

Simplify using `only [Nat.add_sub_cancel_left]`. Rewrite using `[dif_pos (by omega), hwS]`. Establish `hr : q = q / (D.R.t + 1) * (D.R.t + 1) + q % (D.R.t + 1)`. Use `Nat.div_add_mod q (D.R.t + 1)` as an intermediate fact. Rewrite `this` using `[mul_comm]`.

Use linear arithmetic over natural numbers and integers. Establish `hrR : (q : ℝ) = ((q / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1) + ((q % (D.R.t + 1) : ℕ) : ℝ)`. Conclude with `hr` after adjusting the coercions. Use `push_cast`. Rewrite using `[hw _ (by omega), hw i hi]`.

Simplify using `only [kaJ, Ranks.N]`. Use `push_cast`. Rewrite using `[hrR]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (show ¬ D.R.k + q < D.R.N i by omega)]`.

Distinguish the cases in `h3 : q < i * (D.R.t + 1) + (D.R.t + 1)`. Establish `hb : q / (D.R.t + 1) = i`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul ht1, Nat.succ_mul]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Nat.le_div_iff_mul_le ht1]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos (by omega), hb]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg (by omega)]`.

Simplify using the standard rewrite rules.
-/
theorem fock_rows_of_fills : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (Y : LatInst D), FillsAll hT Y → (Y.Fl u w hg).t = D.R.t → ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (i : ℕ), i < D.R.m → ∀ r : ℕ, ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) s (r + 1) : ℤ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) r else 0 := by
  intro D u w hg hT Y hF ht v s i hi r
  have hk : (D.gat u w hg).P.m + 1 = D.R.k := hT.gat_k u w hg
  have hw : ∀ b (hb : b < D.R.m), (((Y.Fl u w hg).w v (b + 1) s : ℤ) : ℝ) =
      ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩ : ℝ) - kaJ D (b + 1) := by
    intro b hb
    rw [hF u w hg v s (b + 1) (by simp [SizeData₂.lifts]; omega)]
    simp [wj, hb, D.hcW_e]
  have hwS : DV.wSz D (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) = ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨i, hi⟩ : ℝ) := by
    simp [DV.wSz, show 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m by omega, D.hcW_e]
  unfold FormalGroupSystem.nu FormalGroupSystem.NN
  rw [ht]
  by_cases h1 : r < D.R.k
  · rw [if_pos (by omega), if_pos (show r < D.R.N i by simp [Ranks.N]; omega)]
    unfold FormalGroupSystem.lamI
    rw [dif_pos (by omega)]
    unfold DV.nuRow DV.srcPar
    rw [dif_pos h1, hwS]
    have hl : (((D.gat u w hg).P.lam0 v s ⟨r + 1 - 1, by omega⟩ : ℤ) : ℚ) =
        (D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).u ⟨r, h1⟩ - ((D.R.k : ℚ) - 1) / 2 + r := by
      rw [hT.gat_lam, (D.fm u).lam_eq 0 (Nat.zero_le _)]
      simp [hcToWeightQ, rhoVec, Ranks.N, h1]
      ring
    have hlR := congrArg (Rat.cast : ℚ → ℝ) hl
    push_cast at hlR ⊢
    rw [hlR, hw i hi]
    simp only [kaJ, Ranks.N, Nat.add_sub_cancel]
    push_cast
    ring
  · rw [if_neg (by omega)]
    obtain ⟨q, rfl⟩ : ∃ q, r = D.R.k + q := ⟨r - D.R.k, by omega⟩
    have hrk : D.R.k + q + 1 - ((D.gat u w hg).P.m + 2) = q := by omega
    rw [hrk]
    have ht1 : 0 < D.R.t + 1 := Nat.succ_pos _
    have hM : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + (D.R.t + 1) := by ring
    have hNi : D.R.N i = D.R.k + i * (D.R.t + 1) := rfl
    by_cases h2 : q < i * (D.R.t + 1)
    · have hb : q / (D.R.t + 1) < i := by
        rw [Nat.div_lt_iff_lt_mul ht1]; exact h2
      rw [if_pos (by omega), if_pos (by omega)]
      unfold DV.nuRow DV.srcPar
      rw [dif_neg h1]
      simp only [Nat.add_sub_cancel_left]
      rw [dif_pos (by omega), hwS]
      have hr : q = q / (D.R.t + 1) * (D.R.t + 1) + q % (D.R.t + 1) := by
        have := Nat.div_add_mod q (D.R.t + 1); rw [mul_comm] at this; omega
      have hrR : (q : ℝ) = ((q / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1) + ((q % (D.R.t + 1) : ℕ) : ℝ) := by
        exact_mod_cast hr
      push_cast
      rw [hw _ (by omega), hw i hi]
      simp only [kaJ, Ranks.N]
      push_cast
      rw [hrR]
      ring
    · rw [if_neg (show ¬ D.R.k + q < D.R.N i by omega)]
      by_cases h3 : q < i * (D.R.t + 1) + (D.R.t + 1)
      · have hb : q / (D.R.t + 1) = i := by
          apply le_antisymm
          · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul ht1, Nat.succ_mul]; omega
          · rw [Nat.le_div_iff_mul_le ht1]; omega
        rw [if_pos (by omega), hb]
        simp
      · rw [if_neg (by omega)]
        simp

end GlobalTheory

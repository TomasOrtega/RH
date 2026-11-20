import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
open GlobalTheory.SignedHC

namespace GlobalTheory.KerConjMean.TopSizes

/- English proof (translation)
Establish `hn : 0 < n` using `a.pos`. Establish `key : (wtOf n E).natW a = ((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩).toNat`. Simplify using `only [DomWeight.natW, DomWeight.detShift, dif_pos hn]`. Establish `hd : (((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩ : ℤ) : ℝ) ≤ hi - lo + 1`. Unfold `wtOf`.

Use `split_ifs with h`. Establish `e0` using `hE _ (descEnum_mem E h.1 a)`. Establish `e1` using `hE _ (descEnum_mem E h.1 ⟨n - 1, by omega⟩)`. Establish `f0 : ((⌊highestWeight E h.1 a⌋ : ℤ) : ℝ) ≤ ((highestWeight E h.1 a : ℚ) : ℝ)`. Conclude with `Int.floor_le _` after adjusting the coercions.

Establish `f1 : ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) - 1 < ((⌊highestWeight E h.1 ⟨n - 1, by omega⟩⌋ : ℤ) : ℝ)`. Conclude with `Int.sub_one_lt_floor _` after adjusting the coercions. Establish `hr : ((a : ℕ) : ℝ) + 1 ≤ (n : ℝ)` using `by exact_mod_cast a.2`. Establish `hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1` using `by rw [Nat.cast_sub hn]; simp`. Establish `g0 : ((highestWeight E h.1 a : ℚ) : ℝ) ≤ hi + ((n : ℝ) - 1) / 2`.

Simplify using `only [highestWeight]`. Use `push_cast`. Combine the linear relations using `[e0.2]`. Establish `g1 : lo + ((n : ℝ) - 1) / 2 ≤ ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ)`. Simplify using `only [highestWeight, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, hc]`.

Combine the linear relations using `[e1.1]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[key]`. Establish `c : ∀ z : ℤ, (z.toNat : ℝ) = (((z.toNat : ℕ) : ℤ) : ℝ)` using `fun z => (Int.cast_natCast _).symm`. Rewrite using `[c, Int.toNat_eq_max]`. Use `push_cast`. Conclude with `max_le (by push_cast at hd; exact hd) (by linarith)`.
-/
theorem natW_wtOf_le (n : ℕ) (E : Finset ℚ) (lo hi : ℝ) (hM : lo ≤ hi) (hE : ∀ x ∈ E, lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi) (a : Fin n) :
    (((wtOf n E).natW a : ℕ) : ℝ) ≤ hi - lo + 1 := by
  have hn : 0 < n := a.pos
  have key : (wtOf n E).natW a = ((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩).toNat := by
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn]
  have hd : (((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩ : ℤ) : ℝ) ≤ hi - lo + 1 := by
    unfold wtOf
    split_ifs with h
    · have e0 := hE _ (descEnum_mem E h.1 a)
      have e1 := hE _ (descEnum_mem E h.1 ⟨n - 1, by omega⟩)
      have f0 : ((⌊highestWeight E h.1 a⌋ : ℤ) : ℝ) ≤ ((highestWeight E h.1 a : ℚ) : ℝ) := by
        exact_mod_cast Int.floor_le _
      have f1 : ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) - 1 <
          ((⌊highestWeight E h.1 ⟨n - 1, by omega⟩⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.sub_one_lt_floor _
      have hr : ((a : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast a.2
      have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
      have g0 : ((highestWeight E h.1 a : ℚ) : ℝ) ≤ hi + ((n : ℝ) - 1) / 2 := by
        simp only [highestWeight]; push_cast; linarith [e0.2]
      have g1 : lo + ((n : ℝ) - 1) / 2 ≤ ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) := by
        simp only [highestWeight, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, hc]
        linarith [e1.1]
      push_cast
      linarith
    · simp; linarith
  rw [key]
  have c : ∀ z : ℤ, (z.toNat : ℝ) = (((z.toNat : ℕ) : ℤ) : ℝ) := fun z => (Int.cast_natCast _).symm
  rw [c, Int.toNat_eq_max]
  push_cast
  exact max_le (by push_cast at hd; exact hd) (by linarith)

/- English proof (translation)
Unfold `GridData.extend`. Use `split_ifs with hj`. Take `⟨h1, h2⟩` from `hf ⟨j - d, hj⟩`. Establish `a1 : (0 : ℚ) ≤ f ⟨j - d, hj⟩` using `by exact_mod_cast h1`. Use `⟨by exact_mod_cast Int.floor_nonneg.2 a1, le_trans ?_ h2⟩` and prove the remaining obligations.

Conclude with `Int.floor_le _` after adjusting the coercions. Simplify using `[hh]`.
-/
theorem extend_bounds {n : ℕ} (d : ℕ) (f : Fin n → ℚ) (h : ℝ) (hh : 0 ≤ h)
    (hf : ∀ i, 0 ≤ ((f i : ℚ) : ℝ) ∧ ((f i : ℚ) : ℝ) ≤ h) (j : ℕ) :
    0 ≤ ((GridData.extend d f j : ℤ) : ℝ) ∧ ((GridData.extend d f j : ℤ) : ℝ) ≤ h := by
  unfold GridData.extend
  split_ifs with hj
  · obtain ⟨h1, h2⟩ := hf ⟨j - d, hj⟩
    have a1 : (0 : ℚ) ≤ f ⟨j - d, hj⟩ := by exact_mod_cast h1
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 a1, le_trans ?_ h2⟩
    exact_mod_cast Int.floor_le _
  · simp [hh]

/- English proof (translation)
Take `⟨hN, -, -, -, hm2, -, -, hb12⟩` from `GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, hgap, hbe, -⟩` from `hs`. Establish `hSc` using `large₂.Sc_pos`. Establish `hg0 : (0 : ℝ) ≤ (gap D 1 : ℝ)` using `Nat.cast_nonneg _`. Establish `hm0 : (0 : ℝ) ≤ (D.R.m : ℝ)` using `Nat.cast_nonneg _`.

Establish `hScb : large₂.Sc ≤ large₂.sc.b` using `by nlinarith`. Establish `hts : D.R.t + sLen D + 1 ≤ bigN D`. Establish `: D.R.t + sLen D + 1 ≤ D.R.m * (D.R.t + sLen D + 1)` using `Nat.le_mul_of_pos_left _ (by omega)`. Unfold `bigN`. Use linear arithmetic over natural numbers and integers.

Establish `hts' : (D.R.t : ℝ) + (sLen D : ℝ) + 1 ≤ large₂.sc.b` using `le_trans (by exact_mod_cast hts) hN`. Establish `ht0 : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Establish `hs0 : (0 : ℝ) ≤ (sLen D : ℝ)` using `Nat.cast_nonneg _`. Establish `hv : ∀ j, 0 ≤ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ∧ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ≤ large₂.Sc` using `extend_bounds 2 _ _ hSc.le fun l => large₂.cloud_v τ l`. Establish `hel : ∀ l : Fin D.R.m, 0 ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * large₂.sc.b` using `fun l => by`.

Take `⟨h1, h2⟩` from `hbe τ l`. Establish `h3` using `(D.hc τ).gap_be l`. Establish `ht : (0 : ℚ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `h4 : 0 ≤ (D.hc τ).e l` using `by linarith`. Conclude with `⟨by exact_mod_cast h4, h2⟩`.

Establish `he` using `extend_bounds 1 _ _ (by linarith) hel`. Establish `hcen : ∀ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ ((cen D 1 τ j : ℤ) : ℝ) ∧ ((cen D 1 τ j : ℤ) : ℝ) ≤ large₂.sc.b`. Introduce `j hj1 hj2`. Establish `e` using `GridData.mid_eq (GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0) hj1`. Establish `hv2` using `hv 2`.

Establish `hj1' : (1 : ℝ) ≤ (j : ℝ)` using `by exact_mod_cast hj1`. Establish `hj2' : (j : ℝ) ≤ (D.R.m : ℝ)` using `by exact_mod_cast hj2`. Establish `hmid : 0 ≤ (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ∧ (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ≤ large₂.sc.b`. Rewrite using `[e]`. Simplify using `only [GridData.a, GridData.ofHCParam]`.

Use `push_cast`. Apply the tactic sequence `constructor <;> nlinarith`. Unfold `cen`. Use `⟨by exact_mod_cast Int.floor_nonneg.2 (by exact_mod_cast hmid.1), le_trans ?_ hmid.2⟩` and prove the remaining obligations. Conclude with `Int.floor_le _` after adjusting the coercions.

Introduce `x hx`. Break down `GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, -, -, h⟩` into its components or cases. Take `⟨i, hi, rfl⟩` from `GridData.mem_tops.1 h`. Establish `hi' : (i : ℝ) ≤ (D.R.m : ℝ)` using `by exact_mod_cast (show i ≤ D.R.m from hi)`. Establish `hi0 : (0 : ℝ) ≤ (i : ℝ)` using `Nat.cast_nonneg _`.

Establish `hv2` using `hv 2`. Simplify using `only [GridData.a, num, GridData.ofHCParam]`. Use `push_cast`. Apply the tactic sequence `constructor <;> nlinarith`. Take `⟨i, -, -, rfl⟩` from `GridData.mem_cloudHalf.1 h`.

Establish `h : 0 ≤ (((num D 1 τ).v i : ℤ) : ℝ) ∧ (((num D 1 τ).v i : ℤ) : ℝ) ≤ large₂.Sc` using `hv i`. Simplify using `only [GridData.vHalf]`. Use `push_cast`. Apply the tactic sequence `constructor <;> linarith`. Take `⟨a, ha, rfl⟩` from `GlobalTheory.SignedHC.mem_block.1 h`.

Establish `h : 0 ≤ (((num D 1 τ).cen i : ℤ) : ℝ) ∧ (((num D 1 τ).cen i : ℤ) : ℝ) ≤ large₂.sc.b` using `hcen i hi1 hi2`. Establish `h1 : (((num D 1 τ).s - 1 : ℕ) : ℝ) ≤ (sLen D : ℝ)`. Conclude with `(show sLen D - 1 ≤ sLen D from Nat.sub_le _ _)` after adjusting the coercions. Establish `ha' : (a : ℝ) + 1 ≤ (((num D 1 τ).s - 1 : ℕ) : ℝ)` using `by exact_mod_cast ha`. Establish `ha0 : (0 : ℝ) ≤ (a : ℝ)` using `Nat.cast_nonneg _`.

Simplify using `only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_one, Rat.cast_ofNat]`. Apply the tactic sequence `constructor <;> linarith`. Take `⟨a, ha, rfl⟩` from `GlobalTheory.SignedHC.mem_block.1 h`. Establish `h : 0 ≤ (((num D 1 τ).e l : ℤ) : ℝ) ∧ (((num D 1 τ).e l : ℤ) : ℝ) ≤ 4 * large₂.sc.b` using `he l`. Establish `h1 : ((num D 1 τ).t : ℝ) = (D.R.t : ℝ)` using `rfl`.

Establish `ha' : (a : ℝ) ≤ ((num D 1 τ).t : ℝ)` using `by exact_mod_cast Nat.lt_succ_iff.1 ha`. Establish `ha0 : (0 : ℝ) ≤ (a : ℝ)` using `Nat.cast_nonneg _`. Use `push_cast`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem entry_bounds {D : D7} (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (j : ℕ) (τ : D.what₂.Tau) :
    ∀ x ∈ (num D 1 τ).weightX j, -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
  obtain ⟨hN, -, -, -, hm2, -, -, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, hbe, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hg0 : (0 : ℝ) ≤ (gap D 1 : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hScb : large₂.Sc ≤ large₂.sc.b := by nlinarith
  have hts : D.R.t + sLen D + 1 ≤ bigN D := by
    have : D.R.t + sLen D + 1 ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_left _ (by omega)
    unfold bigN; omega
  have hts' : (D.R.t : ℝ) + (sLen D : ℝ) + 1 ≤ large₂.sc.b := le_trans (by exact_mod_cast hts) hN
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (sLen D : ℝ) := Nat.cast_nonneg _
  have hv : ∀ j, 0 ≤ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ∧ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ≤ large₂.Sc :=
    extend_bounds 2 _ _ hSc.le fun l => large₂.cloud_v τ l
  have hel : ∀ l : Fin D.R.m, 0 ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * large₂.sc.b := fun l => by
    obtain ⟨h1, h2⟩ := hbe τ l
    have h3 := (D.hc τ).gap_be l
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have h4 : 0 ≤ (D.hc τ).e l := by linarith
    exact ⟨by exact_mod_cast h4, h2⟩
  have he := extend_bounds 1 _ _ (by linarith) hel
  have hcen : ∀ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ ((cen D 1 τ j : ℤ) : ℝ) ∧ ((cen D 1 τ j : ℤ) : ℝ) ≤ large₂.sc.b := by
    intro j hj1 hj2
    have e := GridData.mid_eq (GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0) hj1
    have hv2 := hv 2
    have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hj2' : (j : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hj2
    have hmid : 0 ≤ (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ∧
        (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ≤ large₂.sc.b := by
      rw [e]
      simp only [GridData.a, GridData.ofHCParam]
      push_cast
      constructor <;> nlinarith
    unfold cen
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 (by exact_mod_cast hmid.1), le_trans ?_ hmid.2⟩
    exact_mod_cast Int.floor_le _
  intro x hx
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, -, -, h⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    have hi' : (i : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (show i ≤ D.R.m from hi)
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    have hv2 := hv 2
    simp only [GridData.a, num, GridData.ofHCParam]
    push_cast
    constructor <;> nlinarith
  · obtain ⟨i, -, -, rfl⟩ := GridData.mem_cloudHalf.1 h
    have h : 0 ≤ (((num D 1 τ).v i : ℤ) : ℝ) ∧ (((num D 1 τ).v i : ℤ) : ℝ) ≤ large₂.Sc := hv i
    simp only [GridData.vHalf]
    push_cast
    constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have h : 0 ≤ (((num D 1 τ).cen i : ℤ) : ℝ) ∧ (((num D 1 τ).cen i : ℤ) : ℝ) ≤ large₂.sc.b := hcen i hi1 hi2
    have h1 : (((num D 1 τ).s - 1 : ℕ) : ℝ) ≤ (sLen D : ℝ) := by
      exact_mod_cast (show sLen D - 1 ≤ sLen D from Nat.sub_le _ _)
    have ha' : (a : ℝ) + 1 ≤ (((num D 1 τ).s - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_one, Rat.cast_ofNat]
    constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have h : 0 ≤ (((num D 1 τ).e l : ℤ) : ℝ) ∧ (((num D 1 τ).e l : ℤ) : ℝ) ≤ 4 * large₂.sc.b := he l
    have h1 : ((num D 1 τ).t : ℝ) = (D.R.t : ℝ) := rfl
    have ha' : (a : ℝ) ≤ ((num D 1 τ).t : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 ha
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    push_cast
    constructor <;> linarith

/- English proof (translation)
Use `⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩` and prove the remaining obligations. Introduce `D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hch _`. Take `⟨hN, hf, hN1, hf1, -, hrd1, hrd, hb12⟩` from `GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size`. Establish `hlb : 0 ≤ Real.log large₂.sc.b` using `Real.log_nonneg (by linarith)`. Establish `hc : ch.sc.cGap = 1`.

Establish `h : ch.sc = { cGap` using `1, cDep := CF, b := large₂.sc.b } := hch`. Rewrite using `[h]`. Use `⟨by linarith, hN1, hN, hf1, hf, (Lnk.card_Tau D).le, by linarith, ?_, fun j hj => ⟨?_, fun τ i => ?_⟩⟩` and prove the remaining obligations. Conclude with `(Real.log_le_log_iff (by linarith) (by linarith)).1 (by linarith)`. Conclude with `GlobalTheory.DefRank.rank_le_bigN ch.G (.top j) hj`.

Establish `key : ∀ x ∈ entries (Node.par D ch.sc.cGap (.top j) τ), -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b`. Rewrite using `[hc]`. Introduce `x hx`. Establish `e : entries (Node.par D 1 (.top j) τ) = (num D 1 τ).weightX j` using `entries_plus _`. Conclude with `entry_bounds large₂ hS.size j τ x (e ▸ hx)`.

Establish `hw` using `natW_wtOf_le _ _ _ _ (by linarith) key i`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sizesK : BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hch _
  obtain ⟨hN, hf, hN1, hf1, -, hrd1, hrd, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
  have hc : ch.sc.cGap = 1 := by
    have h : ch.sc = { cGap := 1, cDep := CF, b := large₂.sc.b } := hch
    rw [h]
  refine ⟨by linarith, hN1, hN, hf1, hf, (Lnk.card_Tau D).le, by linarith, ?_, fun j hj => ⟨?_, fun τ i => ?_⟩⟩
  · exact (Real.log_le_log_iff (by linarith) (by linarith)).1 (by linarith)
  · exact GlobalTheory.DefRank.rank_le_bigN ch.G (.top j) hj
  · have key : ∀ x ∈ entries (Node.par D ch.sc.cGap (.top j) τ), -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
      rw [hc]
      intro x hx
      have e : entries (Node.par D 1 (.top j) τ) = (num D 1 τ).weightX j := entries_plus _
      exact entry_bounds large₂ hS.size j τ x (e ▸ hx)
    have hw := natW_wtOf_le _ _ _ _ (by linarith) key i
    calc (((wt ch.G (.top j) τ).natW i : ℕ) : ℝ)
        = (((wtOf _ (entries (Node.par D ch.sc.cGap (.top j) τ))).natW i : ℕ) : ℝ) := rfl
      _ ≤ _ := hw
      _ ≤ 8 * large₂.sc.b := by linarith

end GlobalTheory.KerConjMean.TopSizes

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfSize.WtSize

/- English proof (translation)
The claim follows from `|(((wtOf n E).w i : ℤ) : ℝ)| ≤ B + n + 1 := by unfold wtOf split_ifs with h · show |((⌊GlobalTheory.SignedHC.highestWeight E h.1 i⌋ : ℤ) : ℝ)| ≤ _ set y := GlobalTheory.SignedHC.highestWeight E h.1 i with hy have hy' : (y : ℝ) = (GlobalTheory.SignedHC.descEnum E h.1 i : ℝ) - (((n …`.
-/
theorem wtOf_abs_le {n : ℕ} {E : Finset ℚ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ E, |(x : ℝ)| ≤ B) (i : Fin n) :
    |(((wtOf n E).w i : ℤ) : ℝ)| ≤ B + n + 1 := by
  unfold wtOf
  split_ifs with h
  · show |((⌊GlobalTheory.SignedHC.highestWeight E h.1 i⌋ : ℤ) : ℝ)| ≤ _
    set y := GlobalTheory.SignedHC.highestWeight E h.1 i with hy
    have hy' : (y : ℝ) = (GlobalTheory.SignedHC.descEnum E h.1 i : ℝ) - (((n : ℝ) - 1) / 2 - ((i : ℕ) : ℝ)) := by
      rw [hy]; unfold GlobalTheory.SignedHC.highestWeight; push_cast; ring
    have hd := hB _ (GlobalTheory.SignedHC.descEnum_mem E h.1 i)
    have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.2
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
    have f1 : ((⌊y⌋ : ℤ) : ℝ) ≤ y := by exact_mod_cast Int.floor_le y
    have f2 : (y : ℝ) < ⌊y⌋ + 1 := by exact_mod_cast Int.lt_floor_add_one y
    rw [abs_le] at hd ⊢
    constructor <;> linarith [hd.1, hd.2]
  · show |((((0 : Fin n → ℤ) i : ℤ)) : ℝ)| ≤ _
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
    linarith

end GlobalTheory.InfSize.WtSize

namespace GlobalTheory.InfSize.WtSize

/- English proof (translation)
Take `⟨hγb, hb⟩` from `GlobalTheory.BigTop.Fun.gap_le_b hs`. Establish `hs'` using `hs`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩` from `hs'`. Establish `hS` using `large₂.Sc_pos`. Establish `h4` using `(isLeast_gap D 1).1.2.1`.

Establish `hm` using `D.R.two_le_m`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hNg : bigN D ≤ gap D 1`. Use `Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `htN : D.R.t + 1 ≤ bigN D`. Unfold `bigN`. Use `Nat.le_mul_of_pos_left (D.R.t + sLen D + 1) (by omega : 0 < D.R.m)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hsN : sLen D ≤ gap D 1` using `by omega`.

Establish `hγ0 : (0 : ℝ) ≤ gap D 1` using `by positivity`. Establish `hmR : (0 : ℝ) ≤ D.R.m` using `by positivity`. Establish `htR : (D.R.t : ℝ) + 1 ≤ large₂.sc.b`. Establish `h1 : ((D.R.t + 1 : ℕ) : ℝ) ≤ gap D 1` using `by exact_mod_cast htN.trans hNg`. Move the coercions through the operations in `at h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsR : (sLen D : ℝ) ≤ large₂.sc.b`. Establish `h1 : (sLen D : ℝ) ≤ gap D 1` using `by exact_mod_cast hsN`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmγ : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1` using `by positivity`.

Break down `GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, hl1, hl2, h⟩` into its components or cases. Take `⟨i, hi, rfl⟩` from `GlobalTheory.SignedHC.GridData.mem_tops.1 h`. Establish `ev : (D.hc τ).v ⟨0, by omega⟩ = ((num D 1 τ).v 2 : ℚ)` using `(GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨0, by omega⟩`. Take `⟨v0, v1⟩` from `large₂.cloud_v τ ⟨0, by omega⟩`. Rewrite `v0`, `v1` using `[ev]`.

Establish `ha : (num D 1 τ).a i = ((num D 1 τ).v 2 : ℚ) + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D 1 : ℚ)` using `rfl`. Establish `hi' : (i : ℝ) ≤ D.R.m` using `by exact_mod_cast hi`. Establish `hi0 : (0 : ℝ) ≤ i` using `by positivity`. Establish `v0' : (0 : ℝ) ≤ ((num D 1 τ).v 2 : ℝ)` using `by exact_mod_cast v0`. Establish `v1' : ((num D 1 τ).v 2 : ℝ) ≤ large₂.Sc` using `by exact_mod_cast v1`.

Rewrite using `[ha]`. Use `push_cast`. Establish `p1 : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ)` using `mul_nonneg (by linarith) hγ0`. Establish `p2 : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1` using `by nlinarith`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`.

Take `⟨i, hi2, hik, rfl⟩` from `GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h`. Establish `hik' : i ≤ D.R.k` using `hik`. Establish `ev : (D.hc τ).v ⟨i - 2, by omega⟩ = ((num D 1 τ).v (i - 2 + 2) : ℚ)` using `(GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨i - 2, by omega⟩`. Rewrite `ev` using `[show i - 2 + 2 = i by omega]`. Take `⟨v0, v1⟩` from `large₂.cloud_v τ ⟨i - 2, by omega⟩`.

Rewrite `v0`, `v1` using `[ev]`. Establish `v0' : (0 : ℝ) ≤ ((num D 1 τ).v i : ℝ)` using `by exact_mod_cast v0`. Establish `v1' : ((num D 1 τ).v i : ℝ) ≤ large₂.Sc` using `by exact_mod_cast v1`. Unfold `GlobalTheory.SignedHC.GridData.vHalf`. Use `push_cast`.

Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Take `⟨a, ha, rfl⟩` from `GlobalTheory.SignedHC.mem_block.1 h`. Take `⟨c0, c1⟩` from `GlobalTheory.BigTop.Fun.cen_bounds hs τ hi1 hi2`. Establish `ec : (num D 1 τ).cen i = cen D 1 τ i` using `rfl`. Establish `es : (num D 1 τ).s = sLen D` using `rfl`.

Rewrite using `[ec, es]`. Establish `hs1 : (((sLen D - 1 : ℕ)) : ℝ) ≤ large₂.sc.b`. Establish `: ((sLen D - 1 : ℕ) : ℝ) ≤ sLen D` using `by exact_mod_cast Nat.sub_le _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha' : (a : ℝ) + 1 ≤ ((sLen D - 1 : ℕ) : ℝ)` using `by exact_mod_cast ha`.

Establish `ha0 : (0 : ℝ) ≤ a` using `by positivity`. Establish `c0' : (0 : ℝ) ≤ (cen D 1 τ i : ℝ)` using `by exact_mod_cast c0`. Use `push_cast`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Take `⟨a, ha, rfl⟩` from `GlobalTheory.SignedHC.mem_block.1 h`.

Establish `hl2' : l ≤ D.R.m` using `hl2`. Take `⟨e0, e1⟩` from `GlobalTheory.BigTop.Fun.numE_bounds hs τ (j := l - 1) (by omega)`. Rewrite `e0`, `e1` using `[show l - 1 + 1 = l by omega]`. Establish `et : (num D 1 τ).t = D.R.t` using `rfl`. Rewrite using `[et]`.

Establish `ha' : (a : ℝ) + 1 ≤ (D.R.t : ℝ) + 1` using `by exact_mod_cast ha`. Establish `ha0 : (0 : ℝ) ≤ a` using `by positivity`. Establish `e0' : (0 : ℝ) ≤ ((num D 1 τ).e l : ℝ)` using `by exact_mod_cast e0`. Use `push_cast`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`.
-/
theorem weightX_abs_le {D : D7} {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (τ : D.what₂.Tau) {x : ℚ}
    (hx : x ∈ (num D 1 τ).weightX D.R.m) : |(x : ℝ)| ≤ 5 * large₂.sc.b := by
  obtain ⟨hγb, hb⟩ := GlobalTheory.BigTop.Fun.gap_le_b hs
  have hs' := hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs'
  have hS := large₂.Sc_pos
  have h4 := (isLeast_gap D 1).1.2.1
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hNg : bigN D ≤ gap D 1 := by
    have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)
    omega
  have htN : D.R.t + 1 ≤ bigN D := by
    unfold bigN
    have := Nat.le_mul_of_pos_left (D.R.t + sLen D + 1) (by omega : 0 < D.R.m)
    omega
  have hsN : sLen D ≤ gap D 1 := by omega
  have hγ0 : (0 : ℝ) ≤ gap D 1 := by positivity
  have hmR : (0 : ℝ) ≤ D.R.m := by positivity
  have htR : (D.R.t : ℝ) + 1 ≤ large₂.sc.b := by
    have h1 : ((D.R.t + 1 : ℕ) : ℝ) ≤ gap D 1 := by exact_mod_cast htN.trans hNg
    push_cast at h1
    linarith
  have hsR : (sLen D : ℝ) ≤ large₂.sc.b := by
    have h1 : (sLen D : ℝ) ≤ gap D 1 := by exact_mod_cast hsN
    linarith
  have hmγ : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by positivity
  rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, hl1, hl2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
    have ev : (D.hc τ).v ⟨0, by omega⟩ = ((num D 1 τ).v 2 : ℚ) :=
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨0, by omega⟩
    obtain ⟨v0, v1⟩ := large₂.cloud_v τ ⟨0, by omega⟩
    rw [ev] at v0 v1
    have ha : (num D 1 τ).a i = ((num D 1 τ).v 2 : ℚ) + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D 1 : ℚ) := rfl
    have hi' : (i : ℝ) ≤ D.R.m := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have v0' : (0 : ℝ) ≤ ((num D 1 τ).v 2 : ℝ) := by exact_mod_cast v0
    have v1' : ((num D 1 τ).v 2 : ℝ) ≤ large₂.Sc := by exact_mod_cast v1
    rw [ha]
    push_cast
    have p1 : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) := mul_nonneg (by linarith) hγ0
    have p2 : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by nlinarith
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨i, hi2, hik, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
    have hik' : i ≤ D.R.k := hik
    have ev : (D.hc τ).v ⟨i - 2, by omega⟩ = ((num D 1 τ).v (i - 2 + 2) : ℚ) :=
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨i - 2, by omega⟩
    rw [show i - 2 + 2 = i by omega] at ev
    obtain ⟨v0, v1⟩ := large₂.cloud_v τ ⟨i - 2, by omega⟩
    rw [ev] at v0 v1
    have v0' : (0 : ℝ) ≤ ((num D 1 τ).v i : ℝ) := by exact_mod_cast v0
    have v1' : ((num D 1 τ).v i : ℝ) ≤ large₂.Sc := by exact_mod_cast v1
    unfold GlobalTheory.SignedHC.GridData.vHalf
    push_cast
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    obtain ⟨c0, c1⟩ := GlobalTheory.BigTop.Fun.cen_bounds hs τ hi1 hi2
    have ec : (num D 1 τ).cen i = cen D 1 τ i := rfl
    have es : (num D 1 τ).s = sLen D := rfl
    rw [ec, es]
    have hs1 : (((sLen D - 1 : ℕ)) : ℝ) ≤ large₂.sc.b := by
      have : ((sLen D - 1 : ℕ) : ℝ) ≤ sLen D := by exact_mod_cast Nat.sub_le _ _
      linarith
    have ha' : (a : ℝ) + 1 ≤ ((sLen D - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have c0' : (0 : ℝ) ≤ (cen D 1 τ i : ℝ) := by exact_mod_cast c0
    push_cast
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have hl2' : l ≤ D.R.m := hl2
    obtain ⟨e0, e1⟩ := GlobalTheory.BigTop.Fun.numE_bounds hs τ (j := l - 1) (by omega)
    rw [show l - 1 + 1 = l by omega] at e0 e1
    have et : (num D 1 τ).t = D.R.t := rfl
    rw [et]
    have ha' : (a : ℝ) + 1 ≤ (D.R.t : ℝ) + 1 := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have e0' : (0 : ℝ) ≤ ((num D 1 τ).e l : ℝ) := by exact_mod_cast e0
    push_cast
    rw [abs_le]; constructor <;> linarith

/- English proof (translation)
Use `⟨7, fun D large₂ hs T L sc G hc τ i => ?_⟩` and prove the remaining obligations. Take `⟨hγb, hb⟩` from `GlobalTheory.BigTop.Fun.gap_le_b hs`. Establish `h4` using `(isLeast_gap D 1).1.2.1`. Establish `hNg : bigN D ≤ gap D 1`. Use `Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hn` using `GlobalTheory.DefRank.rank_le_bigN G (.top D.R.m) (show D.R.m ≤ D.R.m from le_rfl)`. Establish `hnb : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ large₂.sc.b`. Establish `: (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ gap D 1` using `by exact_mod_cast hn.trans hNg`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e : wt G (.top D.R.m) τ = wtOf (G.V (.top D.R.m)).rank ((num D 1 τ).weightX D.R.m)` using `by show wtOf _ (GlobalTheory.SignedHC.entries (Node.par D sc.cGap (.top D.R.m) τ)) = _`. Rewrite using `[hc]`. Conclude with `congrArg _ (GlobalTheory.SignedHC.entries_plus _)`. Rewrite using `[e]`. Use `wtOf_abs_le (B := 5 * large₂.sc.b) (by linarith) (fun x hx => weightX_abs_le hs τ hx) i` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wt_top_abs_le : ∃ K1 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), sc.cGap = 1 → ∀ τ i, |(((wt G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ K1 * large₂.sc.b := by
  refine ⟨7, fun D large₂ hs T L sc G hc τ i => ?_⟩
  obtain ⟨hγb, hb⟩ := GlobalTheory.BigTop.Fun.gap_le_b hs
  have h4 := (isLeast_gap D 1).1.2.1
  have hNg : bigN D ≤ gap D 1 := by
    have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)
    omega
  have hn := GlobalTheory.DefRank.rank_le_bigN G (.top D.R.m) (show D.R.m ≤ D.R.m from le_rfl)
  have hnb : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ large₂.sc.b := by
    have : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ gap D 1 := by exact_mod_cast hn.trans hNg
    linarith
  have e : wt G (.top D.R.m) τ = wtOf (G.V (.top D.R.m)).rank ((num D 1 τ).weightX D.R.m) := by
    show wtOf _ (GlobalTheory.SignedHC.entries (Node.par D sc.cGap (.top D.R.m) τ)) = _
    rw [hc]
    exact congrArg _ (GlobalTheory.SignedHC.entries_plus _)
  rw [e]
  have := wtOf_abs_le (B := 5 * large₂.sc.b) (by linarith) (fun x hx => weightX_abs_le hs τ hx) i
  linarith

end GlobalTheory.InfSize.WtSize

end

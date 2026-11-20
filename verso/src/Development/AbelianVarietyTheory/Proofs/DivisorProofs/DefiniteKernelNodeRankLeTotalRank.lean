import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.DefRank

/- English proof (translation)
Introduce `D T L sc G X hX`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hm` using `D.R.two_le_m`. Break down `X with ⟨_ | i, j⟩ | i | j` into its components or cases. Take `rfl` from `hX.2`.

Establish `e : G.V (.grid 0 D.R.m) = D.sp.X'` using `congrArg LSp.sp (colY_m L)`. Rewrite using `[e, D.sp.X'_rank]`. Use `show D.R.r + D.R.m * D.R.t ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)`. Establish `e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m` using `by ring`. Use linear arithmetic over natural numbers and integers.

Take `⟨hi, rfl⟩` from `hX`. Rewrite using `[(G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (by simp)).rank]`. Use `show D.R.r + D.R.m * D.R.t + (i + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)`. Use `Nat.mul_le_mul_right (sLen D) hi` as an intermediate fact. Establish `e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m` using `by ring`.

Use linear arithmetic over natural numbers and integers. Conclude with `hX.elim`. Rewrite using `[(G.isV (X := .top j) hX (by simp)).rank] show nRk D + D.R.m * (sLen D - 1) + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)`. Establish `h1` using `Nat.mul_le_mul_right (D.R.t + 1) (show j ≤ D.R.m from hX)`. Establish `hs : sLen D - 1 + 1 = sLen D` using `by unfold sLen; omega`.

Establish `hn : nRk D = D.R.r + 1` using `rfl`. Establish `e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * (sLen D - 1) + D.R.m * (D.R.t + 1) + D.R.m` using `by conv_lhs => rw [← hs]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : j * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1)` using `h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem rank_le_bigN : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node),
    DefNode D.R.m X → (G.V X).rank ≤ bigN D := by
  intro D T L sc G X hX
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hm := D.R.two_le_m
  rcases X with ⟨_ | i, j⟩ | i | j
  · obtain rfl := hX.2
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e, D.sp.X'_rank]
    show D.R.r + D.R.m * D.R.t ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    omega
  · obtain ⟨hi, rfl⟩ := hX
    rw [(G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (by simp)).rank]
    show D.R.r + D.R.m * D.R.t + (i + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have := Nat.mul_le_mul_right (sLen D) hi
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    omega
  · exact hX.elim
  · rw [(G.isV (X := .top j) hX (by simp)).rank]
    show nRk D + D.R.m * (sLen D - 1) + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have h1 := Nat.mul_le_mul_right (D.R.t + 1) (show j ≤ D.R.m from hX)
    have hs : sLen D - 1 + 1 = sLen D := by unfold sLen; omega
    have hn : nRk D = D.R.r + 1 := rfl
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * (sLen D - 1) + D.R.m * (D.R.t + 1) + D.R.m := by
      conv_lhs => rw [← hs]
      ring
    have h2 : j * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := h1
    omega

end GlobalTheory.DefRank

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ChiGrid

/- English proof (translation)
Use `set P := D.hc τ with hP`. Use `set G := GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) 0 with hG`. Take `⟨hv, hb, -⟩` from `GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) 0`. Establish `he` using `(GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) (cen D C τ)).2.2 j`. Establish `hne : (num D C τ).e (j + 1) = (GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) (cen D C τ)).e (j.1 + 1)` using `rfl`.

Establish `hj` using `j.2`. Establish `hi` using `i.2`. Establish `hk : D.R.m + 3 ≤ D.R.k` using `D.R.m_add_three_le_k`. Establish `hGm : G.m = D.R.m` using `rfl`. Establish `hGk : G.k = D.R.k` using `rfl`.

Establish `hGga : G.ga = gap D C` using `rfl`. Establish `h1` using `P.gap_be j`. Establish `e0 : P.b ⟨0, by omega⟩ = (G.b 1 : ℚ)` using `hb ⟨0, by omega⟩`. Establish `ej : P.b j = (G.b (j.1 + 1) : ℚ)` using `hb j`. Establish `h2 : P.b ⟨0, by omega⟩ ≤ P.b j`.

Break down `Nat.eq_zero_or_pos j.1 with h0 | hj0` into its components or cases. Conclude with `le_of_eq (congrArg P.b (Fin.ext (by simp [h0])))`. Use `G.b_mono 1 (j.1 + 1) le_rfl (by omega) (by rw [hGm]; omega)` as an intermediate fact. Rewrite using `[e0, ej]`. Conclude with `this.le` after adjusting the coercions.

Establish `hu2` using `P.u_last_gt (by omega) (by omega)`. Establish `hu1` using `P.v_gt_u ⟨D.R.k - 2, by omega⟩`. Establish `hu : P.u ⟨D.R.k - 2 + 1, by omega⟩ = P.u ⟨D.R.k - 1, by omega⟩` using `congrArg P.u (Fin.ext (by dsimp only; omega))`. Establish `ev0 : P.v ⟨0, by omega⟩ = (G.v 2 : ℚ)` using `hv ⟨0, by omega⟩`. Establish `evl : P.v ⟨D.R.k - 2, by omega⟩ = (G.v D.R.k : ℚ)`.

Use `hv ⟨D.R.k - 2, by omega⟩` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[Nat.sub_add_cancel (by omega : 2 ≤ D.R.k)]`. Then use the resulting hypothesis. Establish `hvv : G.v D.R.k < G.v 2` using `G.v_anti 2 D.R.k le_rfl (by omega) (by rw [hGk])`. Establish `hvv' : (G.v D.R.k : ℚ) < G.v 2` using `by exact_mod_cast hvv`.

Rewrite `hu1` using `[hu]`. Rewrite `hu1` using `[evl]`. Establish `hc : G.mid (D.R.m - i) < (cen D C τ (D.R.m - i) : ℚ) + 1` using `Int.lt_floor_add_one _`. Establish `hmid : G.mid (D.R.m - i) = G.a (D.R.m - i) + G.ga / 2` using `G.mid_eq (by omega)`. Establish `ha : G.a (D.R.m - i) = (G.v 2 : ℚ) + 1 / 2 + ((i : ℚ) + 1) * (gap D C : ℚ)`.

Simplify using `only [GlobalTheory.SignedHC.GridData.a, hGm, hGga]`. Rewrite using `[Nat.cast_sub hi.le]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hc` using `[hmid, ha, hGga]`. Establish `hg` using `(isLeast_gap D C).1.2.1`.

Establish `hN : bigN D ≤ bigN D ^ 3` using `Nat.le_self_pow (by norm_num) _`. Establish `hr : D.R.r + 1 = D.R.k + D.R.m` using `by unfold Formalism.BasicNotions.Ranks.r; omega`. Establish `m1 : (j.1 + 1) * D.R.t ≤ D.R.m * D.R.t` using `Nat.mul_le_mul_right _ (by omega)`. Establish `m2 : j.1 * D.R.t ≤ D.R.m * D.R.t` using `Nat.mul_le_mul_right _ (by omega)`. Establish `m3 : (i.1 + 1) * sLen D ≤ D.R.m * sLen D` using `Nat.mul_le_mul_right _ (by omega)`.

Establish `m4 : i.1 * sLen D ≤ D.R.m * sLen D` using `Nat.mul_le_mul_right _ (by omega)`. Establish `hrank : rankV D (i.1 + 1) (j.1 + 1) + rankV D i.1 j.1 ≤ 2 * bigN D`. Unfold `rankV bigN`. Use the polynomial consequences of the given equalities and inequalities. Establish `hbot : GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j ≤ rankV D (i.1 + 1) (j.1 + 1) + rankV D i.1 j.1`.

Unfold `GlobalTheory.FunObj.SqNum.botBig GlobalTheory.FunObj.SqNum.botSmall`. Use linear arithmetic over natural numbers and integers. Establish `hR : GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j + 1 ≤ gap D C` using `by omega`. Establish `hR' : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) + 1 ≤ (gap D C : ℚ)`. Conclude with `hR` after adjusting the coercions.

Establish `hpos : (0 : ℚ) ≤ (i : ℚ) * (gap D C : ℚ)` using `by positivity`. Establish `ht : (0 : ℚ) ≤ D.R.t` using `by positivity`. Establish `h0 : (0 : ℚ) ≤ ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ)` using `by positivity`. Establish `key : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) < 2 * ((num D C τ).e (j + 1) : ℚ) + 2 * (cen D C τ (D.R.m - i) : ℚ)`. Rewrite using `[hne, ← he]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `key' : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) < 2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i))`. Establish `: (((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) : ℚ) < ((2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i)) : ℤ) : ℚ)` using `by push_cast; push_cast at key; linarith`. Conclude with `this` after adjusting the coercions. Conclude with `key'.le`.
-/
theorem botBig_add_botSmall_le_two_e_add_two_cen (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) :
    ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) ≤
      2 * ((GlobalTheory.ChiGrid.num D C τ).e (j + 1) + GlobalTheory.ChiGrid.cen D C τ (D.R.m - i)) := by
  set P := D.hc τ with hP
  set G := GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) 0 with hG
  obtain ⟨hv, hb, -⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) 0
  have he := (GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) (cen D C τ)).2.2 j
  have hne : (num D C τ).e (j + 1) = (GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) (cen D C τ)).e (j.1 + 1) := rfl
  have hj := j.2
  have hi := i.2
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGga : G.ga = gap D C := rfl
  have h1 := P.gap_be j
  have e0 : P.b ⟨0, by omega⟩ = (G.b 1 : ℚ) := hb ⟨0, by omega⟩
  have ej : P.b j = (G.b (j.1 + 1) : ℚ) := hb j
  have h2 : P.b ⟨0, by omega⟩ ≤ P.b j := by
    rcases Nat.eq_zero_or_pos j.1 with h0 | hj0
    · exact le_of_eq (congrArg P.b (Fin.ext (by simp [h0])))
    · have := G.b_mono 1 (j.1 + 1) le_rfl (by omega) (by rw [hGm]; omega)
      rw [e0, ej]; exact_mod_cast this.le
  have hu2 := P.u_last_gt (by omega) (by omega)
  have hu1 := P.v_gt_u ⟨D.R.k - 2, by omega⟩
  have hu : P.u ⟨D.R.k - 2 + 1, by omega⟩ = P.u ⟨D.R.k - 1, by omega⟩ :=
    congrArg P.u (Fin.ext (by dsimp only; omega))
  have ev0 : P.v ⟨0, by omega⟩ = (G.v 2 : ℚ) := hv ⟨0, by omega⟩
  have evl : P.v ⟨D.R.k - 2, by omega⟩ = (G.v D.R.k : ℚ) := by
    have := hv ⟨D.R.k - 2, by omega⟩
    dsimp only at this
    rwa [Nat.sub_add_cancel (by omega : 2 ≤ D.R.k)] at this
  have hvv : G.v D.R.k < G.v 2 := G.v_anti 2 D.R.k le_rfl (by omega) (by rw [hGk])
  have hvv' : (G.v D.R.k : ℚ) < G.v 2 := by exact_mod_cast hvv
  rw [hu] at hu1
  rw [evl] at hu1
  have hc : G.mid (D.R.m - i) < (cen D C τ (D.R.m - i) : ℚ) + 1 := Int.lt_floor_add_one _
  have hmid : G.mid (D.R.m - i) = G.a (D.R.m - i) + G.ga / 2 := G.mid_eq (by omega)
  have ha : G.a (D.R.m - i) = (G.v 2 : ℚ) + 1 / 2 + ((i : ℚ) + 1) * (gap D C : ℚ) := by
    simp only [GlobalTheory.SignedHC.GridData.a, hGm, hGga]
    rw [Nat.cast_sub hi.le]; ring
  rw [hmid, ha, hGga] at hc
  have hg := (isLeast_gap D C).1.2.1
  have hN : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Formalism.BasicNotions.Ranks.r; omega
  have m1 : (j.1 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m2 : j.1 * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m3 : (i.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have m4 : i.1 * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have hrank : rankV D (i.1 + 1) (j.1 + 1) + rankV D i.1 j.1 ≤ 2 * bigN D := by
    unfold rankV bigN; nlinarith
  have hbot : GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j ≤
      rankV D (i.1 + 1) (j.1 + 1) + rankV D i.1 j.1 := by
    unfold GlobalTheory.FunObj.SqNum.botBig GlobalTheory.FunObj.SqNum.botSmall; omega
  have hR : GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j + 1 ≤ gap D C := by omega
  have hR' : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) + 1 ≤ (gap D C : ℚ) := by
    exact_mod_cast hR
  have hpos : (0 : ℚ) ≤ (i : ℚ) * (gap D C : ℚ) := by positivity
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have h0 : (0 : ℚ) ≤ ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) := by positivity
  have key : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℚ) <
      2 * ((num D C τ).e (j + 1) : ℚ) + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
    rw [hne, ← he]
    nlinarith
  have key' : ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) <
      2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i)) := by
    have : (((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) : ℚ) <
        ((2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i)) : ℤ) : ℚ) := by
      push_cast; push_cast at key; linarith
    exact_mod_cast this
  exact key'.le

end GlobalTheory.ChiGrid

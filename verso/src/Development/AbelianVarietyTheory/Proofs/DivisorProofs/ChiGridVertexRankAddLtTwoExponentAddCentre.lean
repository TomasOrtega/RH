import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ChiGrid

/- English proof (translation)
Use `set P := D.hc τ with hP`. Use `set G := GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) 0 with hG`. Take `⟨hv, hb, -⟩` from `GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) 0`. Establish `hk : D.R.m + 3 ≤ D.R.k` using `D.R.m_add_three_le_k`. Establish `hGm : G.m = D.R.m` using `rfl`.

Establish `hGk : G.k = D.R.k` using `rfl`. Establish `hGga : G.ga = gap D C` using `rfl`. Establish `h1` using `P.gap_be ⟨j, hj⟩`. Establish `e0 : P.b ⟨0, by omega⟩ = (G.b 1 : ℚ)` using `hb ⟨0, by omega⟩`. Establish `ej : P.b ⟨j, hj⟩ = (G.b (j + 1) : ℚ)` using `hb ⟨j, hj⟩`.

Establish `h2 : P.b ⟨0, by omega⟩ ≤ P.b ⟨j, hj⟩`. Break down `Nat.eq_zero_or_pos j with rfl | hj0` into its components or cases. Conclude with `le_rfl`. Use `G.b_mono 1 (j + 1) le_rfl (by omega) (by rw [hGm]; omega)` as an intermediate fact. Rewrite using `[e0, ej]`.

Conclude with `this.le` after adjusting the coercions. Establish `hu2` using `P.u_last_gt (by omega) (by omega)`. Establish `hu1` using `P.v_gt_u ⟨D.R.k - 2, by omega⟩`. Establish `hu : P.u ⟨D.R.k - 2 + 1, by omega⟩ = P.u ⟨D.R.k - 1, by omega⟩` using `congrArg P.u (Fin.ext (by dsimp only; omega))`. Establish `ev0 : P.v ⟨0, by omega⟩ = (G.v 2 : ℚ)` using `hv ⟨0, by omega⟩`.

Establish `evl : P.v ⟨D.R.k - 2, by omega⟩ = (G.v D.R.k : ℚ)`. Use `hv ⟨D.R.k - 2, by omega⟩` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[Nat.sub_add_cancel (by omega : 2 ≤ D.R.k)]`. Then use the resulting hypothesis. Establish `hvv : G.v D.R.k < G.v 2` using `G.v_anti 2 D.R.k le_rfl (by omega) (by rw [hGk])`.

Establish `hvv' : (G.v D.R.k : ℚ) < G.v 2` using `by exact_mod_cast hvv`. Rewrite `hu1` using `[hu]`. Rewrite `hu1` using `[evl]`. Establish `hc : G.mid (D.R.m - i) < (cen D C τ (D.R.m - i) : ℚ) + 1` using `Int.lt_floor_add_one _`. Establish `hmid : G.mid (D.R.m - i) = G.a (D.R.m - i) + G.ga / 2` using `G.mid_eq (by omega)`.

Establish `ha : G.a (D.R.m - i) = (G.v 2 : ℚ) + 1 / 2 + ((i : ℚ) + 1) * (gap D C : ℚ)`. Simplify using `only [GlobalTheory.SignedHC.GridData.a, hGm, hGga]`. Rewrite using `[Nat.cast_sub hi.le]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hc` using `[hmid, ha, hGga]`.

Establish `hg` using `(isLeast_gap D C).1.2.1`. Establish `hN : bigN D ≤ bigN D ^ 3` using `Nat.le_self_pow (by norm_num) _`. Establish `hr : D.R.r + 1 = D.R.k + D.R.m` using `by unfold Formalism.BasicNotions.Ranks.r; omega`. Establish `m1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t` using `Nat.mul_le_mul_right _ (by omega)`. Establish `m2 : j * D.R.t ≤ D.R.m * D.R.t` using `Nat.mul_le_mul_right _ (by omega)`.

Establish `m3 : (i + 1) * sLen D ≤ D.R.m * sLen D` using `Nat.mul_le_mul_right _ (by omega)`. Establish `m4 : i * sLen D ≤ D.R.m * sLen D` using `Nat.mul_le_mul_right _ (by omega)`. Establish `hrank : rankV D (i + 1) (j + 1) + rankV D i j ≤ 2 * bigN D`. Unfold `rankV bigN`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hR : rankV D (i + 1) (j + 1) + rankV D i j + 1 ≤ gap D C` using `by omega`. Establish `hR' : ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) + 1 ≤ (gap D C : ℚ)` using `by exact_mod_cast hR`. Establish `hpos : (0 : ℚ) ≤ (i : ℚ) * (gap D C : ℚ)` using `by positivity`. Establish `ht : (0 : ℚ) ≤ D.R.t` using `by positivity`. Establish `h0 : (0 : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem rankV_add_lt_two_e_add_two_cen {D : D7} (C : ℝ) (τ : D.what₂.Tau) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) :
    ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) < 2 * (D.hc τ).e ⟨j, hj⟩ + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
  set P := D.hc τ with hP
  set G := GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) 0 with hG
  obtain ⟨hv, hb, -⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) 0
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGga : G.ga = gap D C := rfl

  have h1 := P.gap_be ⟨j, hj⟩

  have e0 : P.b ⟨0, by omega⟩ = (G.b 1 : ℚ) := hb ⟨0, by omega⟩
  have ej : P.b ⟨j, hj⟩ = (G.b (j + 1) : ℚ) := hb ⟨j, hj⟩
  have h2 : P.b ⟨0, by omega⟩ ≤ P.b ⟨j, hj⟩ := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact le_rfl
    · have := G.b_mono 1 (j + 1) le_rfl (by omega) (by rw [hGm]; omega)
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
  have m1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m2 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m3 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have m4 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have hrank : rankV D (i + 1) (j + 1) + rankV D i j ≤ 2 * bigN D := by
    unfold rankV bigN; nlinarith
  have hR : rankV D (i + 1) (j + 1) + rankV D i j + 1 ≤ gap D C := by omega
  have hR' : ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) + 1 ≤ (gap D C : ℚ) := by exact_mod_cast hR
  have hpos : (0 : ℚ) ≤ (i : ℚ) * (gap D C : ℚ) := by positivity
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have h0 : (0 : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by positivity
  nlinarith

end GlobalTheory.ChiGrid

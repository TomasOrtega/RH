import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WtPar

/- English proof (translation)
Rewrite using `[Fin.univ_val_map, List.ofFn_eq_map, Multiset.range, Multiset.map_coe, ← List.map_coe_finRange_eq_range, List.map_map]`. Both sides reduce to the same expression.
-/
lemma univ_map_eq_range {α : Type} (n : ℕ) (f : ℕ → α) :
    (Finset.univ : Finset (Fin n)).val.map (fun i : Fin n => f (i : ℕ)) = (Multiset.range n).map f := by
  rw [Fin.univ_val_map, List.ofFn_eq_map, Multiset.range, Multiset.map_coe, ← List.map_coe_finRange_eq_range,
    List.map_map]
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hx`.
-/
lemma transport {D : D7} {j : ℕ} {τ : D.what₂.Tau} {n n' : ℕ} (h : n = n')
    (hx : ∃ lam : DomWeight n, Bridge.IsLamPrime (D := D) lam j τ) :
    ∃ lam : DomWeight n', Bridge.IsLamPrime (D := D) lam j τ := by
  subst h; exact hx

/- English proof (translation)
Establish `hN : W.nV = W.p + W.q + W.t`. Simplify using `only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r, Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q]`. Use linear arithmetic over natural numbers and integers. Establish `hNq : (W.nV : ℚ) = W.p + W.q + W.t` using `by exact_mod_cast hN`. Simplify using `only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau, Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV, Formalism.IndefR.IndefiniteWeightData.WeightDa …`.

Use `split_ifs with h1 h2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hNq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : W.q + 1 - (W.q + 1 - (i - W.p - W.t)) = i - W.p - W.t` using `by omega`.

Rewrite using `[hc]`. Establish `hc' : ((i - W.p - W.t : ℕ) : ℚ) = i - W.p - W.t`. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]`. Rewrite using `[hc', hNq]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma lamPrime_add_rho (W : Formalism.IndefR.IndefiniteWeightData.WeightData) (hk : 1 ≤ W.k) (hj : 1 ≤ W.j) (hjm : W.j ≤ W.m)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ W.nV) :
    W.lamPrime i + W.rhoNV i = W.uSideTarget i - 1 / 2 := by
  have hN : W.nV = W.p + W.q + W.t := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q]; omega
  have hNq : (W.nV : ℚ) = W.p + W.q + W.t := by exact_mod_cast hN
  simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt,
    Formalism.IndefR.IndefiniteWeightData.WeightData.dTau, Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV,
    Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus,
    Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus]
  split_ifs with h1 h2
  · ring
  · rw [hNq]; ring
  · have hc : W.q + 1 - (W.q + 1 - (i - W.p - W.t)) = i - W.p - W.t := by omega
    rw [hc]
    have hc' : ((i - W.p - W.t : ℕ) : ℚ) = i - W.p - W.t := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [hc', hNq]; ring

end GlobalTheory.Mem.WtPar

namespace GlobalTheory.Mem.WtPar

/- English proof (translation)
Introduce `D j τ`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hjm` using `j.2`. Establish `hex : ∃ lam : DomWeight D.R.nV, Bridge.IsLamPrime (D` using `D) lam ((j : ℕ) + 1) τ := by`. Establish `h0` using `GlobalTheory.ForcedWeights.lamLForced D ((j : ℕ) + 1) (by omega) (by omega) τ`.

Establish `hr : (D.sp.V ((j : ℕ) + 1)).rank = D.R.nV` using `D.sp.V_rank _ (by omega) (by omega)`. Conclude with `transport hr ⟨_, h0⟩`. Establish `hl : Bridge.IsLamPrime (D` using `D) (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by`. Unfold `Bridge.lamLdef`. Rewrite using `[dif_pos hex]`.

Conclude with `hex.choose_spec`. Use `set lam := Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ`. Take `⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hw⟩` from `hl`. Establish `hWn : W.nV = D.R.nV`. Simplify using `only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r, Ranks.nV, Ranks.r, hWk, hWm, hWt]`.

Establish `hWp : W.p = D.R.k + (j : ℕ)`. Simplify using `only [Formalism.IndefR.IndefiniteWeightData.WeightData.p, hWk, hWj]`. Use linear arithmetic over natural numbers and integers. Set `g : ℕ → ℚ` to `fun i => W.uSideTarget (i + 1) - 1 / 2`. Establish `hL : NG.infOf lam.w = (Multiset.range D.R.nV).map (fun i => ((g i : ℚ) : ℂ))`.

Unfold `NG.infOf`. Rewrite using `[← univ_map_eq_range]`. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1` using `lamPrime_add_rho W (by omega) (by omega) (by omega) ((i : ℕ) + 1) (by omega) (by have := i.2; omega)`. Establish `h2` using `hw i`.

Establish `key : ((lam.w i : ℤ) : ℚ) + ((D.R.nV : ℚ) - 1) / 2 - ((i : ℕ) : ℚ) = g i`. Simplify using `only [g]`. Rewrite using `[h2, ← h1]`. Simplify using `only [Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV, hWn]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `congrArg (fun x : ℚ => (x : ℂ)) key` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Conclude with `this`. Set `gv : ℕ → ℚ` to `fun n => (W.v (n + 2) : ℚ) - 1 / 2`.

Set `gb : ℕ → ℚ` to `fun n => -(W.b (n + 1) : ℚ) - 1 / 2`. Set `ge : ℕ → ℚ` to `fun c => -(W.e : ℚ) - 1 / 2 + ((D.R.t : ℚ) - 1 - 2 * c) / 2`. Establish `hR : NG.paramV D.R (D.hc τ) j (1 / 2) = ((Multiset.range (D.R.k - 1)).map gv + (Multiset.range D.R.m).map gb + (Multiset.range D.R.t).map ge).map (fun x : ℚ => (x : ℂ))`. Simplify using `only [Multiset.map_add, Multiset.map_map]`. Unfold `NG.paramV`.

Use `congr 1`. Use `congr 1`. Rewrite using `[← univ_map_eq_range]`. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, gv, hWv i]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← univ_map_eq_range]`. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, gb, hWb i]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `Multiset.map_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `he : (D.hc τ).e j = (W.e : ℚ)`. Rewrite using `[hWe]`.

Use `congr 1`. Apply the tactic sequence `try (ext; simp)`. Simplify using `only [Function.comp, ge, he]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hL, hR, show (fun i => ((g i : ℚ) : ℂ)) = (fun x : ℚ => (x : ℂ)) ∘ g from rfl, ← Multiset.map_map]`. Use `congr 1`. Establish `hsplit : D.R.nV = ((D.R.k - 1) + ((j : ℕ) + 1)) + D.R.t + (D.R.m - ((j : ℕ) + 1))`. Simplify using `only [Ranks.nV, Ranks.r]`. Use linear arithmetic over natural numbers and integers.

Establish `hmsplit : D.R.m = ((j : ℕ) + 1) + (D.R.m - ((j : ℕ) + 1))` using `by omega`. Rewrite using `[hsplit, Multiset.range_add, Multiset.range_add, Multiset.range_add]`. Use `conv_rhs => rw [hmsplit, Multiset.range_add]`. Simplify using `only [Multiset.map_add, Multiset.map_map]`. Establish `e1 : (Multiset.range (D.R.k - 1)).map g = (Multiset.range (D.R.k - 1)).map gv`.

Use `Multiset.map_congr rfl fun n hn => ?_` and prove the remaining obligations. Rewrite `hn` using `[Multiset.mem_range]`. Simplify using `only [g, gv, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam, hWp, hWk]`. Rewrite using `[if_pos (by omega), if_pos (by omega)]`. Establish `e2 : (Multiset.range ((j : ℕ) + 1)).map (g ∘ fun x => D.R.k - 1 + x) = (Multiset.range ((j : ℕ) + 1)).map gb`.

Use `Multiset.map_congr rfl fun n hn => ?_` and prove the remaining obligations. Rewrite `hn` using `[Multiset.mem_range]`. Simplify using `only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam, hWp, hWk]`. Rewrite using `[if_pos (by omega), if_neg (by omega)]`. Establish `hh : D.R.k - 1 + n + 1 - (D.R.k - 1) = n + 1` using `by omega`.

Rewrite using `[hh]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : (Multiset.range D.R.t).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + x) = (Multiset.range D.R.t).map ge`. Use `Multiset.map_congr rfl fun c hc => ?_` and prove the remaining obligations.

Rewrite `hc` using `[Multiset.mem_range]`. Simplify using `only [Function.comp, g, ge, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt]`. Rewrite using `[if_neg (by omega), if_pos (by omega)]`. Establish `: ((D.R.k - 1 + ((j : ℕ) + 1) + c + 1 : ℕ) : ℚ) - ((D.R.k + (j : ℕ) : ℕ) : ℚ) = c + 1`. Rewrite using `[show D.R.k - 1 + ((j : ℕ) + 1) + c + 1 = (D.R.k + (j : ℕ)) + (c + 1) by omega]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + x) = (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (gb ∘ fun x => (j : ℕ) + 1 + x)`.

Use `Multiset.map_congr rfl fun c hc => ?_` and prove the remaining obligations. Rewrite `hc` using `[Multiset.mem_range]`. Simplify using `only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt, hWj]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Establish `hh : (j : ℕ) + 1 + (D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + c + 1 - (D.R.k + (j : ℕ)) - D.R.t) = (j : ℕ) + 1 + c + 1` using `by omega`.

Rewrite using `[hh]`. Rewrite using `[e1, e2, e3, e4]`. Normalize the expressions using the abelian group laws.
-/
theorem infOf_lamLdef_eq_paramV : ∀ (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau),
    NG.infOf (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ).w = NG.paramV D.R (D.hc τ) j (1 / 2) := by
  intro D j τ
  have hk := D.R.m_add_three_le_k
  have hjm := j.2
  have hex : ∃ lam : DomWeight D.R.nV, Bridge.IsLamPrime (D := D) lam ((j : ℕ) + 1) τ := by
    have h0 := GlobalTheory.ForcedWeights.lamLForced D ((j : ℕ) + 1) (by omega) (by omega) τ
    have hr : (D.sp.V ((j : ℕ) + 1)).rank = D.R.nV := D.sp.V_rank _ (by omega) (by omega)
    exact transport hr ⟨_, h0⟩
  have hl : Bridge.IsLamPrime (D := D) (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
    unfold Bridge.lamLdef; rw [dif_pos hex]; exact hex.choose_spec
  set lam := Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ
  obtain ⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hw⟩ := hl
  have hWn : W.nV = D.R.nV := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r, Ranks.nV, Ranks.r, hWk, hWm, hWt]
  have hWp : W.p = D.R.k + (j : ℕ) := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.p, hWk, hWj]; omega
  let g : ℕ → ℚ := fun i => W.uSideTarget (i + 1) - 1 / 2

  have hL : NG.infOf lam.w = (Multiset.range D.R.nV).map (fun i => ((g i : ℚ) : ℂ)) := by
    unfold NG.infOf
    rw [← univ_map_eq_range]
    refine Multiset.map_congr rfl fun i _ => ?_
    have h1 := lamPrime_add_rho W (by omega) (by omega) (by omega) ((i : ℕ) + 1) (by omega)
      (by have := i.2; omega)
    have h2 := hw i
    have key : ((lam.w i : ℤ) : ℚ) + ((D.R.nV : ℚ) - 1) / 2 - ((i : ℕ) : ℚ) = g i := by
      simp only [g]
      rw [h2, ← h1]
      simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV, hWn]
      push_cast; ring
    have := congrArg (fun x : ℚ => (x : ℂ)) key
    push_cast at this ⊢
    exact this

  let gv : ℕ → ℚ := fun n => (W.v (n + 2) : ℚ) - 1 / 2
  let gb : ℕ → ℚ := fun n => -(W.b (n + 1) : ℚ) - 1 / 2
  let ge : ℕ → ℚ := fun c => -(W.e : ℚ) - 1 / 2 + ((D.R.t : ℚ) - 1 - 2 * c) / 2
  have hR : NG.paramV D.R (D.hc τ) j (1 / 2) =
      ((Multiset.range (D.R.k - 1)).map gv + (Multiset.range D.R.m).map gb
        + (Multiset.range D.R.t).map ge).map (fun x : ℚ => (x : ℂ)) := by
    simp only [Multiset.map_add, Multiset.map_map]
    unfold NG.paramV
    congr 1
    · congr 1
      · rw [← univ_map_eq_range]
        refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp, gv, hWv i]
        push_cast; ring
      · rw [← univ_map_eq_range]
        refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp, gb, hWb i]
        push_cast; ring
    · refine Multiset.map_congr rfl fun c _ => ?_
      have he : (D.hc τ).e j = (W.e : ℚ) := by
        rw [hWe]; congr 1; try (ext; simp)
      simp only [Function.comp, ge, he]
      push_cast; ring
  rw [hL, hR, show (fun i => ((g i : ℚ) : ℂ)) = (fun x : ℚ => (x : ℂ)) ∘ g from rfl, ← Multiset.map_map]
  congr 1

  have hsplit : D.R.nV = ((D.R.k - 1) + ((j : ℕ) + 1)) + D.R.t + (D.R.m - ((j : ℕ) + 1)) := by
    simp only [Ranks.nV, Ranks.r]; omega
  have hmsplit : D.R.m = ((j : ℕ) + 1) + (D.R.m - ((j : ℕ) + 1)) := by omega
  rw [hsplit, Multiset.range_add, Multiset.range_add, Multiset.range_add]
  conv_rhs => rw [hmsplit, Multiset.range_add]
  simp only [Multiset.map_add, Multiset.map_map]
  have e1 : (Multiset.range (D.R.k - 1)).map g = (Multiset.range (D.R.k - 1)).map gv := by
    refine Multiset.map_congr rfl fun n hn => ?_
    rw [Multiset.mem_range] at hn
    simp only [g, gv, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam, hWp, hWk]
    rw [if_pos (by omega), if_pos (by omega)]
  have e2 : (Multiset.range ((j : ℕ) + 1)).map (g ∘ fun x => D.R.k - 1 + x) =
      (Multiset.range ((j : ℕ) + 1)).map gb := by
    refine Multiset.map_congr rfl fun n hn => ?_
    rw [Multiset.mem_range] at hn
    simp only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      hWp, hWk]
    rw [if_pos (by omega), if_neg (by omega)]
    have hh : D.R.k - 1 + n + 1 - (D.R.k - 1) = n + 1 := by omega
    rw [hh]; push_cast; ring
  have e3 : (Multiset.range D.R.t).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + x) =
      (Multiset.range D.R.t).map ge := by
    refine Multiset.map_congr rfl fun c hc => ?_
    rw [Multiset.mem_range] at hc
    simp only [Function.comp, g, ge, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt]
    rw [if_neg (by omega), if_pos (by omega)]
    have : ((D.R.k - 1 + ((j : ℕ) + 1) + c + 1 : ℕ) : ℚ) - ((D.R.k + (j : ℕ) : ℕ) : ℚ) = c + 1 := by
      rw [show D.R.k - 1 + ((j : ℕ) + 1) + c + 1 = (D.R.k + (j : ℕ)) + (c + 1) by omega]
      push_cast; ring
    rw [this]; ring
  have e4 : (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + x) =
      (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (gb ∘ fun x => (j : ℕ) + 1 + x) := by
    refine Multiset.map_congr rfl fun c hc => ?_
    rw [Multiset.mem_range] at hc
    simp only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt, hWj]
    rw [if_neg (by omega), if_neg (by omega)]
    have hh : (j : ℕ) + 1 + (D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + c + 1 - (D.R.k + (j : ℕ)) - D.R.t) = (j : ℕ) + 1 + c + 1 := by omega
    rw [hh]
  rw [e1, e2, e3, e4]
  abel

end GlobalTheory.Mem.WtPar

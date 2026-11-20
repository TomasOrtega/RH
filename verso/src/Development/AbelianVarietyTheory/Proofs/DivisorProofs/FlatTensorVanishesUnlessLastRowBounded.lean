import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridMovedTensorBoundedSupportLocallyConstant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FunObj.FlatLast

open GlobalTheory.RootEx

section Step
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

open Classical in

/- English proof (translation)
Simplify using `only [stepPt, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem stepPt_add_apply (x₀ : Matrix n n' k) (e δ : StepVar n c n' → k) (a : n ⊕ Fin c) (b : n' ⊕ Fin (c + 1)) :
    stepPt x₀ (e + δ) a b =
      stepPt x₀ e a b + if h : Free (c / 2 + 1) (a, b) ∨ Kept (a, b) then δ ⟨(a, b), h⟩ else 0 := by
  simp only [stepPt, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> ring

end Step

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}

open Classical in

def shiftVar (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) : Vars G := fun j w =>
  if j = j₀ ∧ Sum.elim (fun a : Fin (topRank G (j + 1)) => (a : ℕ) = r) (fun _ => False) w.1.1 ∧
    w.1.2.isRight = true then t else 0

/- English proof (translation)
Unfold `shiftVar`. Use `split_ifs`. Conclude with `ht`. Simplify using the standard rewrite rules.
-/
theorem valuation_shiftVar_le (j₀ : Fin (G.m - 1)) (r : ℕ) {t s₀ : k} (ht : valuation k t ≤ valuation k s₀)
    (j : Fin (G.m - 1)) (w) : valuation k (shiftVar j₀ r t j w) ≤ valuation k s₀ := by
  unfold shiftVar
  split_ifs
  · exact ht
  · simp

/- English proof (translation)
Unfold `ch`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.add_apply, stepPt_add_apply]`. Apply the tactic sequence `split_ifs <;> simp [shiftVar]`.
-/
theorem ch_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) (j : Fin (G.m - 1)) :
    ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) = ch (stepPt (x j) (e j)) := by
  unfold ch
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, stepPt_add_apply]
  split_ifs <;> simp [shiftVar]

/- English proof (translation)
Unfold `rowVar`. Use `split_ifs with h`. Use `Finset.sum_congr rfl fun l _ => ?_ split_ifs` and prove the remaining obligations. Apply the tactic sequence `rw [Pi.add_apply, stepPt_add_apply] split_ifs <;> simp [shiftVar]`. Both sides reduce to the same expression.

Both sides reduce to the same expression.
-/
theorem rowVar_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) (j : ℕ) (s) :
    rowVar x (e + shiftVar j₀ r t) j s = rowVar x e j s := by
  unfold rowVar
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [Pi.add_apply, stepPt_add_apply]
      split_ifs <;> simp [shiftVar]
    · rfl
  · rfl

/- English proof (translation)
Unfold `colVar`. Rewrite using `[Pi.add_apply, stepPt_add_apply]`. Use `congr 1`. Distinguish the cases in `hj : j = j₀`. Substitute `hj` using the available equality.

Rewrite using `[dif_pos (Or.inr ⟨by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩, rfl⟩)]`. Simplify using `[shiftVar]`. Simplify using `[shiftVar, hj]`.
-/
theorem colVar_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m) (r : ℕ) (t : k)
    (j : Fin (G.m - 1)) (r' : Fin (topRank G (j + 1))) :
    colVar x (e + shiftVar j₀ r t) j r' = colVar x e j r' + if j = j₀ ∧ (r' : ℕ) = r then t else 0 := by
  unfold colVar
  rw [Pi.add_apply, stepPt_add_apply]
  congr 1
  by_cases hj : j = j₀
  · subst hj
    rw [dif_pos (Or.inr ⟨by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩, rfl⟩)]
    simp [shiftVar]
  · simp [shiftVar, hj]

/- English proof (translation)
Unfold `phase`. Establish `key : ∀ j : Fin (G.m - 1), (ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) + if Even (G.m - 2 - j) then ∑ r', rowVar x (e + shiftVar j₀ r t) (j + 1) r' * colVar x (e + shiftVar j₀ r t) j r' else 0) = (ch (stepPt (x j) (e j)) + if Even (G.m - 2 - j) then ∑ r', rowVar x e (j + 1) r' * …`. Introduce `j`. Rewrite using `[ch_shift]`. Simplify using `only [rowVar_shift, colVar_shift x e j₀ hj₀]`.

Distinguish the cases in `hj : j = j₀`. Substitute `hj` using the available equality. Establish `hev : Even (G.m - 2 - (j : ℕ))` using `by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩`. Rewrite using `[if_pos hev, if_pos hev, if_pos rfl]`. Simplify using `only [true_and, mul_add, Finset.sum_add_distrib, add_assoc]`.

Use `congr 2`. Repeatedly rewrite using `[Fin.val_inj, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules. Simplify using `[hj]`.

Rewrite using `[Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.
-/
theorem phase_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m)
    (r : Fin (topRank G ((j₀ : ℕ) + 1))) (t : k) :
    phase x (e + shiftVar j₀ r t) = phase x e + rowVar x e ((j₀ : ℕ) + 1) r * t := by
  unfold phase
  have key : ∀ j : Fin (G.m - 1), (ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) +
      if Even (G.m - 2 - j) then ∑ r', rowVar x (e + shiftVar j₀ r t) (j + 1) r' *
        colVar x (e + shiftVar j₀ r t) j r' else 0) =
      (ch (stepPt (x j) (e j)) + if Even (G.m - 2 - j) then ∑ r', rowVar x e (j + 1) r' * colVar x e j r' else 0) +
      if j = j₀ then rowVar x e ((j₀ : ℕ) + 1) r * t else 0 := by
    intro j
    rw [ch_shift]
    simp only [rowVar_shift, colVar_shift x e j₀ hj₀]
    by_cases hj : j = j₀
    · subst hj
      have hev : Even (G.m - 2 - (j : ℕ)) := by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩
      rw [if_pos hev, if_pos hev, if_pos rfl]
      simp only [true_and, mul_add, Finset.sum_add_distrib, add_assoc]
      congr 2
      simp_rw [Fin.val_inj, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    · simp [hj]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

variable (hs : 1 ≤ G.s)

/- English proof (translation)
Unfold `downMap`. Use `split_ifs with h1 h2`. Simplify using `only [reindex_apply, submatrix_apply, Pi.add_apply]`. Rewrite using `[stepPt_add_apply, add_sub_cancel_left]`. Use `split_ifs`.

Conclude with `hδ _ _`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem valuation_downMap_sub_le (x : ColArgs G) (e δ : Vars G) {s₀ : k}
    (hδ : ∀ j w, valuation k (δ j w) ≤ valuation k s₀) (j : ℕ) (a b) :
    valuation k (downMap hs x (e + δ) j a b - downMap hs x e j a b) ≤ valuation k s₀ := by
  classical
  unfold downMap
  split_ifs with h1 h2
  · simp only [reindex_apply, submatrix_apply, Pi.add_apply]
    rw [stepPt_add_apply, add_sub_cancel_left]
    split_ifs
    · exact hδ _ _
    · simp
  · simp
  · simp

/- English proof (translation)
Break down `b with ⟨i, j⟩ | ⟨i, j⟩` into its components or cases. Simplify using `only [fill, Pi.sub_apply] split_ifs with h`. Simplify using `only [Matrix.sub_apply, transpose_apply, submatrix_apply]`. Conclude with `valuation_downMap_sub_le hs x e δ hδ j _ _`. Simplify using the standard rewrite rules.

Simplify using `only [fill, Pi.sub_apply] split_ifs with h`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem valuation_fill_sub_le (x : ColArgs G) (y : RowArgs G) (e δ : Vars G) {s₀ : k}
    (hδ : ∀ j w, valuation k (δ j w) ≤ valuation k s₀) (b : Edge) (r s) :
    valuation k ((fill hs x y (e + δ) - fill hs x y e) b r s) ≤ valuation k s₀ := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [fill, Pi.sub_apply]
    split_ifs with h
    · simp only [Matrix.sub_apply, transpose_apply, submatrix_apply]
      exact valuation_downMap_sub_le hs x e δ hδ j _ _
    · simp
  · simp only [fill, Pi.sub_apply]
    split_ifs with h
    · simp
    · simp

end GlobalTheory.FunObj.FlatLast

namespace GlobalTheory.FunObj.FlatLast
open GlobalTheory.RootEx

/- English proof (translation)
Introduce `k _ _ _ _ _ _ G hs ψ ν _ ϖ e T keep g hm hϖ hψ hT`. Take `⟨n, -, hper⟩` from `GlobalTheory.MovedBound.moved_bounded_locConst G ϖ e T keep g hϖ hT`. Use `⟨n, fun x y hF => ?_⟩` and prove the remaining obligations. Set `j₀ : Fin (G.m - 1)` to `⟨G.m - 2, by omega⟩`. Establish `hj₀ : (j₀ : ℕ) + 2 = G.m` using `by simp only [j₀]; omega`.

It suffices to establish `key : ∀ r : Fin (topRank G ((j₀ : ℕ) + 1)), valuation k (x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) by`. Establish `h : G.m - 1 = (j₀ : ℕ) + 1` using `by omega`. Rewrite using `[h]`. Conclude with `key`. Introduce `r`.

Assume the negation of the conclusion as `hlt`. Establish `hu : x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r ∉ cball (1 * (ϖ ^ n)⁻¹)`. Simplify `hlt` using `[cball]`. Take `⟨t, ht, hne⟩` from `hψ.exists_ne_one (ϖ ^ n) hu`. Use `set u := x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r with hu_def`.

Establish `hrow : ∀ e' : Vars G, rowVar x e' ((j₀ : ℕ) + 1) r = u` using `fun e' => by`. Rewrite using `[rowVar, dif_neg (by omega)]`. Set `δ : Vars G` to `shiftVar j₀ r (-t)`. Establish `hδ : ∀ j w, valuation k (δ j w) ≤ valuation k ((ϖ ^ n : kˣ) : k)` using `valuation_shiftVar_le _ _ (by simpa [cball, Valuation.map_neg] using ht)`. Establish `hS : ∀ e' : Vars G, moved G keep g T (fill hs x y (e' + δ)) = moved G keep g T (fill hs x y e')` using `fun e' => by`.

Use `hper (fill hs x y e') (fill hs x y (e' + δ) - fill hs x y e') (fun b _ r s => valuation_fill_sub_le hs x y e' δ hδ b r s)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `hI : ∀ e' : Vars G, flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) = (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e'` using `fun e' => by`. Unfold `flatIntegrand`. Rewrite using `[hS, phase_shift x e' j₀ hj₀ r (-t), hrow, show -(phase x e' + u * -t) = -phase x e' + t * u by ring, AddChar.map_add_eq_mul, Circle.coe_mul]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨_, _⟩` from `GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Establish `hFeq : flatTensor hs ψ ν (moved G keep g T) x y = (ψ (t * u) : ℂ) * flatTensor hs ψ ν (moved G keep g T) x y`. Establish `: SigmaFinite ν` using `inferInstance`. Establish `: ν.IsAddRightInvariant` using `inferInstance`.

Establish `: (varsVol G ν).IsAddRightInvariant` using `by unfold varsVol; infer_instance`. Unfold `flatTensor`. Combine the equalities or inequalities in the displayed calculation. Establish `hne' : (ψ (t * u) : ℂ) ≠ 1` using `fun h => hne (Circle.ext (by simpa using h))`. Establish `: (1 - (ψ (t * u) : ℂ)) * flatTensor hs ψ ν (moved G keep g T) x y = 0`.

Rewrite using `[sub_mul, one_mul, ← hFeq, sub_self]`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `hne' (sub_eq_zero.1 h).symm`. Conclude with `hF h`.
-/
theorem flatTensor_lastRow_bounded : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), 2 ≤ G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → ∀ s, valuation k (x (G.m - 1) (topLast G (G.m - 1 + 1)) s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  intro k _ _ _ _ _ _ G hs ψ ν _ ϖ e T keep g hm hϖ hψ hT
  obtain ⟨n, -, hper⟩ := GlobalTheory.MovedBound.moved_bounded_locConst G ϖ e T keep g hϖ hT
  refine ⟨n, fun x y hF => ?_⟩
  let j₀ : Fin (G.m - 1) := ⟨G.m - 2, by omega⟩
  have hj₀ : (j₀ : ℕ) + 2 = G.m := by simp only [j₀]; omega
  suffices key : ∀ r : Fin (topRank G ((j₀ : ℕ) + 1)),
      valuation k (x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) by
    have h : G.m - 1 = (j₀ : ℕ) + 1 := by omega
    rw [h]
    exact key
  intro r
  by_contra hlt
  have hu : x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r ∉ cball (1 * (ϖ ^ n)⁻¹) := by
    simpa [cball] using hlt
  obtain ⟨t, ht, hne⟩ := hψ.exists_ne_one (ϖ ^ n) hu
  set u := x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r with hu_def
  have hrow : ∀ e' : Vars G, rowVar x e' ((j₀ : ℕ) + 1) r = u := fun e' => by
    rw [rowVar, dif_neg (by omega)]
  let δ : Vars G := shiftVar j₀ r (-t)
  have hδ : ∀ j w, valuation k (δ j w) ≤ valuation k ((ϖ ^ n : kˣ) : k) :=
    valuation_shiftVar_le _ _ (by simpa [cball, Valuation.map_neg] using ht)
  have hS : ∀ e' : Vars G, moved G keep g T (fill hs x y (e' + δ)) = moved G keep g T (fill hs x y e') := fun e' => by
    have := hper (fill hs x y e') (fill hs x y (e' + δ) - fill hs x y e')
      (fun b _ r s => valuation_fill_sub_le hs x y e' δ hδ b r s)
    rwa [add_sub_cancel] at this
  have hI : ∀ e' : Vars G, flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) =
      (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e' := fun e' => by
    unfold flatIntegrand
    rw [hS, phase_shift x e' j₀ hj₀ r (-t), hrow,
      show -(phase x e' + u * -t) = -phase x e' + t * u by ring, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hFeq : flatTensor hs ψ ν (moved G keep g T) x y =
      (ψ (t * u) : ℂ) * flatTensor hs ψ ν (moved G keep g T) x y := by
    have : SigmaFinite ν := inferInstance
    have : ν.IsAddRightInvariant := inferInstance
    have : (varsVol G ν).IsAddRightInvariant := by unfold varsVol; infer_instance
    unfold flatTensor
    calc ∫ e', flatIntegrand hs ψ (moved G keep g T) x y e' ∂(varsVol G ν)
        = ∫ e', flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) ∂(varsVol G ν) :=
          (integral_add_right_eq_self _ δ).symm
      _ = ∫ e', (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e' ∂(varsVol G ν) := by simp_rw [hI]
      _ = _ := integral_const_mul (ψ (t * u) : ℂ) _
  have hne' : (ψ (t * u) : ℂ) ≠ 1 := fun h => hne (Circle.ext (by simpa using h))
  have : (1 - (ψ (t * u) : ℂ)) * flatTensor hs ψ ν (moved G keep g T) x y = 0 := by
    rw [sub_mul, one_mul, ← hFeq, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact hne' (sub_eq_zero.1 h).symm
  · exact hF h

end GlobalTheory.FunObj.FlatLast

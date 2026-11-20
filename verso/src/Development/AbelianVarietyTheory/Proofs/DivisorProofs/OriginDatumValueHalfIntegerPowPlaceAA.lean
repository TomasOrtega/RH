import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetSetOfLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorMoveArgsOriginEqBoxIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingCharacterPhaseOriginValuationLeBoxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsOriginBoxValueExponentLeStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Flat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

open Classical in

/- English proof (translation)
Use `set P := ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) * apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod`. Establish `key : flatIntegrand hs ψ (moved G false g (Set.indicator {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 = (box G ϖ a a').indicator fun _ => P`. Use function extensionality and compare the values at `e`. Rewrite using `[flatIntegrand, moved_false, GlobalTheory.T.indicator_moveArgs_origin_eq_box_indicator G hs ϖ a a' g hg e]`. Distinguish the cases in `he : e ∈ box G ϖ a a'`.

Establish `h1` using `GlobalTheory.T.unfoldingCharacterPhase_origin_valuation_le_box G ϖ a a' e he`. Rewrite using `[Set.indicator_of_mem he, Set.indicator_of_mem he, hψ _ (by rwa [Valuation.map_neg])]`. Simplify using `only [Pi.one_apply, mul_one, Circle.coe_one, P]`. Rewrite using `[Set.indicator_of_notMem he, Set.indicator_of_notMem he]`. Simplify using the standard rewrite rules.

Rewrite using `[flatTensor, key, integral_indicator_const _ (measurableSet_box G ϖ a a'), Measure.real, vol_box G ν hν ϖ a a', Complex.real_smul, mul_comm]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem flatTensor_moved_box (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (hν : IsUnitVol ν)
    (ϖ : kˣ) (a a' : ℤ) (hψ : ∀ y : k, valuation k y ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) → ψ y = 1)
    (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) :
    flatTensor hs ψ ν (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
    ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod *
      ∏ j, ∏ v, ((nabs k (ϖ ^ boxExp G a a' j v) : ℝ) : ℂ) := by
  set P := ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod
  have key : flatIntegrand hs ψ (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
      (box G ϖ a a').indicator fun _ => P := by
    funext e
    rw [flatIntegrand, moved_false, GlobalTheory.T.indicator_moveArgs_origin_eq_box_indicator G hs ϖ a a' g hg e]
    by_cases he : e ∈ box G ϖ a a'
    · have h1 := GlobalTheory.T.unfoldingCharacterPhase_origin_valuation_le_box G ϖ a a' e he
      rw [Set.indicator_of_mem he, Set.indicator_of_mem he, hψ _ (by rwa [Valuation.map_neg])]
      simp only [Pi.one_apply, mul_one, Circle.coe_one, P]
    · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he]
      simp
  rw [flatTensor, key, integral_indicator_const _ (measurableSet_box G ϖ a a'), Measure.real, vol_box G ν hν ϖ a a',
    Complex.real_smul, mul_comm]
  push_cast
  rfl

end Flat
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Expo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Establish `hn : ∀ x : kˣ, ((nabs k x : ℝ) : ℂ) = apow x 1` using `fun x => by simp [apow]`. Rewrite using `[flatTensor_moved_box G hs ψ ν hν ϖ a a' hψ g hg]`. Repeatedly rewrite using `[gdet_eq ϖ a a' g hg hg', ← _root_.zpow_neg, apow_zpow, ← apow_add, hn, apow_zpow, prod_apow_finset, prod_apow_list, ← apow_add]`. Use `congr 1`. Establish `hl : ∀ l : List Edge, (l.map fun b => ((-vtxDet G a a' b.src : ℤ) : ℂ) * ((G.rank b.tgt : ℂ) / 2) + ((-vtxDet G a a' b.tgt : ℤ) : ℂ) * (-(G.rank b.src : ℂ) / 2)).sum = -(((l.map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum : ℤ) : ℂ) / 2`.

Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons b l ih => simp only [List.map_cons, List.sum_cons, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hl, expo]`. Use `push_cast`. Simplify using `only [mul_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flatTensor_moved_box_apow (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (hν : IsUnitVol ν)
    (ϖ : kˣ) (a a' : ℤ) (hψ : ∀ y : k, valuation k y ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) → ψ y = 1)
    (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) (hg' : ∀ i j, i ≠ G.m → g (i, j) = 1) :
    flatTensor hs ψ ν (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
    apow ϖ (-(expo G a a' : ℂ) / 2) := by
  classical
  have hn : ∀ x : kˣ, ((nabs k x : ℝ) : ℂ) = apow x 1 := fun x => by simp [apow]
  rw [flatTensor_moved_box G hs ψ ν hν ϖ a a' hψ g hg]
  simp_rw [gdet_eq ϖ a a' g hg hg', ← _root_.zpow_neg, apow_zpow, ← apow_add, hn, apow_zpow, prod_apow_finset,
    prod_apow_list, ← apow_add]
  congr 1
  have hl : ∀ l : List Edge, (l.map fun b => ((-vtxDet G a a' b.src : ℤ) : ℂ) * ((G.rank b.tgt : ℂ) / 2) +
      ((-vtxDet G a a' b.tgt : ℤ) : ℂ) * (-(G.rank b.src : ℂ) / 2)).sum =
      -(((l.map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum : ℤ) : ℂ) / 2 := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring
  rw [hl, expo]
  push_cast
  simp only [mul_one]
  ring

end Expo
end GlobalTheory.OriginBox
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Generic
variable {k : Type} [Field k]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[colDiag, diagGL_val, Units.val_one, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `h` using `topRank_add hs j`.

Establish `hx` using `x.2`. Rewrite using `[vtxExp, if_neg (by omega), zpow_zero, Units.val_one]`.
-/
theorem colDiag_eq_one (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) {j : ℕ} (hj : G.m - 1 ≤ j) :
    colDiag G ϖ a a' j = 1 := by
  refine Units.ext ?_
  rw [colDiag, diagGL_val, Units.val_one, ← diagonal_one]
  congr 1
  funext x
  have h := topRank_add hs j
  have hx := x.2
  rw [vtxExp, if_neg (by omega), zpow_zero, Units.val_one]

end Generic

variable {D : D7}

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[aaElt, colDiag, diagGL_val, diagGL_val]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `h` using `topRank_add (G := bareGrid w) one_le_sLen j`.

Establish `hx` using `x.2`. Simplify using `only [vtxExp]`. Use `split_ifs with h1`. Simplify using `only [genAt, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_neg, ← _root_.zpow_add, Units.val_zpow_eq_zpow_val]`. Use `congr 1`.

Establish `: x.val - topRank (bareGrid w) j < D.R.m - 1 - j`. Express the relevant statement in the definitionally equal form `topRank (bareGrid w) j + D.R.m = (bareGrid w).rank ((bareGrid w).m, j) + j + 1 at h`. Express the relevant statement in the definitionally equal form `(x : ℕ) < (bareGrid w).rank ((bareGrid w).m, j) at hx`. Use linear arithmetic over natural numbers and integers. Express the relevant statement in the definitionally equal form `_ = _ * (((D.R.m - 1 - j : ℕ) : ℤ) - _) - _`.

Move the coercions through the operations in `[Nat.sub_sub]`. Rewrite using `[show D.R.m - (1 + j + (x.val - topRank (bareGrid w) j)) = D.R.m - (1 + j) - (x.val - topRank (bareGrid w) j) by omega, Nat.cast_sub (by omega)]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem aaElt_eq (w : Pl D.host.E) (j : ℕ) :
    aaElt w j = colDiag (bareGrid w) (unifAt w) (FractionalIdeal.count D.host.E w D.host.AA)
      (FractionalIdeal.count D.host.E w D.host.AAbar) j := by
  refine Units.ext ?_
  rw [aaElt, colDiag, diagGL_val, diagGL_val]
  congr 1
  funext x
  have h := topRank_add (G := bareGrid w) one_le_sLen j
  have hx := x.2
  simp only [vtxExp]
  split_ifs with h1
  · simp only [genAt, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_neg, ← _root_.zpow_add, Units.val_zpow_eq_zpow_val]
    congr 1
    have : x.val - topRank (bareGrid w) j < D.R.m - 1 - j := by
      change topRank (bareGrid w) j + D.R.m = (bareGrid w).rank ((bareGrid w).m, j) + j + 1 at h
      change (x : ℕ) < (bareGrid w).rank ((bareGrid w).m, j) at hx
      omega
    change _ = _ * (((D.R.m - 1 - j : ℕ) : ℤ) - _) - _
    push_cast [Nat.sub_sub]
    rw [show D.R.m - (1 + j + (x.val - topRank (bareGrid w) j)) = D.R.m - (1 + j) - (x.val - topRank (bareGrid w) j) by omega,
      Nat.cast_sub (by omega)]
    ring
  · simp

/- English proof (translation)
Unfold `Reps.elt`. Rewrite using `[onColumn_apply]`. Consider the cases of `j with`. Consider the case `zero => exact aaElt_eq w 0`. Consider the case `succ i`.

Simplify using `only [Reps.through]`. Use `split_ifs with h`. Conclude with `aaElt_eq w (i + 1)`. Conclude with `(colDiag_eq_one _ one_le_sLen _ _ _ (by omega)).symm`.
-/
theorem aaElt_elt_col (w : Pl D.host.E) (j : ℕ) :
    (Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)).elt
      (fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))) ((bareGrid w).m, j) =
    colDiag (bareGrid w) (unifAt w) (FractionalIdeal.count D.host.E w D.host.AA)
      (FractionalIdeal.count D.host.E w D.host.AAbar) j := by
  unfold Reps.elt
  rw [onColumn_apply]
  cases j with
  | zero => exact aaElt_eq w 0
  | succ i =>
    simp only [Reps.through]
    split_ifs with h
    · exact aaElt_eq w (i + 1)
    · exact (colDiag_eq_one _ one_le_sLen _ _ _ (by omega)).symm

/- English proof (translation)
Simplify using `[Reps.elt, onColumn, hi]`.
-/
theorem aaElt_elt_off (w : Pl D.host.E) (i j : ℕ) (hi : i ≠ (bareGrid w).m) :
    (Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)).elt
      (fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))) (i, j) = 1 := by
  simp [Reps.elt, onColumn, hi]

/- English proof (translation)
Establish `h1` using `Nat.mul_le_mul_right D.R.t hj`. Establish `h2` using `Nat.mul_le_mul_right (sLen D) hi`. Establish `hr : D.R.r ≤ D.R.k + D.R.m`. Establish `: D.R.r = D.R.k + D.R.m - 1` using `rfl`. Use linear arithmetic over natural numbers and integers.

Express the relevant statement in the definitionally equal form `D.R.r + j * D.R.t + i * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)`. Express the relevant statement in the definitionally equal form `i ≤ D.R.m at hi`. Express the relevant statement in the definitionally equal form `j ≤ D.R.m at hj`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem rank_le_bigN (w : Pl D.host.E) (i j : ℕ) (hi : i ≤ (bareGrid w).m) (hj : j ≤ (bareGrid w).m) :
    (bareGrid w).rank (i, j) ≤ bigN D := by
  have h1 := Nat.mul_le_mul_right D.R.t hj
  have h2 := Nat.mul_le_mul_right (sLen D) hi
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + i * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
  change i ≤ D.R.m at hi
  change j ≤ D.R.m at hj
  nlinarith

/- English proof (translation)
Introduce `D T L sc G W w hψ`. Establish `hψ' : ∀ y : Kw w, valuation (Kw w) y ≤ valuation (Kw w) (((unifAt w) ^ (FractionalIdeal.count D.host.E w D.host.AA + FractionalIdeal.count D.host.E w D.host.AAbar) : (Kw w)ˣ) : Kw w) → psiAt W w y = 1` using `fun y hy => hψ y (by rwa [genAt, genAt, ← _root_.zpow_add])`. Establish `key` using `flatTensor_moved_box_apow (bareGrid w) one_le_sLen (psiAt W w) (unitVol w) (isUnitVol_unitVol w) (unifAt w) _ _ hψ' _ (aaElt_elt_col w) (aaElt_elt_off w)`. Use `⟨expo (bareGrid w) (FractionalIdeal.count D.host.E w D.host.AA) (FractionalIdeal.count D.host.E w D.host.AAbar), ?_, GlobalTheory.T.abs_originBoxValueExponent_le (bareGrid w) one_le_sLen _ _ (bigN D) (rank_le_bigN w)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `flatTensor _ _ _ _ 0 0 = _`.

Rewrite `*` using `[aaVac, genAt]`. Rewrite using `[key, IsUnif.apow_eq (isUnif_unifAt w)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aaTerm_datum_origin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E), (∀ a : Kw w, valuation (Kw w) a ≤ valuation (Kw w) ((genAt w D.host.AA * genAt w D.host.AAbar : (Kw w)ˣ) : Kw w) → psiAt W w a = 1) → ∃ n : ℤ, (aaTerm W w).datum 0 0 = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧ |n| ≤ 8 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 * (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  intro D T L sc G W w hψ
  have hψ' : ∀ y : Kw w, valuation (Kw w) y ≤ valuation (Kw w) (((unifAt w) ^ (FractionalIdeal.count D.host.E w D.host.AA +
      FractionalIdeal.count D.host.E w D.host.AAbar) : (Kw w)ˣ) : Kw w) → psiAt W w y = 1 := fun y hy =>
    hψ y (by rwa [genAt, genAt, ← _root_.zpow_add])
  have key := flatTensor_moved_box_apow (bareGrid w) one_le_sLen (psiAt W w) (unitVol w) (isUnitVol_unitVol w) (unifAt w)
    _ _ hψ' _ (aaElt_elt_col w) (aaElt_elt_off w)
  refine ⟨expo (bareGrid w) (FractionalIdeal.count D.host.E w D.host.AA) (FractionalIdeal.count D.host.E w D.host.AAbar),
    ?_, GlobalTheory.T.abs_originBoxValueExponent_le (bareGrid w) one_le_sLen _ _ (bigN D) (rank_le_bigN w)⟩
  change flatTensor _ _ _ _ 0 0 = _
  rw [aaVac, genAt] at *
  rw [key, IsUnif.apow_eq (isUnif_unifAt w)]
  congr 1
  ring

end GlobalTheory.OriginBox

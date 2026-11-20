import Formalism.LocalToGlobal.Divisibility.RecBridgeNum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookProductPosLogEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FloorCastOfInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowMainTerm

/- English proof (translation)
Unfold `Formalism.BasicNotions.DV.logHook`. Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[h i (Finset.mem_range.mp hi)]`. Use `Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations.

Establish `hi'` using `Finset.mem_range.mp hi`. Establish `hl'` using `(Finset.mem_Ioo.mp hl).2`. Rewrite using `[h i hi', h l hl']`.
-/
theorem logHook_congr (n : ℕ) (a b : ℕ → ℝ) (h : ∀ i < n, a i = b i) :
    Formalism.BasicNotions.DV.logHook n a = Formalism.BasicNotions.DV.logHook n b := by
  unfold Formalism.BasicNotions.DV.logHook
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [h i (Finset.mem_range.mp hi)]
  · refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => ?_
    have hi' := Finset.mem_range.mp hi
    have hl' := (Finset.mem_Ioo.mp hl).2
    rw [h i hi', h l hl']

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW`. Rewrite using `[GlobalTheory.RecGaps.sig_Wc]`.
-/
theorem pW_eq (D : D7) (j : Fin D.R.m) (ρ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ = (D.R.sigW ((j : ℕ) + 1)).1 := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW
  rw [GlobalTheory.RecGaps.sig_Wc]

/- English proof (translation)
Simplify using `[Formalism.BasicNotions.Ranks.sigW]`.
-/
theorem sigW_fst (D : D7) (j : Fin D.R.m) : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ) := by
  simp [Formalism.BasicNotions.Ranks.sigW]

/- English proof (translation)
Establish `h1 : 1 ≤ (j : ℕ) + 1` using `Nat.le_add_left 1 _`. Establish `h2 : (j : ℕ) + 1 ≤ D.R.m` using `j.isLt`. Rewrite using `[pW_eq, sigW_fst]`. Establish `key : ∀ n < D.R.k + (j : ℕ), ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ n : ℕ) : ℝ) = Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ n`. Introduce `n hn`.

Use `GlobalTheory.RecordWeightVec.aPl_eq_aPlusQ D j ρ n hn` as an intermediate fact. Unfold `Formalism.BasicNotions.DV.aPlus`. Rewrite using `[← this]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `rs` using `(GlobalTheory.BlockRows.rows_sizes D ((j : ℕ) + 1) h1 h2 ρ).1`. Establish `hanti : ∀ (x y : ℕ), x ≤ y → y < D.R.k + (j : ℕ) → Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y ≤ Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x`. Introduce `x y hxy hy`. Establish `hx : x < D.R.k + (j : ℕ)` using `lt_of_le_of_lt hxy hy`. Establish `e : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ)` using `sigW_fst D j`.

Establish `hy' : y < (D.R.sigW ((j : ℕ) + 1)).1` using `e ▸ hy`. Establish `hx' : x < (D.R.sigW ((j : ℕ) + 1)).1` using `e ▸ hx`. Establish `ha` using `rs.1 (show (⟨x, hx'⟩ : Fin _) ≤ ⟨y, hy'⟩ from hxy)`. Establish `ex` using `rs.2.2 ⟨x, hx'⟩`. Establish `ey` using `rs.2.2 ⟨y, hy'⟩`.

Establish `r : ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y : ℕ) : ℝ) ≤ ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x : ℕ) : ℝ)`. Rewrite using `[key y hy, key x hx]`. Simplify using `only at ex ey`. Rewrite using `[← ex, ← ey]`. Conclude with `ha` after adjusting the coercions.

Conclude with `r` after adjusting the coercions. Rewrite using `[(GlobalTheory.HookDiagram.hookOf_pos_log _ _ hanti).2]`. Conclude with `logHook_congr _ _ _ key`.
-/
theorem hook_term (D : D7) (j : Fin D.R.m) (ρ : D.what₂.Tau) :
    Real.log ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ)
        (Formalism.IndefR.Links.aPl D j (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ) ρ) : ℕ) : ℝ)
      = Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ) := by
  have h1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
  have h2 : (j : ℕ) + 1 ≤ D.R.m := j.isLt
  rw [pW_eq, sigW_fst]
  have key : ∀ n < D.R.k + (j : ℕ),
      ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ n : ℕ) : ℝ) = Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ n := by
    intro n hn
    have := GlobalTheory.RecordWeightVec.aPl_eq_aPlusQ D j ρ n hn
    unfold Formalism.BasicNotions.DV.aPlus
    rw [← this]
    push_cast
    rfl
  have rs := (GlobalTheory.BlockRows.rows_sizes D ((j : ℕ) + 1) h1 h2 ρ).1
  have hanti : ∀ (x y : ℕ), x ≤ y → y < D.R.k + (j : ℕ) →
      Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y ≤ Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x := by
    intro x y hxy hy
    have hx : x < D.R.k + (j : ℕ) := lt_of_le_of_lt hxy hy
    have e : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ) := sigW_fst D j
    have hy' : y < (D.R.sigW ((j : ℕ) + 1)).1 := e ▸ hy
    have hx' : x < (D.R.sigW ((j : ℕ) + 1)).1 := e ▸ hx
    have ha := rs.1 (show (⟨x, hx'⟩ : Fin _) ≤ ⟨y, hy'⟩ from hxy)
    have ex := rs.2.2 ⟨x, hx'⟩
    have ey := rs.2.2 ⟨y, hy'⟩
    have r : ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y : ℕ) : ℝ)
        ≤ ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x : ℕ) : ℝ) := by
      rw [key y hy, key x hx]
      simp only at ex ey
      rw [← ex, ← ey]
      exact_mod_cast ha
    exact_mod_cast r
  rw [(GlobalTheory.HookDiagram.hookOf_pos_log _ _ hanti).2]
  exact logHook_congr _ _ _ key

end GlobalTheory.LowMainTerm

namespace GlobalTheory.LowMainTerm

/- English proof (translation)
Establish `h1 : 1 ≤ (j : ℕ) + 1` using `Nat.le_add_left 1 _`. Establish `h2 : (j : ℕ) + 1 ≤ D.R.m` using `j.isLt`. Establish `e1 : (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) = ∑ z : Bool × G.HH D, Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) (tauPl D z))` using `Finset.sum_congr rfl fun z _ => Formalism.L2.DIV.NumTieH.logHook_eq D L Del h0 h1 h2 z`. Rewrite using `[e1, Function.Bijective.sum_comp (tauPl_bijective D) (fun τ => Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) τ))]`. Unfold `GlobalTheory.LiftLower.hookPlus`.

Conclude with `(Finset.sum_congr rfl fun ρ _ => hook_term D j ρ).symm`.
-/
theorem sum_logHook_eq (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (j : Fin D.R.m) :
    (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) = GlobalTheory.LiftLower.hookPlus D j := by
  have h1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
  have h2 : (j : ℕ) + 1 ≤ D.R.m := j.isLt
  have e1 : (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ)
      = ∑ z : Bool × G.HH D, Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1
          (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) (tauPl D z)) :=
    Finset.sum_congr rfl fun z _ => Formalism.L2.DIV.NumTieH.logHook_eq D L Del h0 h1 h2 z
  rw [e1, Function.Bijective.sum_comp (tauPl_bijective D)
    (fun τ => Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) τ))]
  unfold GlobalTheory.LiftLower.hookPlus
  exact (Finset.sum_congr rfl fun ρ _ => hook_term D j ρ).symm

/- English proof (translation)
Introduce `D L Del h0 Csz j hC hS`. Rewrite using `[sum_logHook_eq]`. Establish `hLp : (ofRecord D L Del h0).Lp = GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b`. Rewrite using `[Formalism.L2.DIV.NumTieH.Lp_eq]`. Both sides reduce to the same expression.

Establish `hpos : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b`. Use `(GlobalTheory.AdelicScalar.SizeBounds.sizes D j L.sc.b hS).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hLp]`. Unfold `GlobalTheory.BigOn.lowB`.

Establish `hX : 0 ≤ (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem main_le_lowB : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (Csz : ℝ) (j : Fin D.R.m), 8 ≤ Csz → Sizes D j L.sc.b → (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) - Csz * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp) ≤ lowB D j L.sc.b := by
  intro D L Del h0 Csz j hC hS
  rw [sum_logHook_eq]
  have hLp : (ofRecord D L Del h0).Lp = GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by
    rw [Formalism.L2.DIV.NumTieH.Lp_eq]; rfl
  have hpos : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by
    have := (GlobalTheory.AdelicScalar.SizeBounds.sizes D j L.sc.b hS).1
    linarith
  rw [hLp]
  unfold GlobalTheory.BigOn.lowB
  have hX : 0 ≤ (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by positivity
  nlinarith

end GlobalTheory.LowMainTerm

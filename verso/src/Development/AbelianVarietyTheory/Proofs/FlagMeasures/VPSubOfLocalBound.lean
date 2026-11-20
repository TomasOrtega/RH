import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMultilinearMapOfInnerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtOrbitTens
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepSpacePropsOfDiff

open Formalism.MainNotions.S NumberField GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.StepTens

/- English proof (translation)
Take `⟨m, hm, -⟩` from `GlobalTheory.rowsAut_tens_continuousMultilinear B`. Establish `hloc` using `(GlobalTheory.StepLoc.stepSpace_props_of_diff B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (hU v) (hd v) P).2.1 X.1 X.2 (u v) (hu v)`. Establish `h1 : ∀ v, B.σ v 1 = 1` using `fun v => (hU v).1.1`. Use `set y := GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X.1 (u v) with hy`. Establish `hder : ∀ v', HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (atPlace B v X v').1 (u v')) ((Pi.single v y : ∀ v, B.H v) v') 0`.

Introduce `v'`. Distinguish the cases in `h : v' = v`. Substitute `h` using the available equality. Simplify `hloc.1` using `[atPlace]`. Establish `h0 : atPlace B v X v' = 0`.

Simplify using `[atPlace, h]`. Rewrite using `[h0, Pi.single_eq_of_ne h]`. Establish `: GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (0 : gLie (B.I.ε v')).1 (u v') = fun _ => u v'`. Use function extensionality and compare the values at `t`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, h1]`.

Rewrite using `[this]`. Conclude with `hasDerivAt_const _ _`. Establish `hT` using `(GlobalTheory.TensDer.hasDerivAt_orbit_tens B (atPlace B v X) u _ hder h1).deriv`. Use `⟨Function.update u v y, ?_, ?_⟩` and prove the remaining obligations. Introduce `v'`.

Distinguish the cases in `h : v' = v`. Substitute `h` using the available equality. Simplify using `using hloc.2`. Rewrite using `[Function.update_of_ne h]`. Conclude with `GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_mono _ _ _ (Nat.le_succ P) (hu v')`.

Unfold `dAct`. Rewrite using `[hT, Finset.sum_eq_single v]`. Simplify using `only [Pi.single_eq_same]`. Introduce `v' _ h`. Rewrite using `[Pi.single_eq_of_ne h, ← hm]`.

Conclude with `m.map_coord_zero v' (by simp)`. Simplify using the standard rewrite rules.
-/
theorem dAct_tens_of_diff (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w)
    (P : ℕ) (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)) (u : ∀ v, B.H v)
    (hu : ∀ v, u v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) :
    ∃ u' : ∀ v, B.H v, (∀ v, u' v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) (P + 1)) ∧
      dAct B (atPlace B v X) (B.tens u) = B.tens u' := by
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  have hloc := (GlobalTheory.StepLoc.stepSpace_props_of_diff B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (hU v)
    (hd v) P).2.1 X.1 X.2 (u v) (hu v)
  have h1 : ∀ v, B.σ v 1 = 1 := fun v => (hU v).1.1
  set y := GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X.1 (u v) with hy
  have hder : ∀ v', HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (atPlace B v X v').1 (u v'))
      ((Pi.single v y : ∀ v, B.H v) v') 0 := by
    intro v'
    by_cases h : v' = v
    · subst h
      simpa [atPlace] using hloc.1
    · have h0 : atPlace B v X v' = 0 := by
        simp [atPlace, h]
      rw [h0, Pi.single_eq_of_ne h]
      have : GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (0 : gLie (B.I.ε v')).1 (u v') = fun _ => u v' := by
        funext t
        simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, h1]
      rw [this]
      exact hasDerivAt_const _ _
  have hT := (GlobalTheory.TensDer.hasDerivAt_orbit_tens B (atPlace B v X) u _ hder h1).deriv
  refine ⟨Function.update u v y, ?_, ?_⟩
  · intro v'
    by_cases h : v' = v
    · subst h
      simpa using hloc.2
    · rw [Function.update_of_ne h]
      exact GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_mono _ _ _ (Nat.le_succ P) (hu v')
  · unfold dAct
    rw [hT, Finset.sum_eq_single v]
    · simp only [Pi.single_eq_same]
    · intro v' _ h
      rw [Pi.single_eq_of_ne h, ← hm]
      exact m.map_coord_zero v' (by simp)
    · simp

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Use `⟨u, fun v => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[List.length_nil, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_zero]`. Conclude with `hu v`.

Consider the case `cons X l ih`. Take `⟨u', h1, h2⟩` from `ih`. Take `⟨u'', h3, h4⟩` from `dAct_tens_of_diff B hU hd l.length X.1 X.2 u' h1`. Use `⟨u'', h3, ?_⟩` and prove the remaining obligations. Rewrite using `[← h4, ← h2]`.

Both sides reduce to the same expression.
-/
theorem wordAct_tens_of_diff (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w)
    (u : ∀ v, B.H v) (hu : ∀ v, u v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v))
    (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) :
    ∃ u' : ∀ v, B.H v, (∀ v, u' v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) l.length) ∧
      wordAct B l (B.tens u) = B.tens u' := by
  induction l with
  | nil =>
    refine ⟨u, fun v => ?_, rfl⟩
    rw [List.length_nil, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_zero]
    exact hu v
  | cons X l ih =>
    obtain ⟨u', h1, h2⟩ := ih
    obtain ⟨u'', h3, h4⟩ := dAct_tens_of_diff B hU hd l.length X.1 X.2 u' h1
    refine ⟨u'', h3, ?_⟩
    rw [← h4, ← h2]
    rfl

/- English proof (translation)
Introduce `w hw`. Take `⟨m, hm, -⟩` from `GlobalTheory.rowsAut_tens_continuousMultilinear B`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, u, hl, hu, rfl⟩` from `hx`.

Take `⟨u', h1, h2⟩` from `wordAct_tens_of_diff B hU hd u hu l`. Conclude with `⟨1, fun _ => u', fun _ v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_mono _ _ _ hl (h1 v), by simp [h2]⟩`. Consider the case `zero => exact ⟨0, fun i => i.elim0, fun i => i.elim0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨k, u, hu, rfl⟩` from `hx`.

Take `⟨k', u', hu', rfl⟩` from `hy`. Use `⟨k + k', Fin.append u u', ?_, ?_⟩` and prove the remaining obligations. Introduce `l`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) l` and prove the remaining obligations. Simplify using `using hu i`.

Simplify using `using hu' i`. Simplify using `[Fin.sum_univ_add]`. Consider the case `smul c x _ hx`. Take `⟨k, u, hu, rfl⟩` from `hx`. Take `⟨v₀⟩ : Nonempty (InfinitePlace B.I.F)` from `inferInstance`.

Use `⟨k, fun l => Function.update (u l) v₀ (c • u l v₀), ?_, ?_⟩` and prove the remaining obligations. Introduce `l v`. Distinguish the cases in `h : v = v₀`. Substitute `h` using the available equality. Simplify using `using Submodule.smul_mem _ c (hu l v)`.

Simplify `hu l v` using `[Function.update_of_ne h]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← hm, ← hm, m.map_update_smul, Function.update_eq_self]`.
-/
theorem stepSpan_le_of_differentiable (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w) (P : ℕ) :
    ∀ w ∈ VP B P, ∃ (k : ℕ) (u : Fin k → ∀ v, B.H v),
      (∀ l v, u l v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) ∧ w = ∑ l, B.tens (u l) := by
  classical
  intro w hw
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, u, hl, hu, rfl⟩ := hx
    obtain ⟨u', h1, h2⟩ := wordAct_tens_of_diff B hU hd u hu l
    exact ⟨1, fun _ => u', fun _ v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_mono _ _ _ hl (h1 v), by simp [h2]⟩
  | zero => exact ⟨0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, u, hu, rfl⟩ := hx
    obtain ⟨k', u', hu', rfl⟩ := hy
    refine ⟨k + k', Fin.append u u', ?_, ?_⟩
    · intro l
      refine Fin.addCases (fun i => ?_) (fun i => ?_) l
      · simpa using hu i
      · simpa using hu' i
    · simp [Fin.sum_univ_add]
  | smul c x _ hx =>
    obtain ⟨k, u, hu, rfl⟩ := hx
    obtain ⟨v₀⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    refine ⟨k, fun l => Function.update (u l) v₀ (c • u l v₀), ?_, ?_⟩
    · intro l v
      by_cases h : v = v₀
      · subst h
        simpa using Submodule.smul_mem _ c (hu l v)
      · simpa [Function.update_of_ne h] using hu l v
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← hm, ← hm, m.map_update_smul, Function.update_eq_self]

end GlobalTheory.StepTens

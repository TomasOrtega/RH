import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMultilinearMapOfInnerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtOrbitTens
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepSpacePropsOfDiff

open Formalism.MainNotions.S NumberField GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.StepTens

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
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

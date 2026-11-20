import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PSSeg
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PSLang
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PS_conj
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PUnit
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PCentred
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNegStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIffStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Fin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `⟨Representation.Equiv.refl _⟩`.
-/
theorem congrProd' {h N : ℕ} {x y : Fin h → IrrGL k} (e : x = y) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) :
    Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

/- English proof (translation)
Establish `hA : GlobalTheory.Published.IrreducibleAdmissibleGL` using `PositivityTheory.RgGu.NR.ConjDual.irrAdm'`. Establish `hδu : ∀ j, IsUnitarisable (δ j).rep` using `fun j => PositivityTheory.Gud.Pf.unitarisable_of_unitCC (hL j) (hU j)`. Establish `hc : ∀ j, PositivityTheory.UdReth2.IsCentred (Δ j)` using `fun j => PositivityTheory.Gud.Pf.isCentred_of_unitCC (hL j) (hU j)`. Take `⟨hd1, ⟨e1⟩⟩` from `PositivityTheory.Gud.Symm.Pf.conj_side hA δ s hδu hd hi hu`. Take `⟨hd2, ⟨e2⟩⟩` from `GlobalTheory.T.contragredient_product_irreducible hA (fun j => (δ j).nu (s j)) hd`.

Establish `hfun : (fun j => Zc.dualCl ((δ j).nu (s j))) = fun j => (Zc.dualCl (δ j)).nu (((fun j => -s j) j : ℝ) : ℂ)`. Use function extensionality and compare the values at `fun j => by rw [GlobalTheory.T.dual_class_twist_neg hA]; push_cast; rfl`. Establish `hd3 : ∑ j, ((Zc.dualCl (δ j)).nu (((fun j => -s j) j : ℝ) : ℂ)).1 = N`. Rewrite using `[← hd2]`. Conclude with `congrArg (fun f : Fin h → IrrGL k => ∑ j, (f j).1) hfun.symm`.

Take `⟨e3⟩` from `congrProd' hfun hd2 hd3`. Establish `E` using `e1.symm.trans (e2.trans e3)`. Establish `key : ∀ (t : Fin h → ℝ), (∀ j, |t j| < 1 / 2) → ∀ i j, ¬ ((Zc.segDual (Δ i)).nu (t i : ℂ)).Precedes ((Zc.segDual (Δ j)).nu (t j : ℂ))`. Introduce `t ht i j hP`. Establish `r : ∀ a, (Zc.segDual (Δ a)).nu (t a : ℂ) = Zc.segDual ((Δ a).nu ((-t a : ℝ) : ℂ))` using `fun a => by`.

Rewrite using `[PositivityTheory.Gud.Symm.Pf.segDual_nu hA]`. Use `push_cast`. Rewrite using `[neg_neg]`. Rewrite `hP` using `[r, r, GlobalTheory.T.segment_dual_precedes_iff hA]`. Use `PositivityTheory.UdReth2.add_one_le_of_precedes _ _ (hc j) (hc i) _ _ hP` as an intermediate fact.

Establish `h1` using `ht i`. Establish `h2` using `ht j`. Rewrite `h1`, `h2` using `[abs_lt]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM` using `PositivityTheory.Gud.Symm.Pf.multiset_of_equiv (fun j => Zc.segDual (Δ j)) (fun j => Zc.dualCl (δ j)) s (fun j => -s j) (fun j => PositivityTheory.Gud.Symm.Pf.isLSeg_dualCl hA (hL j)) (key s hs) (key (fun j => -s j) (fun j => by simpa using hs j)) hd1 hd3 ⟨E⟩`.

Establish `hM2` using `congrArg (Multiset.map Zc.segDual) hM`. Simplify using `only [Multiset.map_map, Function.comp_def] at hM2`. Establish `r2 : ∀ (a : Fin h) (t : ℝ), Zc.segDual ((Zc.segDual (Δ a)).nu (t : ℂ)) = (Δ a).nu ((-t : ℝ) : ℂ)` using `fun a t => by`. Rewrite using `[PositivityTheory.Gud.Symm.Pf.segDual_nu hA, PositivityTheory.Gud.Symm.Pf.segDual_segDual hA]`. Use `push_cast`.

Both sides reduce to the same expression. Simplify using `only [r2, neg_neg] at hM2`. Conclude with `hM2.symm`.
-/
theorem segs_symm [CharZero k] {h N : ℕ} (δ : Fin h → IrrGL k) (Δ : Fin h → Segment k) (s : Fin h → ℝ)
    (hL : ∀ j, IsLSeg (Δ j) (δ j).rep) (hU : ∀ j, PositivityTheory.RgUd.UOrder.UnitCC (δ j).rep) (hs : ∀ j, |s j| < 1 / 2)
    (hd : ∑ j, ((δ j).nu (s j)).1 = N) (hi : (prodIrr (fun j => (δ j).nu (s j)) hd).IsIrreducible)
    (hu : IsUnitarisable (prodIrr (fun j => (δ j).nu (s j)) hd)) :
    (Finset.univ.val.map fun j => (Δ j).nu ((s j : ℝ) : ℂ)) =
      Finset.univ.val.map fun j => (Δ j).nu ((-s j : ℝ) : ℂ) := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := PositivityTheory.RgGu.NR.ConjDual.irrAdm'
  have hδu : ∀ j, IsUnitarisable (δ j).rep := fun j => PositivityTheory.Gud.Pf.unitarisable_of_unitCC (hL j) (hU j)
  have hc : ∀ j, PositivityTheory.UdReth2.IsCentred (Δ j) := fun j => PositivityTheory.Gud.Pf.isCentred_of_unitCC (hL j) (hU j)
  obtain ⟨hd1, ⟨e1⟩⟩ := PositivityTheory.Gud.Symm.Pf.conj_side hA δ s hδu hd hi hu
  obtain ⟨hd2, ⟨e2⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA (fun j => (δ j).nu (s j)) hd
  have hfun : (fun j => Zc.dualCl ((δ j).nu (s j))) = fun j => (Zc.dualCl (δ j)).nu (((fun j => -s j) j : ℝ) : ℂ) :=
    funext fun j => by rw [GlobalTheory.T.dual_class_twist_neg hA]; push_cast; rfl
  have hd3 : ∑ j, ((Zc.dualCl (δ j)).nu (((fun j => -s j) j : ℝ) : ℂ)).1 = N := by
    rw [← hd2]; exact congrArg (fun f : Fin h → IrrGL k => ∑ j, (f j).1) hfun.symm
  obtain ⟨e3⟩ := congrProd' hfun hd2 hd3
  have E := e1.symm.trans (e2.trans e3)

  have key : ∀ (t : Fin h → ℝ), (∀ j, |t j| < 1 / 2) → ∀ i j,
      ¬ ((Zc.segDual (Δ i)).nu (t i : ℂ)).Precedes ((Zc.segDual (Δ j)).nu (t j : ℂ)) := by
    intro t ht i j hP
    have r : ∀ a, (Zc.segDual (Δ a)).nu (t a : ℂ) = Zc.segDual ((Δ a).nu ((-t a : ℝ) : ℂ)) := fun a => by
      rw [PositivityTheory.Gud.Symm.Pf.segDual_nu hA]; push_cast; rw [neg_neg]
    rw [r, r, GlobalTheory.T.segment_dual_precedes_iff hA] at hP
    have := PositivityTheory.UdReth2.add_one_le_of_precedes _ _ (hc j) (hc i) _ _ hP
    have h1 := ht i; have h2 := ht j
    rw [abs_lt] at h1 h2
    linarith
  have hM := PositivityTheory.Gud.Symm.Pf.multiset_of_equiv (fun j => Zc.segDual (Δ j)) (fun j => Zc.dualCl (δ j)) s (fun j => -s j)
    (fun j => PositivityTheory.Gud.Symm.Pf.isLSeg_dualCl hA (hL j)) (key s hs) (key (fun j => -s j) (fun j => by simpa using hs j))
    hd1 hd3 ⟨E⟩
  have hM2 := congrArg (Multiset.map Zc.segDual) hM
  simp only [Multiset.map_map, Function.comp_def] at hM2
  have r2 : ∀ (a : Fin h) (t : ℝ), Zc.segDual ((Zc.segDual (Δ a)).nu (t : ℂ)) = (Δ a).nu ((-t : ℝ) : ℂ) := fun a t => by
    rw [PositivityTheory.Gud.Symm.Pf.segDual_nu hA, PositivityTheory.Gud.Symm.Pf.segDual_segDual hA]; push_cast; rfl
  simp only [r2, neg_neg] at hM2
  exact hM2.symm

end PositivityTheory.Gud.Fin

end

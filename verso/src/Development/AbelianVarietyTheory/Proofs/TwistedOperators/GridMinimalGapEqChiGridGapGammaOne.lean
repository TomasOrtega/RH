import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

/- English proof (translation)
Break down `le_or_gt 0 x with h | h` into its components or cases. Rewrite using `[show ((x.toNat : ℕ) : ℝ) = (x : ℝ) by exact_mod_cast Int.toNat_of_nonneg h]`. Rewrite using `[Real.sqrt_eq_zero'.2 (by exact_mod_cast h.le), Int.toNat_eq_zero.2 h.le]; simp`.
-/
theorem sqrt_intCast_eq_sqrt_toNat (x : ℤ) : Real.sqrt (x : ℝ) = Real.sqrt ((x.toNat : ℕ) : ℝ) := by
  rcases le_or_gt 0 x with h | h
  · rw [show ((x.toNat : ℕ) : ℝ) = (x : ℝ) by exact_mod_cast Int.toNat_of_nonneg h]
  · rw [Real.sqrt_eq_zero'.2 (by exact_mod_cast h.le), Int.toNat_eq_zero.2 h.le]; simp

/- English proof (translation)
Introduce `D`. Use `haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩`. Establish `hv : ∀ τ : D.what₂.Tau, (GlobalTheory.Grid.gridOf D 0 0 τ).v = (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v` using `fun _ => rfl`. Establish `hk : ∀ τ : D.what₂.Tau, (GlobalTheory.Grid.gridOf D 0 0 τ).v 2 - (GlobalTheory.Grid.gridOf D 0 0 τ).v D.R.k = (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k` using `fun τ => by rw [hv]`. Establish `hN : (GlobalTheory.Grid.bigN D : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ)` using `rfl`.

Establish `hN' : GlobalTheory.Grid.bigN D = GlobalTheory.ChiGrid.bigN D` using `rfl`. Establish `hs : GlobalTheory.Grid.sLen D = GlobalTheory.ChiGrid.sLen D` using `rfl`. Establish `hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = (D.R.r : ℝ) + 1` using `by simp [GlobalTheory.ChiGrid.nRk]`. Use `set f : D.what₂.Tau → ℤ := fun τ => (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k with hf`. Establish `hc : GlobalTheory.ChiGrid.cloudLen D = Finset.univ.sup fun τ => (f τ).toNat` using `rfl`.

Establish `key : ∀ γ : ℕ, GlobalTheory.Grid.GapCond D γ ↔ GlobalTheory.ChiGrid.GapBound D 1 γ`. Introduce `γ`. Unfold `GlobalTheory.Grid.GapCond GlobalTheory.ChiGrid.GapBound`. Simplify using `only [one_mul, hk, hn, hN, hN', hs, hc]`. Use `and_congr ?_ Iff.rfl` and prove the remaining obligations.

Establish `hB : (0 : ℝ) ≤ ((D.R.r : ℝ) + 1) ^ 3` using `by positivity`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨τ, -, hτ⟩` from `Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun τ => (f τ).toNat`. Use `h τ` as an intermediate fact.

Rewrite `this` using `[sqrt_intCast_eq_sqrt_toNat]`. Rewrite using `[hτ]`. Conclude with `this`. Introduce `h τ`. Rewrite using `[sqrt_intCast_eq_sqrt_toNat]`.

Use `le_trans ?_ h` and prove the remaining obligations. Establish `h1 : (f τ).toNat ≤ Finset.univ.sup fun τ => (f τ).toNat` using `Finset.le_sup (f := fun τ => (f τ).toNat) (Finset.mem_univ τ)`. Establish `h2 : Real.sqrt (((f τ).toNat : ℕ) : ℝ) ≤ Real.sqrt (((Finset.univ.sup fun τ => (f τ).toNat : ℕ)) : ℝ)` using `Real.sqrt_le_sqrt (by exact_mod_cast h1)`. Use the polynomial consequences of the given equalities and inequalities. Establish `e : {γ | GlobalTheory.Grid.GapCond D γ} = {g | GlobalTheory.ChiGrid.GapBound D 1 g}` using `Set.ext fun γ => key γ`.

Establish `h1` using `GlobalTheory.Grid.isLeast_gap D`. Rewrite `h1` using `[e]`. Conclude with `h1.unique (GlobalTheory.ChiGrid.isLeast_gap D 1)`.
-/
theorem gap_eq_chiGap : ∀ D : D7, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 := by
  intro D
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hv : ∀ τ : D.what₂.Tau, (GlobalTheory.Grid.gridOf D 0 0 τ).v = (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v := fun _ => rfl
  have hk : ∀ τ : D.what₂.Tau, (GlobalTheory.Grid.gridOf D 0 0 τ).v 2 - (GlobalTheory.Grid.gridOf D 0 0 τ).v D.R.k =
      (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k := fun τ => by rw [hv]
  have hN : (GlobalTheory.Grid.bigN D : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := rfl
  have hN' : GlobalTheory.Grid.bigN D = GlobalTheory.ChiGrid.bigN D := rfl
  have hs : GlobalTheory.Grid.sLen D = GlobalTheory.ChiGrid.sLen D := rfl
  have hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = (D.R.r : ℝ) + 1 := by simp [GlobalTheory.ChiGrid.nRk]
  set f : D.what₂.Tau → ℤ := fun τ => (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k with hf
  have hc : GlobalTheory.ChiGrid.cloudLen D = Finset.univ.sup fun τ => (f τ).toNat := rfl
  have key : ∀ γ : ℕ, GlobalTheory.Grid.GapCond D γ ↔ GlobalTheory.ChiGrid.GapBound D 1 γ := by
    intro γ
    unfold GlobalTheory.Grid.GapCond GlobalTheory.ChiGrid.GapBound
    simp only [one_mul, hk, hn, hN, hN', hs, hc]
    refine and_congr ?_ Iff.rfl
    have hB : (0 : ℝ) ≤ ((D.R.r : ℝ) + 1) ^ 3 := by positivity
    constructor
    · intro h
      obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun τ => (f τ).toNat
      have := h τ
      rw [sqrt_intCast_eq_sqrt_toNat] at this
      rw [hτ]; exact this
    · intro h τ
      rw [sqrt_intCast_eq_sqrt_toNat]
      refine le_trans ?_ h
      have h1 : (f τ).toNat ≤ Finset.univ.sup fun τ => (f τ).toNat := Finset.le_sup (f := fun τ => (f τ).toNat) (Finset.mem_univ τ)
      have h2 : Real.sqrt (((f τ).toNat : ℕ) : ℝ) ≤ Real.sqrt (((Finset.univ.sup fun τ => (f τ).toNat : ℕ)) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast h1)
      nlinarith
  have e : {γ | GlobalTheory.Grid.GapCond D γ} = {g | GlobalTheory.ChiGrid.GapBound D 1 g} := Set.ext fun γ => key γ
  have h1 := GlobalTheory.Grid.isLeast_gap D
  rw [e] at h1
  exact h1.unique (GlobalTheory.ChiGrid.isLeast_gap D 1)

end GlobalTheory.GridJoin

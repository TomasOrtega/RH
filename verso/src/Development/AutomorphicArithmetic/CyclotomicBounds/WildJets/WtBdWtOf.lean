import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ParBdGeneric
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
open GlobalTheory.SignedHC

/- English proof (translation)
Distinguish the cases in `hc : E.card = n ∧ InCoset (((n : ℚ) - 1) / 2) E`. Establish `e1` using `wtOf_cast hc.1 hc.2 a`. Establish `e2` using `wtOf_cast hc.1 hc.2 a'`. Establish `b1` using `abs_le.1 (hE _ (descEnum_mem E hc.1 a))`. Establish `b2` using `abs_le.1 (hE _ (descEnum_mem E hc.1 a'))`.

Unfold `highestWeight at e1 e2`. Establish `e1'` using `congrArg (fun q : ℚ => (q : ℝ)) e1`. Establish `e2'` using `congrArg (fun q : ℚ => (q : ℝ)) e2`. Establish `h' : ((a : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ)` using `by exact_mod_cast h`. Move the coercions through the operations in `at e1' e2' ⊢`.

Combine the linear relations using `[b1.1, b1.2, b2.1, b2.2]`. Rewrite using `[wtOf, dif_neg hc]`. Simplify using `only [Pi.zero_apply, sub_self, Int.cast_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem wtBd_wtOf (n : ℕ) (E : Finset ℚ) (B : ℝ) (hB : 0 ≤ B) (hE : ∀ x ∈ E, |(x : ℝ)| ≤ B)
    (a a' : Fin n) (h : a ≤ a') : (((wtOf n E).w a - (wtOf n E).w a' : ℤ) : ℝ) ≤ 2 * B := by
  by_cases hc : E.card = n ∧ InCoset (((n : ℚ) - 1) / 2) E
  · have e1 := wtOf_cast hc.1 hc.2 a
    have e2 := wtOf_cast hc.1 hc.2 a'
    have b1 := abs_le.1 (hE _ (descEnum_mem E hc.1 a))
    have b2 := abs_le.1 (hE _ (descEnum_mem E hc.1 a'))
    unfold highestWeight at e1 e2
    have e1' := congrArg (fun q : ℚ => (q : ℝ)) e1
    have e2' := congrArg (fun q : ℚ => (q : ℝ)) e2
    have h' : ((a : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at e1' e2' ⊢
    linarith [b1.1, b1.2, b2.1, b2.2]
  · rw [wtOf, dif_neg hc]
    simp only [Pi.zero_apply, sub_self, Int.cast_zero]
    linarith

/- English proof (translation)
Establish `hn : 0 < n` using `a.pos`. Establish `hle : a ≤ (⟨n - 1, by omega⟩ : Fin n)`. Use `a.2` as an intermediate fact. Use `show a.1 ≤ n - 1`. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `h a _ hle`. Establish `h2` using `lam.anti hle`. Establish `h3 : ((lam.natW a : ℕ) : ℤ) = lam.w a - lam.w ⟨n - 1, by omega⟩`. Unfold `DomWeight.natW DomWeight.detShift`. Rewrite using `[dif_pos hn]`.

Conclude with `Int.toNat_of_nonneg (by linarith)`. Rewrite `h1` using `[← h3]`. Conclude with `h1` after adjusting the coercions.
-/
private theorem wtBd_natW {n : ℕ} (lam : DomWeight n) (C : ℝ)
    (h : ∀ a a' : Fin n, a ≤ a' → ((lam.w a - lam.w a' : ℤ) : ℝ) ≤ C) (a : Fin n) :
    ((lam.natW a : ℕ) : ℝ) ≤ C := by
  have hn : 0 < n := a.pos
  have hle : a ≤ (⟨n - 1, by omega⟩ : Fin n) := by
    have := a.2
    show a.1 ≤ n - 1
    omega
  have h1 := h a _ hle
  have h2 := lam.anti hle
  have h3 : ((lam.natW a : ℕ) : ℤ) = lam.w a - lam.w ⟨n - 1, by omega⟩ := by
    unfold DomWeight.natW DomWeight.detShift
    rw [dif_pos hn]
    exact Int.toNat_of_nonneg (by linarith)
  rw [← h3] at h1
  exact_mod_cast h1

/- English proof (translation)
Establish `h1` using `h a'.rev a.rev (Fin.rev_le_rev.2 haa)`. Establish `e : lam.dual.w a - lam.dual.w a' = lam.w a'.rev - lam.w a.rev` using `by show -lam.w a.rev - -lam.w a'.rev = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h1`.
-/
private theorem wtBd_dual {n : ℕ} (lam : DomWeight n) (C : ℝ)
    (h : ∀ a a' : Fin n, a ≤ a' → ((lam.w a - lam.w a' : ℤ) : ℝ) ≤ C) (a a' : Fin n) (haa : a ≤ a') :
    ((lam.dual.w a - lam.dual.w a' : ℤ) : ℝ) ≤ C := by
  have h1 := h a'.rev a.rev (Fin.rev_le_rev.2 haa)
  have e : lam.dual.w a - lam.dual.w a' = lam.w a'.rev - lam.w a.rev := by
    show -lam.w a.rev - -lam.w a'.rev = _
    ring
  rw [e]; exact h1

end

/- English proof (translation)
Introduce `D T L sc G large₂ hS hH hc p hp τ`. Take `⟨-, -, -, -, -, -, -, h12⟩` from `GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS`. Establish `key : ∀ X : Node, DefNode D.R.m X → ∀ a, (((wt G X τ).natW a : ℕ) : ℝ) ≤ 12 * large₂.sc.b`. Introduce `X hX`. Establish `hb` using `UpperTheory.WildA.parBd D large₂ hS hH X hX τ`.

Rewrite `hb` using `[← hc]`. Establish `hl : ∀ a a', a ≤ a' → (((listedWt G X τ).w a - (listedWt G X τ).w a' : ℤ) : ℝ) ≤ 12 * large₂.sc.b`. Introduce `a a' h`. Use `wtBd_wtOf (G.V X).rank _ (6 * large₂.sc.b) (by linarith) hb a a' h` as an intermediate fact. Unfold `listedWt`.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the cases of `X with`. Consider the case `core i => exact hX.elim`. Consider the case `top j => exact wtBd_natW _ _ hl`. Consider the case `grid i j => exact wtBd_natW _ _ (wtBd_dual _ _ hl)`.

Conclude with `key p.big hp.nodes.2`.
-/
theorem UpperTheory.WildA.wtBd :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → sc.cGap = 1 → ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p →
      ∀ τ a, (((wt G p.big τ).natW a : ℕ) : ℝ) ≤ 12 * large₂.sc.b := by
  intro D T L sc G large₂ hS hH hc p hp τ
  obtain ⟨-, -, -, -, -, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS
  have key : ∀ X : Node, DefNode D.R.m X → ∀ a, (((wt G X τ).natW a : ℕ) : ℝ) ≤ 12 * large₂.sc.b := by
    intro X hX
    have hb := UpperTheory.WildA.parBd D large₂ hS hH X hX τ
    rw [← hc] at hb
    have hl : ∀ a a', a ≤ a' → (((listedWt G X τ).w a - (listedWt G X τ).w a' : ℤ) : ℝ) ≤ 12 * large₂.sc.b := by
      intro a a' h
      have := wtBd_wtOf (G.V X).rank _ (6 * large₂.sc.b) (by linarith) hb a a' h
      unfold listedWt
      linarith
    cases X with
    | core i => exact hX.elim
    | top j => exact wtBd_natW _ _ hl
    | grid i j => exact wtBd_natW _ _ (wtBd_dual _ _ hl)
  exact key p.big hp.nodes.2

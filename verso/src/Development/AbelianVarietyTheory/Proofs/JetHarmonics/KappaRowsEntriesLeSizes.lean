import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.WeightRows

/- English proof (translation)
Introduce `D L Pm Tp hK j hj τ`. Establish `h1` using `hj.1`. Establish `h2` using `hj.2`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `a9 : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`.

Establish `big : ∀ i : Fin (D.R.sigW j).1, ((kaR Tp hK j).aP τ i : ℝ) ≤ ((DV.sigPar D τ i : ℚ) : ℝ) + (((D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ)`. Introduce `i`. Establish `hi : i.1 < D.R.k + j - 1` using `i.2`. Establish `hi' : i.1 + 2 ≤ D.R.k + j` using `by omega`. Establish `hr : (i.1 : ℝ) + 2 ≤ D.R.k + j` using `by exact_mod_cast hi'`.

Establish `e1` using `kaWt_big D hK (even_nV Tp) j h1 h2 τ i`. Establish `e2` using `(hK j h1 h2 τ).1 i`. Rewrite `e2` using `[← e1, DV.aPlusQ_eq]`. Unfold `DV.eQ at e2`. Rewrite `e2` using `[dif_pos ⟨h1, h2⟩]`.

Establish `e3` using `congrArg (fun q : ℚ => (q : ℝ)) e2`. Move the coercions through the operations in `at e3`. Unfold `kaR`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun i hi => ?_, fun i hi => ?_, fun i => ?_⟩` and prove the remaining obligations.

Establish `b` using `big i`. Unfold `DV.sigPar at b`. Rewrite `b` using `[dif_pos hi]`. Establish `a1` using `(L.cloud_v τ ⟨i.1, hi⟩).2`. Unfold `wj`.

Rewrite using `[dif_pos (by omega : j - 1 < D.R.m)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b` using `big i`. Establish `hi2 : i.1 < D.R.k + j - 1` using `i.2`. Establish `hb : i.1 - (D.R.k - 1) < D.R.m` using `by omega`.

Unfold `DV.sigPar at b`. Rewrite `b` using `[dif_neg (by omega), dif_pos hb]`. Establish `a2` using `(abs_le.1 (L.be_close τ ⟨i.1 - (D.R.k - 1), hb⟩ ⟨j - 1, by omega⟩)).1`. Move the coercions through the operations in `at a2 b`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hs : (D.R.sigW j).2 = D.R.m - j` using `rfl`. Establish `e1` using `kaWt_small D hK (even_nV Tp) j h1 h2 τ i`. Establish `e2` using `(hK j h1 h2 τ).2 (Fin.rev i)`. Establish `hi` using `(Fin.rev i).2`. Unfold `DV.aMinusQ DV.eQ at e2`.

Rewrite `e2` using `[dif_pos (by omega), dif_pos ⟨h1, h2⟩]`. Establish `a2` using `(abs_le.1 (L.be_close τ ⟨j + (Fin.rev i).1, by omega⟩ ⟨j - 1, by omega⟩)).2`. Establish `a8 : (0 : ℝ) ≤ (Fin.rev i).1` using `Nat.cast_nonneg _`. Establish `e3` using `congrArg (fun q : ℚ => (q : ℝ)) e2`. Establish `e4` using `congrArg (fun q : ℤ => (q : ℝ)) e1`.

Move the coercions through the operations in `at e3 e4 a2`. Unfold `kaR`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kappa_entries_le : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ τ : D.what₂.Tau, (∀ i, i.1 < D.R.k - 1 → ((kaR Tp hK j).aP τ i : ℝ) ≤ wj D j τ + L.Sc) ∧ (∀ i, D.R.k - 1 ≤ i.1 → ((kaR Tp hK j).aP τ i : ℝ) ≤ L.etaSz) ∧ ∀ i, ((kaR Tp hK j).aM τ i : ℝ) ≤ L.etaSz := by
  intro D L Pm Tp hK j hj τ
  have h1 := hj.1
  have h2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have a9 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have big : ∀ i : Fin (D.R.sigW j).1, ((kaR Tp hK j).aP τ i : ℝ) ≤
      ((DV.sigPar D τ i : ℚ) : ℝ) + (((D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by
    intro i
    have hi : i.1 < D.R.k + j - 1 := i.2
    have hi' : i.1 + 2 ≤ D.R.k + j := by omega
    have hr : (i.1 : ℝ) + 2 ≤ D.R.k + j := by exact_mod_cast hi'
    have e1 := kaWt_big D hK (even_nV Tp) j h1 h2 τ i
    have e2 := (hK j h1 h2 τ).1 i
    rw [← e1, DV.aPlusQ_eq] at e2
    unfold DV.eQ at e2
    rw [dif_pos ⟨h1, h2⟩] at e2
    have e3 := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at e3
    unfold kaR
    linarith
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i => ?_⟩
  · have b := big i
    unfold DV.sigPar at b
    rw [dif_pos hi] at b
    have a1 := (L.cloud_v τ ⟨i.1, hi⟩).2
    unfold wj
    rw [dif_pos (by omega : j - 1 < D.R.m)]
    linarith
  · have b := big i
    have hi2 : i.1 < D.R.k + j - 1 := i.2
    have hb : i.1 - (D.R.k - 1) < D.R.m := by omega
    unfold DV.sigPar at b
    rw [dif_neg (by omega), dif_pos hb] at b
    have a2 := (abs_le.1 (L.be_close τ ⟨i.1 - (D.R.k - 1), hb⟩ ⟨j - 1, by omega⟩)).1
    push_cast at a2 b
    linarith
  · have hs : (D.R.sigW j).2 = D.R.m - j := rfl
    have e1 := kaWt_small D hK (even_nV Tp) j h1 h2 τ i
    have e2 := (hK j h1 h2 τ).2 (Fin.rev i)
    have hi := (Fin.rev i).2
    unfold DV.aMinusQ DV.eQ at e2
    rw [dif_pos (by omega), dif_pos ⟨h1, h2⟩] at e2
    have a2 := (abs_le.1 (L.be_close τ ⟨j + (Fin.rev i).1, by omega⟩ ⟨j - 1, by omega⟩)).2
    have a8 : (0 : ℝ) ≤ (Fin.rev i).1 := Nat.cast_nonneg _
    have e3 := congrArg (fun q : ℚ => (q : ℝ)) e2
    have e4 := congrArg (fun q : ℤ => (q : ℝ)) e1
    push_cast at e3 e4 a2
    unfold kaR
    linarith

end GlobalTheory.WeightRows

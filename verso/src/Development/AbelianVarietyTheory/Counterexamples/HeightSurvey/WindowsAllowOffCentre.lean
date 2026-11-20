import Mathlib
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

noncomputable section

namespace GlobalTheory.RunCounterexample

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {Q : ModuliIntegralCharts.Prov D} {j : ℕ}

/- English proof (translation)
Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hi' : i.1 + 1 = D.R.k + j - 1` using `hi`. Establish `e1` using `Cons.kaWt_big D hK hn j h1 h2 τ i`. Establish `e2` using `(hK j h1 h2 τ).1 i`. Establish `hlt : ¬ (i.1 < D.R.k - 1)` using `by omega`.

Establish `hb : i.1 - (D.R.k - 1) < D.R.m` using `by omega`. Establish `hc : ((i.1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1`. Establish `: i.1 + 2 = D.R.k + j` using `by omega`. Establish `h' : ((i.1 : ℚ) + 2) = D.R.k + j` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `e2` using `[DV.aPlusQ_eq, hc]`. Unfold `DV.sigPar DV.eQ at e2`. Rewrite `e2` using `[dif_neg hlt, dif_pos hb, dif_pos ⟨h1, h2⟩]`. Establish `hx : (⟨i.1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩` using `Fin.ext (by show i.1 - (D.R.k - 1) = j - 1; omega)`. Rewrite `e2` using `[hx, ← e1]`.

Establish `e3 : (((Cons.kaWt D hK hn j).aP τ i : ℕ) : ℚ) = ((D.hc τ).e ⟨j - 1, by omega⟩ - (D.hc τ).b ⟨j - 1, by omega⟩ : ℚ) - ((D.R.t : ℚ) + 1) / 2`. Move the coercions through the operations in `at e2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e4` using `congrArg (fun q : ℚ => (q : ℝ)) e3`. Move the coercions through the operations in `at e4 ⊢`.

Conclude with `e4`.
-/
theorem last_plus (hK : DV.KapDef D) (hn : Even D.R.nV) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) (hi : i.1 + 1 = (D.R.sigW j).1) :
    (((Cons.kaWt D hK hn j).aP τ i : ℕ) : ℝ) =
      ((((D.hc τ).e ⟨j - 1, by omega⟩ - (D.hc τ).b ⟨j - 1, by omega⟩ : ℚ)) : ℝ) - ((D.R.t : ℝ) + 1) / 2 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hi' : i.1 + 1 = D.R.k + j - 1 := hi
  have e1 := Cons.kaWt_big D hK hn j h1 h2 τ i
  have e2 := (hK j h1 h2 τ).1 i
  have hlt : ¬ (i.1 < D.R.k - 1) := by omega
  have hb : i.1 - (D.R.k - 1) < D.R.m := by omega
  have hc : ((i.1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1 := by
    have : i.1 + 2 = D.R.k + j := by omega
    have h' : ((i.1 : ℚ) + 2) = D.R.k + j := by exact_mod_cast this
    linarith
  rw [DV.aPlusQ_eq, hc] at e2
  unfold DV.sigPar DV.eQ at e2
  rw [dif_neg hlt, dif_pos hb, dif_pos ⟨h1, h2⟩] at e2
  have hx : (⟨i.1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ := Fin.ext (by show i.1 - (D.R.k - 1) = j - 1; omega)
  rw [hx, ← e1] at e2
  have e3 : (((Cons.kaWt D hK hn j).aP τ i : ℕ) : ℚ) =
      ((D.hc τ).e ⟨j - 1, by omega⟩ - (D.hc τ).b ⟨j - 1, by omega⟩ : ℚ) - ((D.R.t : ℚ) + 1) / 2 := by
    push_cast at e2; linarith
  have e4 := congrArg (fun q : ℚ => (q : ℝ)) e3
  push_cast at e4 ⊢
  exact e4

/- English proof (translation)
Establish `e1` using `Cons.kaWt_small D hK hn j h1 h2.le τ i`. Establish `e2` using `(hK j h1 h2.le τ).2 (Fin.rev i)`. Establish `h0 : ((Fin.rev i : Fin _) : ℕ) = 0` using `by rw [Fin.val_rev]; omega`. Rewrite `e2` using `[h0]`. Unfold `DV.aMinusQ DV.eQ at e2`.

Rewrite `e2` using `[dif_pos (by omega : j + 0 < D.R.m), dif_pos ⟨h1, h2.le⟩]`. Establish `e1' : (((Cons.kaWt D hK hn j).aM τ i : ℕ) : ℚ) = -(D.what₂.kaSmall j τ (Fin.rev i) : ℚ)` using `by exact_mod_cast e1`. Establish `e3 : (((Cons.kaWt D hK hn j).aM τ i : ℕ) : ℚ) = ((D.hc τ).b ⟨j, h2⟩ - (D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) - ((D.R.t : ℚ) + 1) / 2`. Rewrite using `[e1', e2]`. Simplify using the standard rewrite rules.

Establish `e4` using `congrArg (fun q : ℚ => (q : ℝ)) e3`. Move the coercions through the operations in `at e4 ⊢`. Conclude with `e4`.
-/
theorem last_minus (hK : DV.KapDef D) (hn : Even D.R.nV) (h1 : 1 ≤ j) (h2 : j < D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).2) (hi : i.1 + 1 = (D.R.sigW j).2) :
    (((Cons.kaWt D hK hn j).aM τ i : ℕ) : ℝ) =
      ((((D.hc τ).b ⟨j, h2⟩ - (D.hc τ).e ⟨j - 1, by omega⟩ : ℚ)) : ℝ) - ((D.R.t : ℝ) + 1) / 2 := by
  have e1 := Cons.kaWt_small D hK hn j h1 h2.le τ i
  have e2 := (hK j h1 h2.le τ).2 (Fin.rev i)
  have h0 : ((Fin.rev i : Fin _) : ℕ) = 0 := by rw [Fin.val_rev]; omega
  rw [h0] at e2
  unfold DV.aMinusQ DV.eQ at e2
  rw [dif_pos (by omega : j + 0 < D.R.m), dif_pos ⟨h1, h2.le⟩] at e2
  have e1' : (((Cons.kaWt D hK hn j).aM τ i : ℕ) : ℚ) = -(D.what₂.kaSmall j τ (Fin.rev i) : ℚ) := by exact_mod_cast e1
  have e3 : (((Cons.kaWt D hK hn j).aM τ i : ℕ) : ℚ) =
      ((D.hc τ).b ⟨j, h2⟩ - (D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) - ((D.R.t : ℚ) + 1) / 2 := by
    rw [e1', e2]; simp
  have e4 := congrArg (fun q : ℚ => (q : ℝ)) e3
  push_cast at e4 ⊢
  exact e4

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

/- English proof (translation)
Establish `ht : (5 : ℝ) ≤ D.R.t`. Use `D.R.rank_add_five_le` as an intermediate fact. Conclude with `(by omega : 5 ≤ D.R.t)` after adjusting the coercions. Use `⟨by have := T.heightBound_ge_order_sq; linarith, fun τ i hi => ?_, fun τ i hi => ?_⟩` and prove the remaining obligations. Establish `hc` using `abs_le.1 (P.e_centred τ ⟨j - 1, by omega⟩)`.

Unfold `Cons.kaR`. Rewrite using `[last_plus hK _ h1 h2 τ i hi]`. Combine the linear relations using `[hc.1]`. Establish `h3 : j < D.R.m`. Establish `hs : (D.R.sigW j).2 = D.R.m - j` using `rfl`.

Use linear arithmetic over natural numbers and integers. Establish `hc` using `abs_le.1 (P.e_centred τ ⟨j - 1, by omega⟩)`. Establish `hg` using `(P.nodes_gap τ (j - 1) (by omega)).1`. Establish `hx : (⟨j - 1 + 1, by omega⟩ : Fin D.R.m) = ⟨j, h3⟩` using `Fin.ext (by show j - 1 + 1 = j; omega)`. Rewrite `hg` using `[hx]`.

Unfold `Cons.kaR`. Rewrite using `[last_minus hK _ h1 h3 τ i hi]`. Move the coercions through the operations in `at hc hg ⊢`. Combine the linear relations using `[hc.2]`.
-/
theorem clauses_at_shifted_gap (T : ParamsT D L P) (hK : DV.KapDef D) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    4 * (T.TO : ℝ) ^ 2 + D.R.t + 1 ≤ LevelStarExponents.h0 L - 4 ∧
    (∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      (LevelStarExponents.h0 L - 4) / 2 - ((D.R.t : ℝ) + 1) / 2 ≤ ((Cons.kaR T hK j).aP τ i : ℝ)) ∧
    (∀ τ (i : Fin (D.R.sigW j).2), i.1 + 1 = (D.R.sigW j).2 →
      (LevelStarExponents.h0 L - 4) / 2 - ((D.R.t : ℝ) + 1) / 2 ≤ ((Cons.kaR T hK j).aM τ i : ℝ)) := by
  have ht : (5 : ℝ) ≤ D.R.t := by
    have := D.R.rank_add_five_le
    exact_mod_cast (by omega : 5 ≤ D.R.t)
  refine ⟨by have := T.heightBound_ge_order_sq; linarith, fun τ i hi => ?_, fun τ i hi => ?_⟩
  · have hc := abs_le.1 (P.e_centred τ ⟨j - 1, by omega⟩)
    unfold Cons.kaR
    rw [last_plus hK _ h1 h2 τ i hi]
    linarith [hc.1]
  · have h3 : j < D.R.m := by
      have hs : (D.R.sigW j).2 = D.R.m - j := rfl
      omega
    have hc := abs_le.1 (P.e_centred τ ⟨j - 1, by omega⟩)
    have hg := (P.nodes_gap τ (j - 1) (by omega)).1
    have hx : (⟨j - 1 + 1, by omega⟩ : Fin D.R.m) = ⟨j, h3⟩ := Fin.ext (by show j - 1 + 1 = j; omega)
    rw [hx] at hg
    unfold Cons.kaR
    rw [last_minus hK _ h1 h3 τ i hi]
    push_cast at hc hg ⊢
    linarith [hc.2]

end GlobalTheory.RunCounterexample

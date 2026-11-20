import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuLowerBoundLastIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDefiniteBoundGeAnchoredMainTermSubCrudeErrorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDimensionLogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.DefLow

/- English proof (translation)
Introduce `hP hG hA`. Establish `hc` using `GlobalTheory.T.mu_lower_bound_last_index hP`. Use `Closed.imp ((hA.and (hG.and (GlobalTheory.CovTop.WtShape.wtN.and GlobalTheory.T.weight_dimension_log_bound))).and hc) fun Fm CH _ h => ?_` and prove the remaining obligations. Take `⟨⟨⟨CA, hCA, xA, eA⟩, ⟨CG, -, xG, eG⟩, ⟨CW, -, xW, eW⟩, ⟨C3, hC3, x3, e3⟩⟩, ⟨C₀, hC₀, x0, h1⟩⟩` from `h`. Use `⟨CA + C3 + C₀, by positivity, max (max (max xA xG) (max xW x3)) x0, fun x hx hle' ι p hp i hi => ?_⟩` and prove the remaining obligations.

Establish `hle` using `le_trans (le_max_left _ _) hle'`. Establish `l0 : x0 ≤ x` using `le_trans (le_max_right _ _) hle'`. Establish `lA : xA ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle`. Establish `lG : xG ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle`. Establish `lW : xW ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle`.

Establish `l3 : x3 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle`. Establish `a` using `eA x hx lA ι p hp i`. Establish `g` using `eG x hx lG ι p hp i`. Establish `w` using `eW x hx lW ι p hp i`. Establish `s` using `e3 x hx l3 ι p hp i hi`.

Establish `c` using `h1 x hx l0 ι p hp i hi g`. Establish `hk` using `(Fm.D x ι).R.m_add_three_le_k`. Establish `q0 : (dat p i).q = 0`. Rewrite using `[w.sig.2.1]`. Unfold `Ranks.sigW`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `p1 : 1 ≤ (dat p i).p`. Rewrite using `[w.sig.1]`. Unfold `Ranks.sigW`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `ar` using `GlobalTheory.T.two_definiteBound_ge_anchoredMainTerm_sub_crude_errors _ _ (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1) (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm q0 p1 (p.κ i).n_even`. Establish `a1` using `a.1`. Simplify using `only [q0, Nat.cast_zero, sub_zero] at a1`.

Rewrite `a1` using `[abs_le]`. Unfold `LowAt`. Combine the linear relations using `[a1.1, a1.2]`.
-/
theorem lowDef : Hypotheses2 → Gram → Anchor → LowDef := by
  intro hP hG hA
  have hc := GlobalTheory.T.mu_lower_bound_last_index hP
  refine Closed.imp ((hA.and (hG.and (GlobalTheory.CovTop.WtShape.wtN.and GlobalTheory.T.weight_dimension_log_bound))).and hc) fun Fm CH _ h => ?_
  obtain ⟨⟨⟨CA, hCA, xA, eA⟩, ⟨CG, -, xG, eG⟩, ⟨CW, -, xW, eW⟩, ⟨C3, hC3, x3, e3⟩⟩, ⟨C₀, hC₀, x0, h1⟩⟩ := h
  refine ⟨CA + C3 + C₀, by positivity, max (max (max xA xG) (max xW x3)) x0,
    fun x hx hle' ι p hp i hi => ?_⟩
  have hle := le_trans (le_max_left _ _) hle'
  have l0 : x0 ≤ x := le_trans (le_max_right _ _) hle'
  have lA : xA ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have lG : xG ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have lW : xW ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have l3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle
  have a := eA x hx lA ι p hp i
  have g := eG x hx lG ι p hp i
  have w := eW x hx lW ι p hp i
  have s := e3 x hx l3 ι p hp i hi
  have c := h1 x hx l0 ι p hp i hi g
  have hk := (Fm.D x ι).R.m_add_three_le_k
  have q0 : (dat p i).q = 0 := by
    rw [w.sig.2.1]; unfold Ranks.sigW; simp only; omega
  have p1 : 1 ≤ (dat p i).p := by
    rw [w.sig.1]; unfold Ranks.sigW; simp only; omega
  have ar := GlobalTheory.T.two_definiteBound_ge_anchoredMainTerm_sub_crude_errors _ _ (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1)
    (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm q0 p1 (p.κ i).n_even
  have a1 := a.1
  simp only [q0, Nat.cast_zero, sub_zero] at a1
  rw [abs_le] at a1
  unfold LowAt
  linarith [a1.1, a1.2]

end GlobalTheory.CovTop.DefLow

end

import Formalism.SharpRestriction.Divisibility.OrbitPlaces

noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
Take `⟨U, hU, hT⟩` from `h0`. Conclude with `⟨ep, hep, be, ⟨sg, hsg, U, hU, hT⟩, h1, h2, h3, h4⟩`.
-/
theorem admissible_of_jet_bounds {E : Ent D} {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
    (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hep : ‖ep‖ = 1) (hsg : sg = 1 ∨ sg = -1)
    (h1 : Formalism.MainNotions.product_zeroth_first_parts.B1 p (nP D p) be) (h2 : Formalism.MainNotions.product_zeroth_first_parts.B2 p (nP D p) be) (h3 : Formalism.MainNotions.product_zeroth_first_parts.B3 p (nP D p) be)
    (h4 : Formalism.MainNotions.product_zeroth_first_parts.B4 p (nP D p) be) (h0 : OrbitThetaExpansion (orbLoc E p h u i z Th) ep sg be) :
    (orbLoc E p h u i z Th).AdmB := by
  obtain ⟨U, hU, hT⟩ := h0
  exact ⟨ep, hep, be, ⟨sg, hsg, U, hU, hT⟩, h1, h2, h3, h4⟩

/- English proof (translation)
Unfold `Formalism.MainNotions.product_zeroth_first_parts.KvalGe at hK ⊢`. Introduce `I m`. Use `(hK I m).trans ?_` and prove the remaining obligations. Establish `hl : (1 : ℝ) ≤ (l : ℝ)` using `by exact_mod_cast (Fact.out : l.Prime).one_lt.le`. Conclude with `Real.rpow_le_rpow_of_exponent_le hl (neg_le_neg hB)`.
-/
theorem kvalGe_mono {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]
    {nu : Lt → YoungDiagram} {Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]} {B B' : ℝ}
    (hK : Formalism.MainNotions.product_zeroth_first_parts.KvalGe N0 N1 l nu Th B) (hB : B' ≤ B) : Formalism.MainNotions.product_zeroth_first_parts.KvalGe N0 N1 l nu Th B' := by
  unfold Formalism.MainNotions.product_zeroth_first_parts.KvalGe at hK ⊢
  intro I m
  refine (hK I m).trans ?_
  have hl : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  exact Real.rpow_le_rpow_of_exponent_le hl (neg_le_neg hB)

end PI.OrbBoundFW

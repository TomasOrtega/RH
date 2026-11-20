import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

/- English proof (translation)
Introduce `D L P X C tf h i hi hl`. Take `⟨h2, hq, hd, hg⟩` from `hl`. Establish `hqd : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d)` using `by tauto`. Establish `hR0 : 0 ≤ C * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2`. Use `h.pos` as an intermediate fact.

Check the signs of the components of the expression. Use `show (if D.nd.l i ∈ D.host.small then TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i else if D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d then TwistedPlaces.midG L C (D.nd.l i) else if KillingConditions.RangeAD L X.exc (D.nd.l i) then KillingConditions.supZ i (X.errorBoundH …`. Rewrite using `[if_neg h2, if_neg hqd]`. Use `split_ifs with hR`. Unfold `KillingConditions.supZ split_ifs with hne`.

Conclude with `Finset.sup'_le hne _ (fun π hπ => h.bb i hi hg hR π hπ)`. Conclude with `hR0`. Conclude with `hR0`.
-/
theorem adm5_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm5 L (tab L X tf C) C := by
  classical
  intro D L P X C tf h i hi hl
  obtain ⟨h2, hq, hd, hg⟩ := hl
  have hqd : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by tauto
  have hR0 : 0 ≤ C * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 := by
    have := h.pos
    positivity
  show (if D.nd.l i ∈ D.host.small then TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i
    else if D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d then TwistedPlaces.midG L C (D.nd.l i)
    else if KillingConditions.RangeAD L X.exc (D.nd.l i) then KillingConditions.supZ i (X.errorBoundHub i) else 0) ≤ _
  rw [if_neg h2, if_neg hqd]
  split_ifs with hR
  · unfold KillingConditions.supZ
    split_ifs with hne
    · exact Finset.sup'_le hne _ (fun π hπ => h.bb i hi hg hR π hπ)
    · exact hR0
  · exact hR0

end GlobalTheory.NLink

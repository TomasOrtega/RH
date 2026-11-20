import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SwapCoeff

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem swap_eq_rename (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    swap c = rename (Equiv.sumComm (Fin d) (Fin d)) c := by
  rw [rename_eq_subst]
  unfold swap at2
  congr 1
  funext s
  rcases s with i | i <;> rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_swap : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a e) (swap c) = coeff (Finsupp.sumElim e a) c := by
  intro R _ d c a e
  have h := coeff_embDomain_rename (Equiv.sumComm (Fin d) (Fin d)).toEmbedding c (Finsupp.sumElim e a)
  have hinj : Function.Injective (Equiv.sumComm (Fin d) (Fin d)) := (Equiv.sumComm _ _).injective
  have hE : Finsupp.embDomain (Equiv.sumComm (Fin d) (Fin d)).toEmbedding (Finsupp.sumElim e a) =
      Finsupp.sumElim a e := by
    rw [Finsupp.embDomain_eq_mapDomain]
    ext x
    rcases x with i | i
    · have := Finsupp.mapDomain_apply hinj (Finsupp.sumElim e a) (Sum.inr i)
      simpa using this
    · have := Finsupp.mapDomain_apply hinj (Finsupp.sumElim e a) (Sum.inl i)
      simpa using this
  rw [hE] at h
  rw [swap_eq_rename]
  exact h

end GlobalTheory.SwapCoeff

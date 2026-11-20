import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTateA

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.GaloisCohomology

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

/- English proof (translation)
Introduce `l _ K hK r M _ _ _ _ _ rho hr hrho`. Take `⟨hsep, _, _, hloc, -⟩` from `hF l K hK`. Establish `: CharZero K` using `algebraRat.charZero K`. Take `⟨A, _, e, he⟩` from `gcRep (GK l K) (ZMod (l ^ r)) M rho hrho`. Establish `: Finite A` using `Finite.of_equiv _ e.toEquiv`.

Establish `hn : ((Nat.card A : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Take `⟨e0, -⟩` from `gc0 (GK l K) (ZMod (l ^ r)) M rho A e he`. Take `⟨e1, -⟩` from `gc1 (GK l K) (ZMod (l ^ r)) M rho A e he`. Take `⟨e2, -⟩` from `gc2 (GK l K) (ZMod (l ^ r)) M rho A e he`. Use `finite_cohomology_localField A hn 0` as an intermediate fact.

Use `finite_cohomology_localField A hn 1` as an intermediate fact. Use `finite_cohomology_localField A hn 2` as an intermediate fact. Use `⟨Finite.of_equiv _ e0.symm.toEquiv, Finite.of_equiv _ e1.symm.toEquiv, Finite.of_equiv _ e2.symm.toEquiv, fun n h => ?_⟩` and prove the remaining obligations. Take `⟨en⟩` from `gcn (GK l K) (ZMod (l ^ r)) M rho A e he n`. Use `subsingleton_cohomology_localField A hn n h` as an intermediate fact.

Conclude with `en.toEquiv.subsingleton`.
-/
theorem locfin_of (hF : SgcField) : Formalism.GaloisCohomology.LocalFinitenessK := by
  intro l _ K hK r M _ _ _ _ _ rho hr hrho
  obtain ⟨hsep, _, _, hloc, -⟩ := hF l K hK
  have : CharZero K := algebraRat.charZero K
  obtain ⟨A, _, e, he⟩ := gcRep (GK l K) (ZMod (l ^ r)) M rho hrho
  have : Finite A := Finite.of_equiv _ e.toEquiv
  have hn : ((Nat.card A : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  obtain ⟨e0, -⟩ := gc0 (GK l K) (ZMod (l ^ r)) M rho A e he
  obtain ⟨e1, -⟩ := gc1 (GK l K) (ZMod (l ^ r)) M rho A e he
  obtain ⟨e2, -⟩ := gc2 (GK l K) (ZMod (l ^ r)) M rho A e he
  have := finite_cohomology_localField A hn 0
  have := finite_cohomology_localField A hn 1
  have := finite_cohomology_localField A hn 2
  refine ⟨Finite.of_equiv _ e0.symm.toEquiv, Finite.of_equiv _ e1.symm.toEquiv,
    Finite.of_equiv _ e2.symm.toEquiv, fun n h => ?_⟩
  obtain ⟨en⟩ := gcn (GK l K) (ZMod (l ^ r)) M rho A e he n
  have := subsingleton_cohomology_localField A hn n h
  exact en.toEquiv.subsingleton

end PositivityTheory.LocalTateOrthogonality.Gcoh

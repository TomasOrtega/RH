import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.LocStep
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceFormAlt
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.ThmA
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerivPos
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.BernOf
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.HighestDerivProd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

namespace PositivityTheory.RgUd.All

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem thmT : ThmT k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with h | rfl
  · haveI : Fact p.Prime := ⟨h⟩
    exact TP.Final.thmT k p
  · haveI : CharZero k := CharP.charP_to_charZero k
    exact T.Final.thmT k

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmB : ThmB k := AB.Final.thmB k (AB.Final.thmA k (thmT k))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bernAt : BernAt k :=
  Prod.Final.bern_of k (Form.U.Final.derivTop k (thmB k)) (Form.U.Final.derivPos k (thmB k))
    (GlobalTheory.RgGu.Leib.Hand.leibnizOrd k)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible := fun k _ _ _ _ => bernAt k

end PositivityTheory.RgUd.All

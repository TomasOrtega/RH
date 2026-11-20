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
Take `⟨p, hp⟩` from `CharP.exists k`. Break down `CharP.char_is_prime_or_zero k p with h | rfl` into its components or cases. Use `haveI : Fact p.Prime := ⟨h⟩`. Conclude with `TP.Final.thmT k p`. Use `haveI : CharZero k := CharP.charP_to_charZero k`.

Conclude with `T.Final.thmT k`.
-/
theorem thmT : ThmT k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with h | rfl
  · haveI : Fact p.Prime := ⟨h⟩
    exact TP.Final.thmT k p
  · haveI : CharZero k := CharP.charP_to_charZero k
    exact T.Final.thmT k

/- English proof (translation)
The claim follows from `AB.Final.thmB k (AB.Final.thmA k (thmT k))`.
-/
theorem thmB : ThmB k := AB.Final.thmB k (AB.Final.thmA k (thmT k))

/- English proof (translation)
The claim follows from `Prod.Final.bern_of k (Form.U.Final.derivTop k (thmB k)) (Form.U.Final.derivPos k (thmB k)) (GlobalTheory.RgGu.Leib.Hand.leibnizOrd k)`.
-/
theorem bernAt : BernAt k :=
  Prod.Final.bern_of k (Form.U.Final.derivTop k (thmB k)) (Form.U.Final.derivPos k (thmB k))
    (GlobalTheory.RgGu.Leib.Hand.leibnizOrd k)

/- English proof (translation)
Introduce `k _ _ _ _` and use `bernAt k`.
-/
theorem bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible := fun k _ _ _ _ => bernAt k

end PositivityTheory.RgUd.All

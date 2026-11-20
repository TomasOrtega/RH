import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocalContinuity.LocalDescentHolds
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.AdjointSemisimple.AdjunctionCharZero
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.MemBzOfAdjoin
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.DescFinal
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpB

namespace PositivityTheory.RgUd.T.Final

open PositivityTheory.RgUd.T

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dich [CharZero k] : Dich (k := k) := PositivityTheory.RgUd.T.Alg.dich k
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem adjP [CharZero k] : Adj (k := k) := adjunction_char_zero k
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locStep : LocStep (k := k) := LocStepPf.local_descent_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem descA [CharZero k] : DescA (k := k) := PositivityTheory.RgUd.T.Desc.Final.descA k
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nilpB [CharZero k] : NilpB (k := k) := PositivityTheory.RgUd.T.Nil.Final.nilpB k

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Extract witnesses or component facts from the available result. Prove the second alternative.
-/
theorem van_all [CharZero k] : ∀ (m n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)),
    Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) = m → CR Z → Van Z := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n Z hm hZ
    refine nilpB k n Z hZ fun ξ hs hi => locStep k n Z hZ ξ hs hi fun y => ?_
    rcases dich k n Z hZ y with h | ⟨s, hs, hsZ, hss, hy⟩
    · exact Or.inl h
    · obtain ⟨hC, hlt⟩ := adjP k n Z hZ s hs hsZ hss
      exact Or.inr fun ξ' h1 h2 => descA k n Z hZ s hs hsZ hss (ih _ (hm ▸ hlt) n _ rfl hC) y hy ξ' h1 h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem thmT [CharZero k] : PositivityTheory.RgUd.ThmT k := by
  intro n Z hcomm hred ξ hsupp hinv f hf
  exact van_all k _ n Z rfl ⟨hcomm, hred⟩ ξ (fun g hg h0 => hsupp g hg fun p hp => h0 p ⟨hp, Set.mem_univ _⟩)
    (fun g hg f hf => hinv g hg f hf) f hf

end PositivityTheory.RgUd.T.Final

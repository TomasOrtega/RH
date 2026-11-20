import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply an available result and prove the equalities needed to match it to the conclusion. A detailed English derivation is pending.
-/
theorem isDom_monoid : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), D.IsDom 1 ∧ ∀ t t' : D.T, D.IsDom t → D.IsDom t' → D.IsDom (t * t') := by
  intro G _ _ _ D
  refine ⟨⟨fun n hn => by simpa using hn, fun n hn => by simpa using hn,
    fun x hx => ⟨by simpa using hx, by simpa using hx⟩⟩, ?_⟩
  rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · have h := h1 _ (h1' n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := h2' _ (h2 n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3 _ (h3' x hx).1).1
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3' _ (h3 x hx).2).2
    rw [Subgroup.coe_mul]
    convert h using 1
    group

end GlobalTheory.CompanionTheory.Cass

import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

/- English proof (translation)
Introduce `G _ _ _ D`. Use `⟨⟨fun n hn => by simpa using hn, fun n hn => by simpa using hn, fun x hx => ⟨by simpa using hx, by simpa using hx⟩⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩`. Use `⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h` using `h1 _ (h1' n hn)`.

Rewrite using `[Subgroup.coe_mul]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `group`. Establish `h` using `h2' _ (h2 n hn)`. Rewrite using `[Subgroup.coe_mul]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use `group`. Establish `h` using `(h3 _ (h3' x hx).1).1`. Rewrite using `[Subgroup.coe_mul]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use `group`. Establish `h` using `(h3' _ (h3 x hx).2).2`. Rewrite using `[Subgroup.coe_mul]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `group`.
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

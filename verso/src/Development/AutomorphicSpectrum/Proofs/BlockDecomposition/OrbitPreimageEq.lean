import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

open Matrix
open PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.EllProp

/- English proof (translation)
Simplify using `only [twConj, map_mul]`. Use `group`.
-/
theorem twConj_twConj {G : Type*} [Group G] (θ : Monoid.End G) (x g d : G) :
    twConj θ x (twConj θ g d) = twConj θ (g * x) d := by
  simp only [twConj, map_mul]
  group

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image, twConj_twConj]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨g * x, h, by group⟩`.

Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`.
-/
theorem orbit_preimage_eq {G : Type*} [Group G] (θ : Monoid.End G) (g d : G) (C : Set G) :
    {x | twConj θ x (twConj θ g d) ∈ C} = (fun y => g⁻¹ * y) '' {y | twConj θ y d ∈ C} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, twConj_twConj]
  constructor
  · intro h
    exact ⟨g * x, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/- English proof (translation)
Introduce `hD hP _ n d hd C hC`. Take `⟨g, d', z, h1, h2, h3, rfl⟩` from `hD n d hd`. Rewrite using `[orbit_preimage_eq]`. Conclude with `(hP n d' z h1 h2 h3 C hC).image (continuous_const.mul continuous_id)`.
-/
theorem ellProperOf : EllProperOf := by
  intro hD hP _ n d hd C hC
  obtain ⟨g, d', z, h1, h2, h3, rfl⟩ := hD n d hd
  rw [orbit_preimage_eq]
  exact (hP n d' z h1 h2 h3 C hC).image (continuous_const.mul continuous_id)

end GlobalTheory.CompanionTheory.EllProp

import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.SteinFibre

noncomputable def under {X : Scheme.{0}} (z : X) : Ideal Γ(X, ⊤) :=
  Ideal.comap (X.presheaf.germ ⊤ z trivial).hom (IsLocalRing.maximalIdeal (X.presheaf.stalk z))

/- English proof (translation)
Simplify using `only [under, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.
-/
theorem mem_under_iff {X : Scheme.{0}} (z : X) (a : Γ(X, ⊤)) :
    a ∈ under z ↔ ¬ IsUnit (X.presheaf.germ ⊤ z trivial a) := by
  simp only [under, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

instance under_isPrime {X : Scheme.{0}} (z : X) : (under z).IsPrime :=
  Ideal.comap_isPrime _ _

/- English proof (translation)
Introduce `a ha`. Rewrite `ha`, the goal using `[mem_under_iff]`. Introduce `hu`. Apply `ha` to reduce the goal to its premises. Establish `e` using `X.presheaf.germ_stalkSpecializes (U := ⊤) trivial h`.

Rewrite using `[← e, CommRingCat.comp_apply]`. Conclude with `hu.map (X.presheaf.stalkSpecializes h).hom`.
-/
theorem under_le_of_specializes {X : Scheme.{0}} {z x : X} (h : z ⤳ x) : under z ≤ under x := by
  intro a ha
  rw [mem_under_iff] at ha ⊢
  intro hu
  apply ha
  have e := X.presheaf.germ_stalkSpecializes (U := ⊤) trivial h
  rw [← e, CommRingCat.comp_apply]
  exact hu.map (X.presheaf.stalkSpecializes h).hom

/- English proof (translation)
Establish `hu : IsUnit (X.presheaf.germ ⊤ z trivial a)`. Assume the negation of the conclusion as `h`. Establish `: a ∈ under z` using `(mem_under_iff z a).2 h`. Rewrite `this` using `[hz]`. Conclude with `ha this`.

Establish `hzV : z ∈ X.basicOpen a` using `(X.mem_basicOpen a z trivial).2 hu`. Use `haveI : Nonempty (X.basicOpen a) := ⟨⟨z, hzV⟩⟩`. Establish `h1` using `Scheme.ord_of_isUnit (U := X.basicOpen a) (f := X.presheaf.map (homOfLE le_top).op a) (X.toRingedSpace.isUnit_res_basicOpen a) hzV`. Rewrite using `[← h1]`. Use `congr 1`.

Conclude with `(X.presheaf.germ_res_apply (homOfLE le_top) _ _ a).symm`.
-/
theorem ord_eq_zero_of_under_eq_bot {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (z : X)
    (a : Γ(X, ⊤)) (hz : under z = ⊥) (ha : a ≠ 0) :
    Scheme.ord (algebraMap Γ(X, ⊤) X.functionField a) z = 0 := by
  have hu : IsUnit (X.presheaf.germ ⊤ z trivial a) := by
    by_contra h
    have : a ∈ under z := (mem_under_iff z a).2 h
    rw [hz] at this
    exact ha this
  have hzV : z ∈ X.basicOpen a := (X.mem_basicOpen a z trivial).2 hu
  haveI : Nonempty (X.basicOpen a) := ⟨⟨z, hzV⟩⟩
  have h1 := Scheme.ord_of_isUnit (U := X.basicOpen a) (f := X.presheaf.map (homOfLE le_top).op a)
    (X.toRingedSpace.isUnit_res_basicOpen a) hzV
  rw [← h1]
  congr 1
  exact (X.presheaf.germ_res_apply (homOfLE le_top) _ _ a).symm

end GlobalTheory.SteinFibre

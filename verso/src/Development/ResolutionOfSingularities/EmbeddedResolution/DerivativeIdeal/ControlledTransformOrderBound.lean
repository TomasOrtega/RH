import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Proceed by induction on `a using ENat.recTopCoe with`. Consider the case `top`. Use `iff_of_false ?_ ?_` and prove the remaining obligations. Introduce `h`. Establish `h1 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞)` using `le_trans le_top h`.

Establish `h2 : m + 1 ≤ m` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers. Conclude with `fun h => h le_top`. Consider the case `coe n`. Prove the components needed by the constructor for the conclusion.

Introduce `h h'`. Establish `h1 : n ≤ m` using `by exact_mod_cast h`. Establish `h2 : m + 1 ≤ n` using `by exact_mod_cast h'`. Use linear arithmetic over natural numbers and integers. Introduce `h`.

Establish `h2 : n ≤ m`. Assume the negation of the conclusion as `hc`. Conclude with `h (by exact_mod_cast (by omega : m + 1 ≤ n))`. Conclude with `h2` after adjusting the coercions.
-/
private theorem le_natCast_iff_not_succ_le (a : ℕ∞) (m : ℕ) :
    a ≤ (m : ℕ∞) ↔ ¬ ((m + 1 : ℕ) : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top =>
      refine iff_of_false ?_ ?_
      · intro h
        have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans le_top h
        have h2 : m + 1 ≤ m := by exact_mod_cast h1
        omega
      · exact fun h => h le_top
  | coe n =>
      constructor
      · intro h h'
        have h1 : n ≤ m := by exact_mod_cast h
        have h2 : m + 1 ≤ n := by exact_mod_cast h'
        omega
      · intro h
        have h2 : n ≤ m := by
          by_contra hc
          exact h (by exact_mod_cast (by omega : m + 1 ≤ n))
        exact_mod_cast h2

/- English proof (translation)
Rewrite using `[mem_orderAtLeastLocus_iff]`. Conclude with `le_natCast_iff_not_succ_le (orderAt I x) m`.
-/
theorem orderAt_le_iff_notMem_orderAtLeastLocus {X : Scheme.{u}} (I : X.IdealSheafData) (m : ℕ)
    (x : X) :
    orderAt I x ≤ (m : ℕ∞) ↔ x ∉ orderAtLeastLocus I (m + 1) := by
  rw [mem_orderAtLeastLocus_iff]
  exact le_natCast_iff_not_succ_le (orderAt I x) m

/- English proof (translation)
Establish `h0` using `support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I (m := m + 1) (hm := by omega)`. Rewrite `h0` using `[Nat.add_sub_cancel]`. Establish `hiff : x ∈ (derivIdealSheafIterate k p m I).support ↔ x ∈ orderAtLeastLocus I (m + 1)`. Rewrite using `[← SetLike.mem_coe, h0]`. Rewrite using `[orderAt_le_iff_notMem_orderAtLeastLocus, hiff]`.
-/
theorem notMem_support_derivIdealSheafIterate_iff_orderAt_le (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) (m : ℕ) (x : X) :
    x ∉ (derivIdealSheafIterate k p m I).support ↔ orderAt I x ≤ (m : ℕ∞) := by
  have h0 := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I (m := m + 1) (hm := by omega)
  rw [Nat.add_sub_cancel] at h0
  have hiff : x ∈ (derivIdealSheafIterate k p m I).support ↔ x ∈ orderAtLeastLocus I (m + 1) := by
    rw [← SetLike.mem_coe, h0]
  rw [orderAt_le_iff_notMem_orderAtLeastLocus, hiff]

/- English proof (translation)
Rewrite using `[← notMem_support_derivIdealSheafIterate_iff_orderAt_le k p I m x, mem_support_iff_stalkIdeal_ne_top]`. Simplify using the standard rewrite rules.
-/
theorem stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) (m : ℕ) (x : X) :
    stalkIdeal (derivIdealSheafIterate k p m I) x = ⊤ ↔ orderAt I x ≤ (m : ℕ∞) := by
  rw [← notMem_support_derivIdealSheafIterate_iff_orderAt_le k p I m x,
    mem_support_iff_stalkIdeal_ne_top]
  simp

/- English proof (translation)
Substitute `hx₁` using the available equality. Establish `hsm : AlgebraicGeometry.Smooth (π ≫ p)` using `smooth_comp_of_isBlowupAlongIdealSheaf hZ hπ`. Establish `h1 : stalkIdeal (derivIdealSheafIterate k p m I) (π.base x₁) = ⊤` using `(stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le k p I m (π.base x₁)).2 hz`. Establish `h2 : (derivIdealSheafIterate k p m I).comap π ≤ Blowup.exceptionalIdeal π Z ^ (m - m) * derivIdealSheafIterate k (π ≫ p) m (controlledTransform π Z I m hπ hI)` using `comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ I m hI m le_rfl`. Rewrite `h2` using `[Nat.sub_self, pow_zero, one_mul]`.

Establish `h3 : stalkIdeal ((derivIdealSheafIterate k p m I).comap π) x₁ = ⊤`. Rewrite using `[stalkIdeal_comap, h1, Ideal.map_top]`. Establish `h4` using `stalkIdeal_mono h2 x₁`. Rewrite `h4` using `[h3, top_le_iff]`. Conclude with `(stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le k (π ≫ p) (controlledTransform π Z I m hπ hI) m x₁).1 h4`.
-/
theorem orderAt_controlledTransform_le (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) (z : X) (hz : orderAt I z ≤ (m : ℕ∞)) (x₁ : X₁)
    (hx₁ : π.base x₁ = z) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) := by
  subst hx₁
  have hsm : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hZ hπ
  have h1 : stalkIdeal (derivIdealSheafIterate k p m I) (π.base x₁) = ⊤ :=
    (stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le k p I m (π.base x₁)).2 hz
  have h2 : (derivIdealSheafIterate k p m I).comap π ≤
      Blowup.exceptionalIdeal π Z ^ (m - m) *
        derivIdealSheafIterate k (π ≫ p) m (controlledTransform π Z I m hπ hI) :=
    comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ I m hI m le_rfl
  rw [Nat.sub_self, pow_zero, one_mul] at h2
  have h3 : stalkIdeal ((derivIdealSheafIterate k p m I).comap π) x₁ = ⊤ := by
    rw [stalkIdeal_comap, h1, Ideal.map_top]
  have h4 := stalkIdeal_mono h2 x₁
  rw [h3, top_le_iff] at h4
  exact (stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le k (π ≫ p)
    (controlledTransform π Z I m hπ hI) m x₁).1 h4

/- English proof (translation)
The claim follows from `orderAt_controlledTransform_le k p π Z E hZ hπ I m hI (π.base x₁) hx₁ x₁ rfl`.
-/
theorem orderAt_controlledTransform_le_of_orderAt_image_le (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) (x₁ : X₁) (hx₁ : orderAt I (π.base x₁) ≤ (m : ℕ∞)) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) :=
  orderAt_controlledTransform_le k p π Z E hZ hπ I m hI (π.base x₁) hx₁ x₁ rfl

/- English proof (translation)
The claim follows from `orderAt_controlledTransform_le k p π Z E hZ hπ I m hI z ((orderAt_le_iff_notMem_orderAtLeastLocus I m z).2 hz) x₁ hx₁`.
-/
theorem orderAt_controlledTransform_le_of_not_succ_le (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) (z : X) (hz : ¬ (((m + 1 : ℕ) : ℕ∞) ≤ orderAt I z)) (x₁ : X₁)
    (hx₁ : π.base x₁ = z) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) :=
  orderAt_controlledTransform_le k p π Z E hZ hπ I m hI z
    ((orderAt_le_iff_notMem_orderAtLeastLocus I m z).2 hz) x₁ hx₁

/- English proof (translation)
The claim follows from `orderAt_controlledTransform_le k p π Z E hZ hπ I m hI (π.base x₁) (h (π.base x₁)) x₁ rfl`.
-/
theorem orderAt_controlledTransform_le_of_forall_le (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) (h : ∀ x : X, orderAt I x ≤ (m : ℕ∞)) (x₁ : X₁) :
    orderAt (controlledTransform π Z I m hπ hI) x₁ ≤ (m : ℕ∞) :=
  orderAt_controlledTransform_le k p π Z E hZ hπ I m hI (π.base x₁) (h (π.base x₁)) x₁ rfl

/- English proof (translation)
Introduce `x₁ hx₁`. Assume the negation of the conclusion as `hz`. Rewrite `hz` using `[Set.mem_preimage, mem_orderAtLeastLocus_iff]`. Establish `h` using `orderAt_controlledTransform_le_of_not_succ_le k p π Z E hZ hπ I m hI (π.base x₁) hz x₁ rfl`. Rewrite `hx₁` using `[mem_orderAtLeastLocus_iff]`.

Establish `hle : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞)` using `le_trans hx₁ h`. Establish `hcontra : m + 1 ≤ m` using `by exact_mod_cast hle`. Use linear arithmetic over natural numbers and integers.
-/
theorem orderAtLeastLocus_controlledTransform_subset_preimage (k : Type u) [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁] (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (I : X.IdealSheafData) (m : ℕ)
    (hI : I ≤ Z ^ m) :
    orderAtLeastLocus (controlledTransform π Z I m hπ hI) (m + 1) ⊆
      ⇑π.base ⁻¹' orderAtLeastLocus I (m + 1) := by
  intro x₁ hx₁
  by_contra hz
  rw [Set.mem_preimage, mem_orderAtLeastLocus_iff] at hz
  have h := orderAt_controlledTransform_le_of_not_succ_le k p π Z E hZ hπ I m hI
    (π.base x₁) hz x₁ rfl
  rw [mem_orderAtLeastLocus_iff] at hx₁
  have hle : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans hx₁ h
  have hcontra : m + 1 ≤ m := by exact_mod_cast hle
  omega

end FunctorialResolution.EmbeddedResolution

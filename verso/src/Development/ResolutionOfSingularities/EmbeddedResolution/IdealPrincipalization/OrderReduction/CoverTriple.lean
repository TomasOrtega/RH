import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

/- English proof (translation)
Establish `h` using `d.boundary_append L ([] : List X.IdealSheafData) i`. Rewrite `h` using `[List.append_nil]`. Then use the resulting hypothesis.
-/
theorem boundary_eq_map_iteratedStrictTransform_append {X : Scheme.{u}} (d : BlowupSequenceData X)
    (L : List X.IdealSheafData) (i : ℕ) :
    d.boundaryFrom L i = L.map (d.iteratedStrictTransform i) ++ d.boundaryFrom ([] : List X.IdealSheafData) i := by
  have h := d.boundary_append L ([] : List X.IdealSheafData) i
  rwa [List.append_nil] at h

/- English proof (translation)
Establish `key : ∀ s, s ≤ d.length → ((d.iteratedStrictTransform s D).support : Set ↥(d.obj s)) ⊆ ((K s).support : Set ↥(d.obj s))`. Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `_ x hx`.

Establish `hz : K 0 = d.iteratedStrictTransform 0 D` using `by rw [h0, iteratedStrictTransform_zero]`. Rewrite using `[hz]`. Conclude with `hx`. Consider the case `succ n ih`. Introduce `hn`.

Establish `hlt : n < d.length` using `hn`. Establish `hle` using `ih (Nat.le_of_lt hlt)`. Break down `hstep n hlt with hh | hh` into its components or cases. Rewrite using `[hh, iteratedStrictTransform_succ]`. Conclude with `hsupp n hlt (d.iteratedStrictTransform n D) (K n) hle`.

Rewrite using `[hh, iteratedStrictTransform_succ]`. Introduce `y hy`. Establish `h1` using `support_strictTransform_subset_preimage (d.map n) (d.center n) (d.iteratedStrictTransform n D) hy`. Establish `h2` using `hle h1`. Conclude with `(one_le_orderAt_iff_mem_support ((K n).comap (d.map n)) y).1 (le_trans ((one_le_orderAt_iff_mem_support (K n) _).2 h2) (orderAt_le_orderAt_comap (d.map n) (K n) y))`.

Conclude with `key t ht`.
-/
private theorem support_iteratedStrictTransform_subset_of_strictTransform_mono {X : Scheme.{u}} (d : BlowupSequenceData X)
    (D : X.IdealSheafData)
    (K : ∀ t : ℕ, (d.obj t).IdealSheafData) (h0 : K 0 = D.comap d.isoZero.hom)
    (hstep : ∀ t, t < d.length →
      K (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (K t) ∨
        K (t + 1) = (K t).comap (d.map t))
    (hsupp : ∀ (i : ℕ), i < d.length → ∀ (A B : (d.obj i).IdealSheafData),
      ((A.support : Set ↥(d.obj i)) ⊆ (B.support : Set ↥(d.obj i))) →
      ((Blowup.strictTransform (d.map i) (d.center i) A).support : Set ↥(d.obj (i + 1))) ⊆
        ((Blowup.strictTransform (d.map i) (d.center i) B).support : Set ↥(d.obj (i + 1))))
    (t : ℕ) (ht : t ≤ d.length) :
    ((d.iteratedStrictTransform t D).support : Set ↥(d.obj t)) ⊆ ((K t).support : Set ↥(d.obj t)) := by
  have key : ∀ s, s ≤ d.length →
      ((d.iteratedStrictTransform s D).support : Set ↥(d.obj s)) ⊆ ((K s).support : Set ↥(d.obj s)) := by
    intro s
    induction s with
    | zero =>
        intro _ x hx
        have hz : K 0 = d.iteratedStrictTransform 0 D := by rw [h0, iteratedStrictTransform_zero]
        rw [hz]
        exact hx
    | succ n ih =>
        intro hn
        have hlt : n < d.length := hn
        have hle := ih (Nat.le_of_lt hlt)
        rcases hstep n hlt with hh | hh
        · rw [hh, iteratedStrictTransform_succ]
          exact hsupp n hlt (d.iteratedStrictTransform n D) (K n) hle
        · rw [hh, iteratedStrictTransform_succ]
          intro y hy
          have h1 := support_strictTransform_subset_preimage (d.map n) (d.center n)
            (d.iteratedStrictTransform n D) hy
          have h2 := hle h1
          exact (one_le_orderAt_iff_mem_support ((K n).comap (d.map n)) y).1
            (le_trans ((one_le_orderAt_iff_mem_support (K n) _).2 h2)
              (orderAt_le_orderAt_comap (d.map n) (K n) y))
  exact key t ht

/- English proof (translation)
Use `support_iteratedStrictTransform_subset_of_strictTransform_mono d D K h0 hstep ?_ t ht` and prove the remaining obligations. Introduce `i hi A B hAB`. Use `hN (i + 1) hi` as an intermediate fact. Use `FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian (d.map i) (d.center i) A` as an intermediate fact. Use `FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian (d.map i) (d.center i) B` as an intermediate fact.

Rewrite using `[support_strictTransform_eq_closure_preimage, support_strictTransform_eq_closure_preimage]`. Conclude with `closure_mono (Set.sdiff_subset_sdiff_left (Set.preimage_mono hAB))`.
-/
theorem support_iteratedStrictTransform_subset_support {X : Scheme.{u}} (d : BlowupSequenceData X)
    (hN : ∀ i ≤ d.length, AlgebraicGeometry.IsLocallyNoetherian (d.obj i))
    (D : X.IdealSheafData) (K : ∀ t : ℕ, (d.obj t).IdealSheafData)
    (h0 : K 0 = D.comap d.isoZero.hom)
    (hstep : ∀ t, t < d.length →
      K (t + 1) = Blowup.strictTransform (d.map t) (d.center t) (K t) ∨
        K (t + 1) = (K t).comap (d.map t))
    (t : ℕ) (ht : t ≤ d.length) :
    ((d.iteratedStrictTransform t D).support : Set ↥(d.obj t)) ⊆ ((K t).support : Set ↥(d.obj t)) := by
  refine support_iteratedStrictTransform_subset_of_strictTransform_mono d D K h0 hstep ?_ t ht
  intro i hi A B hAB
  have := hN (i + 1) hi
  have := FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian (d.map i) (d.center i) A
  have := FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian (d.map i) (d.center i) B
  rw [support_strictTransform_eq_closure_preimage, support_strictTransform_eq_closure_preimage]
  exact closure_mono (Set.sdiff_subset_sdiff_left (Set.preimage_mono hAB))

end BlowupSequenceData

namespace BoundarySeparationByMaxContact

/- English proof (translation)
Establish `hlt : m - 1 < m` using `by omega`. Establish `h` using `orderAtLeastLocus_derivIdealSheafIterate k p A (r := m - 1) (m := m) hlt`. Rewrite `h` using `[show m - (m - 1) = 1 from by omega, hempty]`. Use `(Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).2 ?_` and prove the remaining obligations. Use extensionality with `y`.

Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce `hy`. Establish `hy' : y ∈ orderAtLeastLocus (derivIdealSheafIterate k p (m - 1) A) 1`. Use `(mem_orderAtLeastLocus_one_iff _ y).2 ?_` and prove the remaining obligations. Rewrite using `[← maxContactIdeal_eq_derivIdealSheafIterate]`.

Conclude with `hy`. Rewrite `hy'` using `[h]`. Conclude with `hy'`.
-/
private theorem maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (A : P.IdealSheafData) (m : ℕ) (hm : 1 ≤ m)
    (hempty : orderAtLeastLocus A m = ∅) : maxContactIdeal k p A m = ⊤ := by
  have hlt : m - 1 < m := by omega
  have h := orderAtLeastLocus_derivIdealSheafIterate k p A (r := m - 1) (m := m) hlt
  rw [show m - (m - 1) = 1 from by omega, hempty] at h
  refine (Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).2 ?_
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have hy' : y ∈ orderAtLeastLocus (derivIdealSheafIterate k p (m - 1) A) 1 := by
    refine (mem_orderAtLeastLocus_one_iff _ y).2 ?_
    rw [← maxContactIdeal_eq_derivIdealSheafIterate]
    exact hy
  rw [h] at hy'
  exact hy'

/- English proof (translation)
Unfold `FunctorialResolution.EmbeddedResolution.balancedTunedSheaf FunctorialResolution.EmbeddedResolution.tunedSheaf`. Conclude with `le_iSup (fun d : {e : ℕ → ℕ // tuningExponent μ ≤ ∑ j ∈ Finset.range μ, (μ - j) * e j} => (List.map (fun j => derivIdealSheafIterate k p j A ^ d.1 j) (List.range μ)).prod) ⟨c, hc⟩`.
-/
private theorem prod_derivIdealSheafIter_pow_le_balancedTunedSheaf (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (A : P.IdealSheafData) (μ : ℕ) (c : ℕ → ℕ)
    (hc : tuningExponent μ ≤ ∑ j ∈ Finset.range μ, (μ - j) * c j) :
    (List.map (fun j => derivIdealSheafIterate k p j A ^ c j) (List.range μ)).prod ≤
      balancedTunedSheaf k p A μ := by
  unfold FunctorialResolution.EmbeddedResolution.balancedTunedSheaf FunctorialResolution.EmbeddedResolution.tunedSheaf
  exact le_iSup
    (fun d : {e : ℕ → ℕ // tuningExponent μ ≤ ∑ j ∈ Finset.range μ, (μ - j) * e j} =>
      (List.map (fun j => derivIdealSheafIterate k p j A ^ d.1 j) (List.range μ)).prod) ⟨c, hc⟩

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `_`. Establish `h0` using `stalkIdeal_pow (⊤ : X.IdealSheafData) 0 x`.

Rewrite `h0` using `[pow_zero, pow_zero]`. Rewrite using `[List.prod_nil, h0, Ideal.one_eq_top]`. Consider the case `cons I L ih`. Introduce `h`. Rewrite using `[List.prod_cons, stalkIdeal_mul, h I (by simp), ih (fun J hJ => h J (by simp [hJ]))]`.

Simplify using the standard rewrite rules.
-/
private theorem stalkIdeal_prod_eq_top {X : Scheme.{u}} (x : ↥X) :
    ∀ L : List X.IdealSheafData, (∀ I ∈ L, stalkIdeal I x = ⊤) → stalkIdeal L.prod x = ⊤ := by
  intro L
  induction L with
  | nil =>
      intro _
      have h0 := stalkIdeal_pow (⊤ : X.IdealSheafData) 0 x
      rw [pow_zero, pow_zero] at h0
      rw [List.prod_nil, h0, Ideal.one_eq_top]
  | cons I L ih =>
      intro h
      rw [List.prod_cons, stalkIdeal_mul, h I (by simp),
        ih (fun J hJ => h J (by simp [hJ]))]
      simp

/- English proof (translation)
Establish `hE : 1 ≤ tuningExponent μ` using `one_le_tuningExponent μ`. Establish `hmc : maxContactIdeal k p A μ = ⊤` using `maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty k p A μ hμ hempty`. Establish `hstalk : ∀ y : ↥P, stalkIdeal (derivIdealSheafIterate k p (μ - 1) A) y = ⊤`. Introduce `y`. Rewrite using `[← maxContactIdeal_eq_derivIdealSheafIterate, hmc]`.

Conclude with `stalkIdeal_top y`. Establish `hsum : (∑ j ∈ Finset.range μ, (μ - j) * (if j = μ - 1 then tuningExponent μ else 0)) = tuningExponent μ`. Rewrite using `[Finset.sum_eq_single (μ - 1)]`. Simplify using `[show μ - (μ - 1) = 1 from by omega]`. Introduce `b _ hb`.

Simplify using `[hb]`. Introduce `hcon`. Conclude with `absurd (Finset.mem_range.mpr (show μ - 1 < μ from by omega)) hcon`. Establish `hle : (List.map (fun j => derivIdealSheafIterate k p j A ^ (if j = μ - 1 then tuningExponent μ else 0)) (List.range μ)).prod ≤ balancedTunedSheaf k p A μ` using `prod_derivIdealSheafIter_pow_le_balancedTunedSheaf k p A μ (fun j => if j = μ - 1 then tuningExponent μ else 0) (le_of_eq hsum.symm)`. Use extensionality with `x`.

Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce `hx`. Establish `hprod : stalkIdeal (List.map (fun j => derivIdealSheafIterate k p j A ^ (if j = μ - 1 then tuningExponent μ else 0)) (List.range μ)).prod x = ⊤`. Use `stalkIdeal_prod_eq_top x _ ?_` and prove the remaining obligations. Introduce `I hI`.

Take `⟨j, _, rfl⟩` from `List.mem_map.mp hI`. Simplify using `only [stalkIdeal_pow]`. Use `split_ifs with hjj`. Rewrite using `[hjj, hstalk x, ← Ideal.one_eq_top, one_pow]`. Rewrite using `[pow_zero]`.

Conclude with `Ideal.one_eq_top`. Establish `hmono` using `stalkIdeal_mono hle x`. Rewrite `hmono` using `[hprod]`. Establish `htop : stalkIdeal (balancedTunedSheaf k p A μ) x = ⊤` using `top_le_iff.mp hmono`. Establish `hx1 : x ∈ orderAtLeastLocus (balancedTunedSheaf k p A μ) 1` using `orderAtLeastLocus_subset_of_le (balancedTunedSheaf k p A μ) hE hx`.

Establish `hxs : x ∈ (balancedTunedSheaf k p A μ).support` using `(mem_orderAtLeastLocus_one_iff _ x).1 hx1`. Conclude with `((mem_support_iff_stalkIdeal_ne_top _ x).1 hxs) htop`.
-/
private theorem orderAtLeastLocus_balancedTunedSheaf_eq_empty (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (A : P.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (hempty : orderAtLeastLocus A μ = ∅) : orderAtLeastLocus (balancedTunedSheaf k p A μ) (tuningExponent μ) = ∅ := by
  have hE : 1 ≤ tuningExponent μ := one_le_tuningExponent μ
  have hmc : maxContactIdeal k p A μ = ⊤ :=
    maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty k p A μ hμ hempty
  have hstalk : ∀ y : ↥P, stalkIdeal (derivIdealSheafIterate k p (μ - 1) A) y = ⊤ := by
    intro y
    rw [← maxContactIdeal_eq_derivIdealSheafIterate, hmc]
    exact stalkIdeal_top y
  have hsum : (∑ j ∈ Finset.range μ, (μ - j) * (if j = μ - 1 then tuningExponent μ else 0))
      = tuningExponent μ := by
    rw [Finset.sum_eq_single (μ - 1)]
    · simp [show μ - (μ - 1) = 1 from by omega]
    · intro b _ hb
      simp [hb]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (show μ - 1 < μ from by omega)) hcon
  have hle : (List.map
      (fun j => derivIdealSheafIterate k p j A ^ (if j = μ - 1 then tuningExponent μ else 0))
      (List.range μ)).prod ≤ balancedTunedSheaf k p A μ :=
    prod_derivIdealSheafIter_pow_le_balancedTunedSheaf k p A μ
      (fun j => if j = μ - 1 then tuningExponent μ else 0) (le_of_eq hsum.symm)
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hprod : stalkIdeal (List.map
      (fun j => derivIdealSheafIterate k p j A ^ (if j = μ - 1 then tuningExponent μ else 0))
      (List.range μ)).prod x = ⊤ := by
    refine stalkIdeal_prod_eq_top x _ ?_
    intro I hI
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hI
    simp only [stalkIdeal_pow]
    split_ifs with hjj
    · rw [hjj, hstalk x, ← Ideal.one_eq_top, one_pow]
    · rw [pow_zero]
      exact Ideal.one_eq_top
  have hmono := stalkIdeal_mono hle x
  rw [hprod] at hmono
  have htop : stalkIdeal (balancedTunedSheaf k p A μ) x = ⊤ := top_le_iff.mp hmono
  have hx1 : x ∈ orderAtLeastLocus (balancedTunedSheaf k p A μ) 1 :=
    orderAtLeastLocus_subset_of_le (balancedTunedSheaf k p A μ) hE hx
  have hxs : x ∈ (balancedTunedSheaf k p A μ).support := (mem_orderAtLeastLocus_one_iff _ x).1 hx1
  exact ((mem_support_iff_stalkIdeal_ne_top _ x).1 hxs) htop

/- English proof (translation)
Distinguish the cases in `hne : (orderAtLeastLocus A μ).Nonempty`. Establish `hmax : MaxOrderEq A μ` using `⟨(orderLE_iff A μ).2 hord, hne⟩`. Establish `hcs : orderAtLeastLocus (balancedTunedSheaf k p A μ) (tuningExponent μ) = orderAtLeastLocus A μ` using `(hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE k P p A μ hμ hmax (tuningExponent μ) (one_le_tuningExponent μ)).1`. Establish `hmi : maxContactIdeal k p (balancedTunedSheaf k p A μ) (tuningExponent μ) = maxContactIdeal k p A μ` using `hstar.tuning.derivIdealSheafIter_pred_tunedSheaf k P p A μ hμ hmax (tuningExponent μ) (one_le_tuningExponent μ)`. Introduce `x`.

Take `⟨U, hUaff, hxU, hcase⟩` from `hH x`. Use `⟨U, hUaff, hxU, ?_⟩` and prove the remaining obligations. Break down `hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmcc⟩` into its components or cases. Use `Or.inl ⟨?_, htop⟩` and prove the remaining obligations. Rewrite using `[hcs]`.

Conclude with `hdisj`. Use `Or.inr ⟨n, c, j, hcoord, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[hmi]`. Conclude with `hmcc i`.

Rewrite `hne` using `[Set.not_nonempty_iff_eq_empty]`. Establish `hcs : orderAtLeastLocus (balancedTunedSheaf k p A μ) (tuningExponent μ) = ∅` using `orderAtLeastLocus_balancedTunedSheaf_eq_empty k p A μ hμ hne`. Establish `h1 : maxContactIdeal k p A μ = ⊤` using `maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty k p A μ hμ hne`. Establish `h2 : maxContactIdeal k p (balancedTunedSheaf k p A μ) (tuningExponent μ) = ⊤` using `maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty k p (balancedTunedSheaf k p A μ) (tuningExponent μ) (one_le_tuningExponent μ) hcs`. Introduce `x`.

Take `⟨U, hUaff, hxU, hcase⟩` from `hH x`. Use `⟨U, hUaff, hxU, ?_⟩` and prove the remaining obligations. Break down `hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmcc⟩` into its components or cases. Use `Or.inl ⟨?_, htop⟩` and prove the remaining obligations. Rewrite using `[hcs]`.

Conclude with `Set.disjoint_left.2 (fun y hy => ((Set.mem_empty_iff_false y).mp hy).elim)`. Use `Or.inr ⟨n, c, j, hcoord, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[h2, ← h1]`. Conclude with `hmcc i`.
-/
theorem isMaxContactHypersurface_balancedTunedSheaf (hstar : MaxContactCoverProperties.{u}) (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (A : P.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ)
    (hord : ∀ x : ↥P, orderAt A x ≤ (μ : ℕ∞)) (H : P.IdealSheafData)
    (hH : IsMaxContactHypersurface k p A μ H) :
    IsMaxContactHypersurface k p (balancedTunedSheaf k p A μ) (tuningExponent μ) H := by
  by_cases hne : (orderAtLeastLocus A μ).Nonempty
  · have hmax : MaxOrderEq A μ := ⟨(orderLE_iff A μ).2 hord, hne⟩
    have hcs : orderAtLeastLocus (balancedTunedSheaf k p A μ) (tuningExponent μ) = orderAtLeastLocus A μ :=
      (hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE k P p A μ hμ hmax (tuningExponent μ)
        (one_le_tuningExponent μ)).1
    have hmi : maxContactIdeal k p (balancedTunedSheaf k p A μ) (tuningExponent μ) = maxContactIdeal k p A μ :=
      hstar.tuning.derivIdealSheafIter_pred_tunedSheaf k P p A μ hμ hmax (tuningExponent μ)
        (one_le_tuningExponent μ)
    intro x
    obtain ⟨U, hUaff, hxU, hcase⟩ := hH x
    refine ⟨U, hUaff, hxU, ?_⟩
    rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmcc⟩
    · refine Or.inl ⟨?_, htop⟩
      rw [hcs]
      exact hdisj
    · refine Or.inr ⟨n, c, j, hcoord, ?_⟩
      intro i
      rw [hmi]
      exact hmcc i
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hcs : orderAtLeastLocus (balancedTunedSheaf k p A μ) (tuningExponent μ) = ∅ :=
      orderAtLeastLocus_balancedTunedSheaf_eq_empty k p A μ hμ hne
    have h1 : maxContactIdeal k p A μ = ⊤ :=
      maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty k p A μ hμ hne
    have h2 : maxContactIdeal k p (balancedTunedSheaf k p A μ) (tuningExponent μ) = ⊤ :=
      maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty k p (balancedTunedSheaf k p A μ) (tuningExponent μ)
        (one_le_tuningExponent μ) hcs
    intro x
    obtain ⟨U, hUaff, hxU, hcase⟩ := hH x
    refine ⟨U, hUaff, hxU, ?_⟩
    rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmcc⟩
    · refine Or.inl ⟨?_, htop⟩
      rw [hcs]
      exact Set.disjoint_left.2 (fun y hy => ((Set.mem_empty_iff_false y).mp hy).elim)
    · refine Or.inr ⟨n, c, j, hcoord, ?_⟩
      intro i
      rw [h2, ← h1]
      exact hmcc i

/- English proof (translation)
Establish `h` using `(hstar.valid_level S hV s.toMarkedSequenceOfBlowups i hi).locallyOfFiniteType`. Simplify using `at h`. Use `with_unfolding_all exact h`.
-/
theorem locallyOfFiniteType_projectionToBase_comp (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (i : ℕ) (hi : i ≤ s.length) :
    AlgebraicGeometry.LocallyOfFiniteType (s.proj i ≫ S.structMap) := by
  have h := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups i hi).locallyOfFiniteType
  simp at h
  with_unfolding_all exact h

/- English proof (translation)
Establish `h` using `(hstar.valid_level S hV s.toMarkedSequenceOfBlowups i hi).smooth`. Simplify using `at h`. Use `with_unfolding_all exact h`.
-/
theorem smooth_projectionToBase_comp (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (i : ℕ) (hi : i ≤ s.length) :
    AlgebraicGeometry.Smooth (s.proj i ≫ S.structMap) := by
  have h := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups i hi).smooth
  simp at h
  with_unfolding_all exact h

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => rewrite [MaxContactReduction.iteratedStrictTransform_zero, BlowupSequenceData.iteratedStrictTransform_zero]`. Both sides reduce to the same expression. Consider the case `succ n ih => rewrite [MaxContactReduction.iteratedStrictTransform_succ, BlowupSequenceData.iteratedStrictTransform_succ, ih]`. Both sides reduce to the same expression.
-/
theorem iteratedStrictTransform_eq_toBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) (i : ℕ) :
    MaxContactReduction.iteratedStrictTransform s H i = s.toBlowupSequenceData.iteratedStrictTransform i H := by
  induction i with
  | zero =>
      rewrite [MaxContactReduction.iteratedStrictTransform_zero, BlowupSequenceData.iteratedStrictTransform_zero]
      rfl
  | succ n ih =>
      rewrite [MaxContactReduction.iteratedStrictTransform_succ, BlowupSequenceData.iteratedStrictTransform_succ, ih]
      rfl

/- English proof (translation)
Establish `hproj : u.proj 0 = u.isoZero.hom` using `u.proj_zero`. Establish `h` using `inStrictNormalCrossingPosition_comap_iso S.structMap u.isoZero [H] hH`. Rewrite using `[MaxContactReduction.iteratedStrictTransform_zero u H, hproj]`. Conclude with `h`.
-/
theorem inStrictNormalCrossingPosition_iteratedStrictTransform_zero (S : MarkedIdealWithBoundary.{u})
    (u : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (H : S.scheme.IdealSheafData)
    (hH : InStrictNormalCrossingPosition S.structMap [H]) :
    InStrictNormalCrossingPosition (u.proj 0 ≫ S.structMap) [MaxContactReduction.iteratedStrictTransform u H 0] := by
  have hproj : u.proj 0 = u.isoZero.hom := u.proj_zero
  have h := inStrictNormalCrossingPosition_comap_iso S.structMap u.isoZero [H] hH
  rw [MaxContactReduction.iteratedStrictTransform_zero u H, hproj]
  exact h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[List.range_succ, List.map_append, List.prod_append, ih]`. Simplify using `[hf (m + 1) (Nat.succ_ne_zero m)]`.
-/
private theorem prod_map_range_succ_eq_apply_zero {X : Scheme.{u}} (f : ℕ → X.IdealSheafData)
    (hf : ∀ j, j ≠ 0 → f j = 1) (n : ℕ) :
    (List.map f (List.range (n + 1))).prod = f 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih]
      simp [hf (m + 1) (Nat.succ_ne_zero m)]

/- English proof (translation)
Introduce `x hx`. Establish `hx' : stalkIdeal (A ^ e) x ≠ ⊤` using `(mem_support_iff_stalkIdeal_ne_top (A ^ e) x).1 hx`. Use `(mem_support_iff_stalkIdeal_ne_top A x).2 ?_` and prove the remaining obligations. Introduce `htop`. Conclude with `hx' (by rw [stalkIdeal_pow, htop, ← Ideal.one_eq_top, one_pow])`.
-/
private theorem support_pow_subset_support {X : Scheme.{u}} (A : X.IdealSheafData) (e : ℕ) :
    ((A ^ e).support : Set ↥X) ⊆ (A.support : Set ↥X) := by
  intro x hx
  have hx' : stalkIdeal (A ^ e) x ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top (A ^ e) x).1 hx
  refine (mem_support_iff_stalkIdeal_ne_top A x).2 ?_
  intro htop
  exact hx' (by rw [stalkIdeal_pow, htop, ← Ideal.one_eq_top, one_pow])

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n : ℕ, μ = n + 1` from `⟨μ - 1, by omega⟩`. Establish `hd0 : derivIdealSheafIterate k p 0 A = A` using `rfl`. Establish `hsum : (∑ j ∈ Finset.range (n + 1), ((n + 1) - j) * (if j = 0 then tuningExponent (n + 1) else 0)) = (n + 1) * tuningExponent (n + 1)`. Rewrite using `[Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Introduce `hcon`. Conclude with `absurd (Finset.mem_range.mpr (Nat.succ_pos n)) hcon`. Establish `hc : tuningExponent (n + 1) ≤ ∑ j ∈ Finset.range (n + 1), ((n + 1) - j) * (if j = 0 then tuningExponent (n + 1) else 0)`.

Rewrite using `[hsum]`. Combine the equalities or inequalities in the displayed calculation. Establish `hle` using `prod_derivIdealSheafIter_pow_le_balancedTunedSheaf k p A (n + 1) (fun j => if j = 0 then tuningExponent (n + 1) else 0) hc`. Establish `hf : ∀ j : ℕ, j ≠ 0 → derivIdealSheafIterate k p j A ^ (if j = 0 then tuningExponent (n + 1) else 0) = 1`. Introduce `j hj`.

Simplify using `[hj]`. Establish `hA : A ^ tuningExponent (n + 1) ≤ (List.map (fun j => derivIdealSheafIterate k p j A ^ (if j = 0 then tuningExponent (n + 1) else 0)) (List.range (n + 1))).prod`. Rewrite using `[prod_map_range_succ_eq_apply_zero (fun j => derivIdealSheafIterate k p j A ^ (if j = 0 then tuningExponent (n + 1) else 0)) hf n]`. Simplify using `[hd0]`. Conclude with `le_trans hA hle`.
-/
private theorem pow_tuningExponent_le_balancedTunedSheaf (k : Type u) [Field k] [CharZero k] {P : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (A : P.IdealSheafData) (μ : ℕ) (hμ : 1 ≤ μ) :
    A ^ tuningExponent μ ≤ balancedTunedSheaf k p A μ := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, μ = n + 1 := ⟨μ - 1, by omega⟩
  have hd0 : derivIdealSheafIterate k p 0 A = A := rfl
  have hsum : (∑ j ∈ Finset.range (n + 1),
      ((n + 1) - j) * (if j = 0 then tuningExponent (n + 1) else 0)) = (n + 1) * tuningExponent (n + 1) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) hcon
  have hc : tuningExponent (n + 1) ≤ ∑ j ∈ Finset.range (n + 1),
      ((n + 1) - j) * (if j = 0 then tuningExponent (n + 1) else 0) := by
    rw [hsum]
    calc tuningExponent (n + 1) = 1 * tuningExponent (n + 1) := (one_mul _).symm
      _ ≤ (n + 1) * tuningExponent (n + 1) :=
          Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le n)) (le_refl _)
  have hle := prod_derivIdealSheafIter_pow_le_balancedTunedSheaf k p A (n + 1)
    (fun j => if j = 0 then tuningExponent (n + 1) else 0) hc
  have hf : ∀ j : ℕ, j ≠ 0 →
      derivIdealSheafIterate k p j A ^ (if j = 0 then tuningExponent (n + 1) else 0) = 1 := by
    intro j hj
    simp [hj]
  have hA : A ^ tuningExponent (n + 1) ≤
      (List.map (fun j => derivIdealSheafIterate k p j A ^ (if j = 0 then tuningExponent (n + 1) else 0))
        (List.range (n + 1))).prod := by
    rw [prod_map_range_succ_eq_apply_zero
      (fun j => derivIdealSheafIterate k p j A ^ (if j = 0 then tuningExponent (n + 1) else 0)) hf n]
    simp [hd0]
  exact le_trans hA hle

/- English proof (translation)
Establish `hlev` using `hstar.valid_level S hV s.toMarkedSequenceOfBlowups s.length (le_refl s.length)`. Prove the components needed by the constructor for the conclusion. Use `case charZero => exact hV.charZero`. Use `case locallyOfFiniteType =>`. Rewrite using `[MaxContactCoverData.derivedTriple_structureMorphism]`.

Conclude with `hft`. Use `case one_le_mult =>`. Rewrite using `[MaxContactCoverData.derivedTriple_mult]`. Conclude with `one_le_tuningExponent S.mult`. Use `case quasiCompact =>`.

Establish `h` using `hlev.quasiCompact`. Rewrite using `[MaxContactCoverData.derivedTriple_structureMorphism]`. Simplify using `at h`. Use `with_unfolding_all exact h`. Use `case smooth =>`.

Rewrite using `[MaxContactCoverData.derivedTriple_structureMorphism]`. Conclude with `smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)`. Use `case snc =>`. Rewrite using `[MaxContactCoverData.derivedTriple_structureMorphism, MaxContactCoverData.derivedTriple_boundary]`. Conclude with `hsnc`.

Use `case nonzeroOnComponents =>`. Establish `hNZ` using `hlev.nonzeroOnComponents`. Establish `hsupp : ((LowerDimReductionPullback.tunedIdealAtLength S s hft).support : Set ↥(s.obj s.length)) ⊆ ((s.ideal s.length).support : Set ↥(s.obj s.length))`. Establish `: CharZero S.base` using `hV.charZero`. Establish `: AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap)` using `smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)`.

Use `hft` as an intermediate fact. Establish `hpow` using `pow_tuningExponent_le_balancedTunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult hV.one_le_mult`. Conclude with `Set.Subset.trans (Scheme.IdealSheafData.support_antitone hpow) (support_pow_subset_support (s.ideal s.length) (tuningExponent S.mult))`. Rewrite using `[LowerDimReductionPullback.ideal_derivedTriple]`. Unfold `FunctorialResolution.EmbeddedResolution.NonzeroOnComponents`.

Introduce `T hT hsub`. Conclude with `hNZ T hT (Set.Subset.trans hsub hsupp)`.
-/
theorem isAdmissible_derivedTriple (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hsnc : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap)
      (extra ++ (s.boundary s.length).drop keep)) :
    (MaxContactCoverData.derivedTriple S s hft extra keep).IsAdmissible := by
  have hlev := hstar.valid_level S hV s.toMarkedSequenceOfBlowups s.length (le_refl s.length)
  constructor
  case charZero => exact hV.charZero
  case locallyOfFiniteType =>
    rw [MaxContactCoverData.derivedTriple_structureMorphism]
    exact hft
  case one_le_mult =>
    rw [MaxContactCoverData.derivedTriple_mult]
    exact one_le_tuningExponent S.mult
  case quasiCompact =>
    have h := hlev.quasiCompact
    rw [MaxContactCoverData.derivedTriple_structureMorphism]
    simp at h
    with_unfolding_all exact h
  case smooth =>
    rw [MaxContactCoverData.derivedTriple_structureMorphism]
    exact smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
  case snc =>
    rw [MaxContactCoverData.derivedTriple_structureMorphism, MaxContactCoverData.derivedTriple_boundary]
    exact hsnc
  case nonzeroOnComponents =>
    have hNZ := hlev.nonzeroOnComponents
    have hsupp : ((LowerDimReductionPullback.tunedIdealAtLength S s hft).support : Set ↥(s.obj s.length)) ⊆
        ((s.ideal s.length).support : Set ↥(s.obj s.length)) := by
      have : CharZero S.base := hV.charZero
      have : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap) :=
        smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
      have := hft
      have hpow := pow_tuningExponent_le_balancedTunedSheaf S.base (s.proj s.length ≫ S.structMap)
        (s.ideal s.length) S.mult hV.one_le_mult
      exact Set.Subset.trans (Scheme.IdealSheafData.support_antitone hpow)
        (support_pow_subset_support (s.ideal s.length) (tuningExponent S.mult))
    rw [LowerDimReductionPullback.ideal_derivedTriple]
    unfold FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
    intro T hT hsub
    exact hNZ T hT (Set.Subset.trans hsub hsupp)

/- English proof (translation)
Establish `hi' : i ≤ u.toSequenceOfBlowups.length` using `hi`. Establish `hN : AlgebraicGeometry.IsNoetherian (u.toSequenceOfBlowups.schemeAt i)` using `MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hVc u i hi'`. Conclude with `inferInstanceAs (AlgebraicGeometry.IsLocallyNoetherian (u.toSequenceOfBlowups.schemeAt i))`.
-/
theorem isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt (_hMaxContact : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u})
    (_hV : S.IsAdmissible) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra keep).IsAdmissible)
    (u : LowerDimReductionPullback.TunedMarkedBlowupSeq S s hft extra keep) (i : ℕ) (hi : i ≤ u.length) :
    AlgebraicGeometry.IsLocallyNoetherian ((BlowupSequenceData.ofSequenceOfBlowups u.toSequenceOfBlowups).obj i) := by
  have hi' : i ≤ u.toSequenceOfBlowups.length := hi
  have hN : AlgebraicGeometry.IsNoetherian (u.toSequenceOfBlowups.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hVc u i hi'
  exact inferInstanceAs (AlgebraicGeometry.IsLocallyNoetherian (u.toSequenceOfBlowups.schemeAt i))

abbrev continuationMarkedData (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (u : LowerDimReductionPullback.TunedMarkedBlowupSeq S s hft extra keep)
    (hmk : (BlowupSequenceData.ofSequenceOfBlowups u.toSequenceOfBlowups).IsMarked (s.proj s.length ≫ S.structMap)
      (s.ideal s.length) S.mult (s.boundary s.length)) :
    MarkedBlowupSequenceData (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
      (s.boundary s.length) :=
  (BlowupSequenceData.ofSequenceOfBlowups u.toSequenceOfBlowups).toMarkedBlowupSequenceData (s.proj s.length ≫ S.structMap)
    (s.ideal s.length) S.mult (s.boundary s.length) hmk

/- English proof (translation)
The claim follows from `hstar.coverTriple_valid T h.valid h.orderLE (MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid (hstar.exists_goodCover T h.valid h.orderLE))`.
-/
theorem isAdmissible_coverTriple (hstar : MaxContactCoverProperties.{u}) (P : ℕ → Prop) (T : MarkedIdealWithBoundary.{u})
    (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    (MaxContactCoverData.coverTriple T h.valid).IsAdmissible :=
  hstar.coverTriple_valid T h.valid h.orderLE
    (MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid
      (hstar.exists_goodCover T h.valid h.orderLE))

/- English proof (translation)
Use `h.valid.locallyOfFiniteType` as an intermediate fact. Use `h.valid.smooth` as an intermediate fact. Establish `: CharZero T.base` using `h.valid.charZero`. Establish `hμ : 1 ≤ T.mult` using `h.valid.one_le_mult`. Establish `hmax : MaxOrderEq T.ideal T.mult` using `⟨(orderLE_iff T.ideal T.mult).2 h.orderLE, h.coSupport_nonempty⟩`.

Establish `H` using `hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE T.base T.scheme T.structMap T.ideal T.mult hμ hmax (tuningExponent T.mult) (one_le_tuningExponent T.mult)`. Introduce `x`. Conclude with `(orderAt_comap T.base T.structMap (MaxContactCoverData.coverMap T h.valid) (MaxContactCoverData.balancedTunedIdeal T h.valid) x).trans_le (H.2 _)`.
-/
theorem orderAt_coverTriple_ideal_le_mult (hstar : MaxContactCoverProperties.{u}) (P : ℕ → Prop) (T : MarkedIdealWithBoundary.{u})
    (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    ∀ x : ↥(MaxContactCoverData.coverTriple T h.valid).scheme,
      orderAt (MaxContactCoverData.coverTriple T h.valid).ideal x ≤
        ((MaxContactCoverData.coverTriple T h.valid).mult : ℕ∞) := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have : CharZero T.base := h.valid.charZero
  have hμ : 1 ≤ T.mult := h.valid.one_le_mult
  have hmax : MaxOrderEq T.ideal T.mult :=
    ⟨(orderLE_iff T.ideal T.mult).2 h.orderLE, h.coSupport_nonempty⟩
  have H := hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE T.base T.scheme T.structMap T.ideal
    T.mult hμ hmax (tuningExponent T.mult) (one_le_tuningExponent T.mult)
  intro x
  exact (orderAt_comap T.base T.structMap (MaxContactCoverData.coverMap T h.valid)
    (MaxContactCoverData.balancedTunedIdeal T h.valid) x).trans_le (H.2 _)

/- English proof (translation)
Establish `hft : AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverTriple T h.valid).structMap` using `(isAdmissible_coverTriple hstar P T h).locallyOfFiniteType`. Establish `key` using `hstar.coverContact_admissible T h.valid (MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid (hstar.exists_goodCover T h.valid h.orderLE))`. Rewrite using `[MaxContactCoverData.coverTriple_mult]`. Conclude with `key`.
-/
theorem isMaxContactHypersurface_coverMaxContactIdeal (hstar : MaxContactCoverProperties.{u}) (P : ℕ → Prop)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    @IsMaxContactHypersurface (MaxContactCoverData.coverTriple T h.valid).base _
      (MaxContactCoverData.coverTriple T h.valid).scheme
      (MaxContactCoverData.coverTriple T h.valid).structMap
      (isAdmissible_coverTriple hstar P T h).locallyOfFiniteType
      (MaxContactCoverData.coverTriple T h.valid).ideal
      (MaxContactCoverData.coverTriple T h.valid).mult
      (MaxContactCoverData.coverMaxContactIdeal T h.valid) := by
  have hft : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverTriple T h.valid).structMap :=
    (isAdmissible_coverTriple hstar P T h).locallyOfFiniteType
  have key := hstar.coverContact_admissible T h.valid
    (MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid
      (hstar.exists_goodCover T h.valid h.orderLE))
  rw [MaxContactCoverData.coverTriple_mult]
  exact key

/- English proof (translation)
The claim follows from `hstar.coverContact_snc T h.valid (MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid (hstar.exists_goodCover T h.valid h.orderLE))`.
-/
theorem inStrictNormalCrossingPosition_coverMaxContactIdeal (hstar : MaxContactCoverProperties.{u}) (P : ℕ → Prop) (T : MarkedIdealWithBoundary.{u})
    (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T h.valid).structMap
      [MaxContactCoverData.coverMaxContactIdeal T h.valid] :=
  hstar.coverContact_snc T h.valid
    (MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid
      (hstar.exists_goodCover T h.valid h.orderLE))

end BoundarySeparationByMaxContact

end FunctorialResolution.EmbeddedResolution

end

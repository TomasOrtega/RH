import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdeal
universe u

open AlgebraicGeometry CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
For the empty list, global evaluation on the affine open gives the unit section ideal. For a nonempty list, evaluation preserves the product of the first factor with the tail product. Applying induction to the tail gives the desired product of section ideals.
-/
private theorem ideal_listProd_map {X : Scheme.{u}} (g : ℕ → X.IdealSheafData) (l : List ℕ)
    (U : X.affineOpens) :
    ((l.map g).prod).ideal U = (l.map (fun j => (g j).ideal U)).prod := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.ideal_top]
      exact Ideal.one_eq_top.symm
  | cons a t ih =>
      have hmul : ((g a) * (t.map g).prod).ideal U
          = (g a).ideal U * ((t.map g).prod).ideal U := by
        simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, hmul, ih]

/- English proof (authored)
Extension along the ring map preserves multiplication and the unit ideal. Applying this property successively to the finite product over the range gives the product of the extended ideals.
-/
private theorem ideal_map_prod_range {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (g : ℕ → Ideal R) (n : ℕ) :
    Ideal.map φ (∏ j ∈ Finset.range n, g j) = ∏ j ∈ Finset.range n, Ideal.map φ (g j) :=
  map_prod (Ideal.mapHom φ) g (Finset.range n)

/- English proof (authored)
Expand the tuning monomial as the product of powers of derivative iterates. Ideal extension preserves the product and each power. The assumed compatibility with every derivative iterate identifies each extended factor with the corresponding factor for the extended ideal.
-/
private theorem map_tuningMonomial_of_map_derivIdealIterate (k : Type u) [CommRing k] {R S : Type u}
    [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (φ : R →+* S) (J : Ideal R) (m : ℕ)
    (c : ℕ → ℕ)
    (h : ∀ j : ℕ, Ideal.map φ (derivIdealIterate k j J) = derivIdealIterate k j (Ideal.map φ J)) :
    Ideal.map φ (tuningMonomial k J m c) = tuningMonomial k (Ideal.map φ J) m c := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod, ideal_map_prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Ideal.map_pow, h j]

/- English proof (authored)
The exponent functions meeting the weight condition are the same in both rings. Each product term downstairs extends to the corresponding term upstairs because derivative iterates, powers, and products commute with extension here. Every extended term lies in the tuned ideal upstairs, proving one containment. Conversely each qualifying term upstairs is such an extension and therefore lies in the extension of the tuned ideal downstairs.
-/
private theorem map_tunedIdeal_of_map_derivIdealIterate (k : Type u) [CommRing k] {R S : Type u}
    [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (φ : R →+* S) (J : Ideal R) (m s : ℕ)
    (h : ∀ j : ℕ, Ideal.map φ (derivIdealIterate k j J) = derivIdealIterate k j (Ideal.map φ J)) :
    Ideal.map φ (tunedIdeal k J m s) = tunedIdeal k (Ideal.map φ J) m s := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    refine (tunedIdeal_le_iff k J m s _).mpr ?_
    intro c hc
    rw [← Ideal.map_le_iff_le_comap, map_tuningMonomial_of_map_derivIdealIterate k φ J m c h]
    exact tuningMonomial_le_tunedIdeal k (Ideal.map φ J) m s c hc
  · refine (tunedIdeal_le_iff k (Ideal.map φ J) m s _).mpr ?_
    intro c hc
    rw [← map_tuningMonomial_of_map_derivIdealIterate k φ J m c h]
    exact Ideal.map_mono (tuningMonomial_le_tunedIdeal k J m s c hc)

/- English proof (authored)
Use the exponent function that is zero except at the derivative index one below the mark, where it has the given exponent. This index has weight one, so the term meets the threshold exactly. Its product is the requested power of that derivative iterate.
-/
private theorem pow_derivIdealIterate_pred_le_tunedIdeal (k : Type u) [CommRing k] {S : Type u}
    [CommRing S] [Algebra k S] (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    (derivIdealIterate k (m - 1) J) ^ t ≤ tunedIdeal k J m t := by
  have hmem : m - 1 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have h1 : m - (m - 1) = 1 := by omega
  have hmono : tuningMonomial k J m (fun j => if j = m - 1 then t else 0)
      = (derivIdealIterate k (m - 1) J) ^ t := by
    rw [tuningMonomial_eq_prod]
    refine (Finset.prod_eq_single (m - 1) (fun b _ hb => by simp [hb])
      (fun h => absurd hmem h)).trans ?_
    simp
  have hw : tuningWeight m (fun j => if j = m - 1 then t else 0) = t := by
    rw [tuningWeight_eq_sum]
    refine (Finset.sum_eq_single (m - 1) (fun b _ hb => by simp [hb])
      (fun h => absurd hmem h)).trans ?_
    simp [h1]
  rw [← hmono]
  exact tuningMonomial_le_tunedIdeal k J m t _ (le_of_eq hw.symm)

/- English proof (authored)
Evaluating on the affine open preserves the product and every power. Each derivative sheaf iterate evaluates to the derivative iterate of the section ideal. These evaluated factors in range order are exactly the product defining the tuning monomial in the section ring.
-/
private theorem ideal_prod_derivIdealSheafIterate_pow (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ) (c : ℕ → ℕ) (U : X.affineOpens) :
    (((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c j))).prod).ideal U =
      @tuningMonomial k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m c := by
  have hpow : ∀ (J : X.IdealSheafData) (n : ℕ), (J ^ n).ideal U = (J.ideal U) ^ n := by
    intro J n
    exact congrFun (show (J ^ n).ideal = J.ideal ^ n by
      rw [Scheme.IdealSheafData.ideal_pow]) U
  have key : ((List.range m).map
        (fun j =>
          (@derivIdealIterate k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1) j (I.ideal U)) ^ c j)).prod
      = @tuningMonomial k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1) (I.ideal U) m c :=
    listProd_map_range_eq_prod _ m
  simp only [ideal_listProd_map, hpow, derivIdealSheafIterate_ideal]
  exact key

/- English proof (authored)
Restriction to the basic open extends the original affine section ideal to the section ideal there. The same is true for each derivative sheaf iterate. Thus extension along the restriction map commutes with the ring derivative iterates of this ideal. The compatibility of tuning with such extension gives the required ideal on the basic open.
-/
private theorem map_tunedIdeal_basicOpen (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m s : ℕ) :
    ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@tunedIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m s) =
        @tunedIdeal k _ _ _ (sectionsAlgebra k p (X.affineBasicOpen f).1)
          (I.ideal (X.affineBasicOpen f)) m s := by
  intro U f
  let algU : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
  let algV : Algebra k Γ(X, X.basicOpen f) := sectionsAlgebra k p (X.basicOpen f)
  have hI : Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (I.ideal U) =
      I.ideal (X.affineBasicOpen f) := I.map_ideal_basicOpen U f
  have hd : ∀ j : ℕ,
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@derivIdealIterate k _ Γ(X, U.1) _ algU j (I.ideal U)) =
        @derivIdealIterate k _ Γ(X, X.basicOpen f) _ algV j
          (Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (I.ideal U)) := by
    intro j
    have h1 := (derivIdealSheafIterate k p j I).map_ideal_basicOpen U f
    rw [derivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal] at h1
    exact h1.trans (congrArg (@derivIdealIterate k _ Γ(X, X.basicOpen f) _ algV j) hI.symm)
  have h2 := @map_tunedIdeal_of_map_derivIdealIterate k _ Γ(X, U.1) Γ(X, X.basicOpen f) _ _ algU algV
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (I.ideal U) m s hd
  exact h2.trans (congrArg (fun J : Ideal Γ(X, X.basicOpen f) =>
    @tunedIdeal k _ Γ(X, X.basicOpen f) _ algV J m s) hI)

private noncomputable def tunedIdealSheafOfSections (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m s : ℕ) :
    X.IdealSheafData where
  ideal U := @tunedIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m s
  map_ideal_basicOpen := map_tunedIdeal_basicOpen k p I m s

/- English proof (authored)
The tuned ring ideals on affine opens are compatible with basic-open restriction and thus form an ideal sheaf. Each qualifying product of derivative sheaves evaluates to a tuning monomial on each open, which is contained in the local tuned ring ideal. Taking the supremum gives one inclusion. Conversely, every qualifying tuning monomial in the section ring is the evaluation of a product appearing in the definition of the tuned sheaf. These monomials generate the local tuned ring ideal, proving the reverse inclusion.
-/
@[simp] theorem tunedSheaf_ideal (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    (m s : ℕ) (U : X.affineOpens) :
    (tunedSheaf k p I m s).ideal U =
      @tunedIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m s := by
  refine le_antisymm ?_ ?_
  · have hle : tunedSheaf k p I m s ≤ tunedIdealSheafOfSections k p I m s := by
      rw [tunedSheaf_eq_iSup]
      refine iSup_le fun c => ?_
      have key : ∀ V : X.affineOpens,
          (((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod).ideal V ≤
            (tunedIdealSheafOfSections k p I m s).ideal V := by
        intro V
        rw [ideal_prod_derivIdealSheafIterate_pow k p I m c.1 V]
        exact @tuningMonomial_le_tunedIdeal k _ Γ(X, V.1) _ (sectionsAlgebra k p V.1)
          (I.ideal V) m s c.1 c.2
      exact key
    exact hle U
  · refine (@tunedIdeal_le_iff k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
      (I.ideal U) m s _).mpr ?_
    intro c hc
    rw [← ideal_prod_derivIdealSheafIterate_pow k p I m c U]
    have hmono : ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c j))).prod ≤
        tunedSheaf k p I m s := by
      rw [tunedSheaf_eq_iSup]
      exact le_iSup (fun d : {d : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * d j} =>
        ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (d.1 j))).prod) ⟨c, hc⟩
    exact hmono U

/- English proof (authored)
Evaluate on an arbitrary affine open. The power of the derivative iterate becomes the corresponding power of the ring-level iterate, and the tuned sheaf becomes the tuned ring ideal. The latter contains the monomial with nonzero exponent only at the derivative index one below the mark, giving the asserted containment.
-/
private theorem derivIdealSheafIterate_pow_le_tunedSheaf (k : Type u) [CommRing k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] (I : X.IdealSheafData) (m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    (derivIdealSheafIterate k p (m - 1) I) ^ t ≤ tunedSheaf k p I m t := by
  have h : ∀ U : X.affineOpens,
      ((derivIdealSheafIterate k p (m - 1) I) ^ t).ideal U ≤ (tunedSheaf k p I m t).ideal U := by
    intro U
    have hpow : ((derivIdealSheafIterate k p (m - 1) I) ^ t).ideal U
        = ((derivIdealSheafIterate k p (m - 1) I).ideal U) ^ t :=
      congrFun (show ((derivIdealSheafIterate k p (m - 1) I) ^ t).ideal
          = (derivIdealSheafIterate k p (m - 1) I).ideal ^ t by
        rw [Scheme.IdealSheafData.ideal_pow]) U
    rw [hpow, derivIdealSheafIterate_ideal, tunedSheaf_ideal]
    exact @pow_derivIdealIterate_pred_le_tunedIdeal k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
      (I.ideal U) m hm t
  exact h

/- English proof (authored)
On affine sections, the tuned ideal at threshold one is contained in the derivative ideal one below the mark by the ring-level threshold-one estimate. Conversely, the first power of that iterate is one of the qualifying tuned monomials. These inclusions give equality of sheaves.
-/
private theorem tunedSheaf_one_eq_derivIdealSheafIterate (k : Type u) [CommRing k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] (I : X.IdealSheafData) (m : ℕ) (hm : 1 ≤ m) :
    tunedSheaf k p I m 1 = derivIdealSheafIterate k p (m - 1) I := by
  refine le_antisymm ?_ ?_
  · have h : ∀ U : X.affineOpens,
        (tunedSheaf k p I m 1).ideal U ≤ (derivIdealSheafIterate k p (m - 1) I).ideal U := by
      intro U
      rw [tunedSheaf_ideal, derivIdealSheafIterate_ideal]
      exact @tunedIdeal_one_le_derivIdealIterate k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1) (I.ideal U) m hm
    exact h
  · have h := derivIdealSheafIterate_pow_le_tunedSheaf k p I m hm 1
    rwa [pow_one] at h

/- English proof (authored)
On each affine open the ring-level derivative bound puts the derivative of the successor-threshold tuned ideal in the preceding tuned ideal. For the reverse inclusion, work on stalks. At a point of maximal order, choose a maximal-contact coordinate. It belongs to the required original derivative ideal, and its coordinate derivation sends it to one. The ring-level reverse containment using this derivation applies on the chart and hence on the stalk. At a point of smaller order, the original derivative iterate one below the mark has unit stalk. The successor-threshold tuned sheaf contains a power of that iterate and so has unit stalk as well. Its derivative then has unit stalk. This gives the reverse containment at every point.
-/
theorem derivIdealSheaf_tunedSheaf_succ : DerivIdealSheafTunedSheafSucc.{u} := by
  intro k _ _ _ X p _ _ I m hm hmax s
  refine le_antisymm ?_ ?_
  · have h : ∀ U : X.affineOpens,
        (derivIdealSheaf k p (tunedSheaf k p I m (s + 1))).ideal U ≤
          (tunedSheaf k p I m s).ideal U := by
      intro U
      rw [derivIdealSheaf_ideal, tunedSheaf_ideal, tunedSheaf_ideal]
      exact @derivIdeal_tunedIdeal_succ_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
        (I.ideal U) m s
    exact h
  · rw [le_iff_forall_stalkIdeal_le]
    intro x
    have hord : orderAt I x ≤ (m : ℕ∞) := hmax.orderLE x
    rcases eq_or_lt_of_le hord with heq | hlt
    · obtain ⟨U, hU, hxU, n, c, j, hmc, -⟩ := exists_isMaxContactCoord k p I hm x heq
      have hcoord : c.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩ :=
        (isMaxContactCoord_iff_coord_mem k p I m hU c j).mp hmc
      rw [maxContactIdeal_ideal] at hcoord
      have hle : @tunedIdeal k _ Γ(X, U) _ (sectionsAlgebra k p U) (I.ideal ⟨U, hU⟩) m s ≤
          @derivIdeal k _ Γ(X, U) _ (sectionsAlgebra k p U)
            (@tunedIdeal k _ Γ(X, U) _ (sectionsAlgebra k p U)
              (I.ideal ⟨U, hU⟩) m (s + 1)) := by
        let algU : Algebra k Γ(X, U) := sectionsAlgebra k p U
        let algP : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.algebra
        have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := c.isScalarTower
        have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
          c.algebra_formallyEtale hU
        let algQ : Algebra ℚ Γ(X, U) :=
          RingHom.toAlgebra ((algebraMap k Γ(X, U)).comp (algebraMap ℚ k))
        have hδ : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U) (ULift.up j)
            (c.coord j) = 1 := by
          rw [← EtaleChart.etaleCoordinates_coord c j]
          exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin n)) Γ(X, U)
            (ULift.up j)
        exact tunedIdeal_le_derivIdeal_tunedIdeal_succ k (I.ideal ⟨U, hU⟩) m hm hcoord
          (EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, U) (ULift.up j)) hδ s
      rw [stalkIdeal_eq_map_germ (tunedSheaf k p I m s) x ⟨U, hU⟩ hxU,
        stalkIdeal_eq_map_germ (derivIdealSheaf k p (tunedSheaf k p I m (s + 1))) x ⟨U, hU⟩ hxU]
      refine Ideal.map_mono ?_
      simp only [tunedSheaf_ideal, derivIdealSheaf_ideal]
      exact hle
    · have hxns : x ∉ (derivIdealSheafIterate k p (m - 1) I).support := by
        intro hc
        have hmem : x ∈ orderAtLeastLocus I m := by
          rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm]
          exact hc
        exact absurd ((mem_orderAtLeastLocus_iff I m x).mp hmem) (not_le.mpr hlt)
      have htop : stalkIdeal (derivIdealSheafIterate k p (m - 1) I) x = ⊤ :=
        not_not.mp fun hne2 => hxns ((mem_support_iff_stalkIdeal_ne_top _ x).mpr hne2)
      have h1 : stalkIdeal ((derivIdealSheafIterate k p (m - 1) I) ^ (s + 1)) x = ⊤ := by
        rw [stalkIdeal_pow, htop, ← Ideal.one_eq_top, one_pow]
      have h2 : stalkIdeal (tunedSheaf k p I m (s + 1)) x ≤
          stalkIdeal (derivIdealSheaf k p (tunedSheaf k p I m (s + 1))) x :=
        stalkIdeal_mono (le_derivIdealSheaf k p (tunedSheaf k p I m (s + 1))) x
      have h3 : (⊤ : Ideal _) ≤
          stalkIdeal (derivIdealSheaf k p (tunedSheaf k p I m (s + 1))) x := by
        rw [← h1]
        exact le_trans
          (stalkIdeal_mono (derivIdealSheafIterate_pow_le_tunedSheaf k p I m hm (s + 1)) x) h2
      exact le_trans le_top h3

/- English proof (authored)
A derivative step of a positive-threshold tuned sheaf lowers the threshold by one. Induction gives the tuned sheaf at the original threshold minus the number of steps, as long as the steps do not exceed the threshold. Performing one fewer step than the positive threshold leaves threshold one, where the tuned sheaf equals the derivative iterate one below the original mark.
-/
theorem maxContactIdealTunedSheafEq : MaxContactIdealTunedSheafEq.{u} := by
  intro k _ _ _ X p _ _ I m hm hmax s hs
  have h3 : ∀ t : ℕ, derivIdealSheaf k p (tunedSheaf k p I m (t + 1)) = tunedSheaf k p I m t :=
    derivIdealSheaf_tunedSheaf_succ k X p I m hm hmax
  have step : ∀ j t : ℕ, j ≤ t →
      derivIdealSheafIterate k p j (tunedSheaf k p I m t) = tunedSheaf k p I m (t - j) := by
    intro j
    induction j with
    | zero =>
        intro t _
        rw [derivIdealSheafIterate_zero, Nat.sub_zero]
    | succ n ih =>
        intro t ht
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        have hn : n ≤ t' := by omega
        have he : t' + 1 - (n + 1) = t' - n := by omega
        rw [he, derivIdealSheafIterate_add k p n 1 (tunedSheaf k p I m (t' + 1)),
          derivIdealSheafIterate_one, h3 t', ih t' hn]
  have hstep := step (s - 1) s (by omega)
  have he2 : s - (s - 1) = 1 := by omega
  rw [hstep, he2, tunedSheaf_one_eq_derivIdealSheafIterate k p I m hm]

/- English proof (authored)
Check the product containment on each affine open. Evaluation preserves the product, and the differentiated tuned sheaves evaluate to the corresponding derivatives of the tuned section ideal. The ring-level maximal-contact invariance estimate for this tuned ideal gives the containment on every affine open.
-/
theorem isMaxContactInvariantTunedSheaf :
    IsMaxContactInvariantTunedSheaf.{u} := by
  intro k _ _ _ X p _ _ I m _ _ s hs
  have key : ∀ U : X.affineOpens,
      ((derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s)) *
          derivIdealSheaf k p (tunedSheaf k p I m s)).ideal U ≤
        (tunedSheaf k p I m s).ideal U := by
    intro U
    have hmul : ((derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s)) *
          derivIdealSheaf k p (tunedSheaf k p I m s)).ideal U =
        (derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s)).ideal U *
          (derivIdealSheaf k p (tunedSheaf k p I m s)).ideal U := by
      simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
    rw [hmul, derivIdealSheafIterate_ideal, derivIdealSheaf_ideal, tunedSheaf_ideal]
    exact @derivIdealIterate_mul_derivIdeal_tunedIdeal_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1) (I.ideal U) m s hs
  exact key

end FunctorialResolution.EmbeddedResolution

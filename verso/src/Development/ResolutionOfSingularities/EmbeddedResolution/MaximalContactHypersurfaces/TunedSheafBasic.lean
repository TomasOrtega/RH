import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
universe u

open AlgebraicGeometry CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
On each affine open, the section ideal of a product is the product of the section ideals. Monotonicity of ideal multiplication gives the desired inclusion on each open, hence on the sheaves.
-/
private theorem mul_le_mul_idealSheafData {X : Scheme.{u}} {A B C D : X.IdealSheafData}
    (h1 : A ≤ B) (h2 : C ≤ D) : A * C ≤ B * D := by
  have h : ∀ U : X.affineOpens, (A * C).ideal U ≤ (B * D).ideal U := by
    intro U
    rw [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_mul]
    exact Ideal.mul_mono (h1 U) (h2 U)
  exact h

/- English proof (authored)
On an affine open, evaluation of a power gives the corresponding power of its section ideal. An ideal’s higher power is contained in its lower power, since the higher power is the lower one times an ideal. The affine inclusions give the sheaf inclusion.
-/
private theorem idealSheafData_pow_antitone_of_le {X : Scheme.{u}} (I : X.IdealSheafData) {a b : ℕ}
    (h : b ≤ a) : I ^ a ≤ I ^ b := by
  have hU : ∀ U : X.affineOpens, (I ^ a).ideal U ≤ (I ^ b).ideal U := by
    intro U
    rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow]
    exact Ideal.pow_le_pow_right h
  exact hU

/- English proof (authored)
For the empty list both products are the unit ideal. For a nonempty list, apply the pointwise containment to its first entry and use induction on the tail. Monotonicity of multiplication combines these two inclusions.
-/
private theorem listProd_map_le_listProd_map {X : Scheme.{u}} (f g : ℕ → X.IdealSheafData) :
    ∀ L : List ℕ, (∀ j ∈ L, f j ≤ g j) → (L.map f).prod ≤ (L.map g).prod := by
  intro L
  induction L with
  | nil =>
      intro _
      exact le_rfl
  | cons a L ih =>
      intro h
      simp only [List.map_cons, List.prod_cons]
      exact mul_le_mul_idealSheafData (h a (by simp)) (ih fun j hj => h j (by simp [hj]))

/- English proof (authored)
The range list of length one contains only zero. Its mapped product is the indicated value at zero multiplied by the empty product, so it equals that value.
-/
private theorem listProd_map_range_one {X : Scheme.{u}} (f : ℕ → X.IdealSheafData) :
    ((List.range 1).map f).prod = f 0 := by
  have h : List.range 1 = [0] := rfl
  rw [h, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

private def extendExponentsByZero (m s : ℕ) (t : Fin m → Fin (s + 1)) (j : ℕ) : ℕ :=
  if h : j < m then (t ⟨j, h⟩ : ℕ) else 0

/- English proof (authored)
An index below the cutoff belongs to the finite index set. At such an index, extension by zero returns the original exponent.
-/
private theorem extendExponentsByZero_apply_of_lt (m s : ℕ) (t : Fin m → Fin (s + 1)) (j : ℕ) (hj : j < m) :
    extendExponentsByZero m s t j = (t ⟨j, hj⟩ : ℕ) :=
  dif_pos hj

/- English proof (authored)
If all exponents in the sum are already at most the threshold, truncating them changes nothing. Otherwise, an exponent above the threshold becomes exactly the threshold when truncated. Its weight is at least one because its index is below the mark, so that term alone contributes at least the threshold. All other terms are nonnegative.
-/
private theorem le_sum_mul_min_of_le_sum (m s : ℕ) (c : ℕ → ℕ)
    (hc : s ≤ ∑ j ∈ Finset.range m, (m - j) * c j) :
    s ≤ ∑ j ∈ Finset.range m, (m - j) * min (c j) s := by
  by_cases h : ∀ j ∈ Finset.range m, c j ≤ s
  · refine le_trans hc (le_of_eq (Finset.sum_congr rfl ?_))
    intro j hj
    rw [min_eq_left (h j hj)]
  · push Not at h
    obtain ⟨j, hj, hjs⟩ := h
    have hjm : j < m := Finset.mem_range.mp hj
    have h1 : 1 ≤ m - j := by omega
    have hterm : s ≤ (m - j) * min (c j) s := by
      have hmin : min (c j) s = s := min_eq_right (le_of_lt hjs)
      rw [hmin]
      calc s = 1 * s := (one_mul s).symm
        _ ≤ (m - j) * s := Nat.mul_le_mul h1 (le_refl s)
    refine le_trans hterm (Finset.single_le_sum
      (f := fun j : ℕ => (m - j) * min (c j) s) ?_ hj)
    intro i _
    exact Nat.zero_le _

/- English proof (authored)
The exponent function satisfies the required weight bound. Its product is therefore one of the ideals in the supremum defining the tuned sheaf, and lies in that supremum.
-/
theorem prod_pow_derivIdealSheafIterate_le_tunedSheaf (k : Type u) [Field k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m s : ℕ) (c : ℕ → ℕ)
    (hc : s ≤ ∑ j ∈ Finset.range m, (m - j) * c j) :
    ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ c j)).prod ≤
      tunedSheaf k p I m s := by
  rw [tunedSheaf_eq_iSup]
  exact le_iSup (fun c : {c : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
    ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod) ⟨c, hc⟩

/- English proof (authored)
For a term in the original supremum, truncate every exponent in the finite range at the threshold. The weighted sum remains large enough by the truncation estimate. Lowering an ideal’s exponent enlarges its power, so the original product lies in the product for the resulting bounded exponent vector. This proves containment in the bounded supremum. Conversely every bounded exponent vector extends by zero to an exponent function admitted in the original supremum, so each bounded term occurs there.
-/
private theorem tunedSheaf_eq_iSup_fin (k : Type u) [Field k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m s : ℕ) :
    tunedSheaf k p I m s =
      ⨆ t : {t : Fin m → Fin (s + 1) //
          s ≤ ∑ j ∈ Finset.range m, (m - j) * extendExponentsByZero m s t j},
        ((List.range m).map
          (fun j => derivIdealSheafIterate k p j I ^ extendExponentsByZero m s t.1 j)).prod := by
  rw [tunedSheaf_eq_iSup]
  refine le_antisymm (iSup_le ?_) (iSup_le ?_)
  · rintro ⟨c, hc⟩
    have hex : ∀ j : ℕ, j < m →
        extendExponentsByZero m s (fun i : Fin m =>
            (⟨min (c i.1) s, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (s + 1))) j
          = min (c j) s := fun j hj => extendExponentsByZero_apply_of_lt m s _ j hj
    have hconstr : s ≤ ∑ j ∈ Finset.range m, (m - j) *
        extendExponentsByZero m s (fun i : Fin m =>
          (⟨min (c i.1) s, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (s + 1))) j := by
      refine le_trans (le_sum_mul_min_of_le_sum m s c hc) (le_of_eq (Finset.sum_congr rfl ?_))
      intro j hj
      rw [hex j (Finset.mem_range.mp hj)]
    have hprod : ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ c j)).prod ≤
        ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^
          extendExponentsByZero m s (fun i : Fin m =>
            (⟨min (c i.1) s, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (s + 1))) j)).prod := by
      refine listProd_map_le_listProd_map _ _ (List.range m) fun j hj => ?_
      rw [hex j (List.mem_range.mp hj)]
      exact idealSheafData_pow_antitone_of_le _ (min_le_left _ _)
    exact le_iSup_of_le ⟨_, hconstr⟩ hprod
  · rintro ⟨t, ht⟩
    exact le_iSup_of_le ⟨extendExponentsByZero m s t, ht⟩ le_rfl

/- English proof (authored)
On each affine open the power of the sheaf gives the same power of the section ideal. A positive power of a ring ideal lies in that ideal because it contains the ideal as a factor. Apply this on each affine open.
-/
theorem idealSheafData_pow_le_self {X : Scheme.{u}} (I : X.IdealSheafData) {c : ℕ}
    (hc : 1 ≤ c) : I ^ c ≤ I := by
  have h : ∀ U : X.affineOpens, (I ^ c).ideal U ≤ I.ideal U := by
    intro U
    rw [Scheme.IdealSheafData.ideal_pow]
    exact Ideal.pow_le_self (by omega)
  exact h

/- English proof (authored)
With mark one the only derivative order in a product is zero, with weight one. An admitted exponent is therefore at least one, and the corresponding ideal power is contained in the original ideal. Choosing exponent one gives the original ideal itself as a term in the supremum, proving equality.
-/
theorem tunedSheaf_one_one (k : Type u) [Field k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    tunedSheaf k p I 1 1 = I := by
  rw [tunedSheaf_eq_iSup]
  refine le_antisymm (iSup_le ?_) ?_
  · rintro ⟨c, hc⟩
    have hc1 : 1 ≤ c 0 := by simpa using hc
    have key : ((List.range 1).map (fun j => derivIdealSheafIterate k p j I ^ c j)).prod ≤ I := by
      rw [listProd_map_range_one]
      exact idealSheafData_pow_le_self I hc1
    exact key
  · have key : I ≤ ((List.range 1).map
        (fun j => derivIdealSheafIterate k p j I ^ ((fun _ : ℕ => 1) j))).prod := by
      rw [listProd_map_range_one]
      exact le_of_eq (pow_one I).symm
    exact le_trans key (le_iSup
      (fun c : {c : ℕ → ℕ // 1 ≤ ∑ j ∈ Finset.range 1, (1 - j) * c j} =>
        ((List.range 1).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod)
      ⟨fun _ => 1, by simp⟩)

/- English proof (authored)
The balanced tuning exponent at mark one is one. The balanced sheaf therefore agrees with the tuned sheaf of mark and threshold one, which equals the original ideal.
-/
theorem balancedTunedSheaf_one (k : Type u) [Field k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    balancedTunedSheaf k p I 1 = I := by
  rw [balancedTunedSheaf_eq, tuningExponent_one, tunedSheaf_one_one]

/- English proof (authored)
Absence of points of order at least the mark implies that the derivative iterate one below the mark is the unit ideal. Choose the exponent function supported only at that derivative index with value equal to the threshold. That index has weight one, so its product is admitted. The selected factor and all zero-exponent factors are unit ideals, so their product is the unit ideal. The supremum is therefore the unit ideal.
-/
theorem tunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty (k : Type u) [Field k] [CharZero k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p] (I : X.IdealSheafData) {m : ℕ}
    (hm : 1 ≤ m) (s : ℕ) (h : orderAtLeastLocus I m = (∅ : Set X)) :
    tunedSheaf k p I m s = ⊤ := by
  classical
  have hm1 : m - 1 + 1 = m := by omega
  have htop : derivIdealSheafIterate k p (m - 1) I = ⊤ :=
    derivIdealSheafIterate_eq_top_of_orderAtLeastLocus_eq_empty k p I (m - 1) (by rw [hm1]; exact h)
  have hmem : m - 1 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have hm2 : m - (m - 1) = 1 := by omega
  have heq : ∑ j ∈ Finset.range m, (m - j) * (if j = m - 1 then s else 0)
      = (m - (m - 1)) * (if m - 1 = m - 1 then s else 0) :=
    Finset.sum_eq_single (m - 1) (fun b _ hb => by rw [if_neg hb, mul_zero])
      (fun hb => absurd hmem hb)
  have h3 : (m - (m - 1)) * (if m - 1 = m - 1 then s else 0) = s := by simp [hm2]
  have hsum : s ≤ ∑ j ∈ Finset.range m, (m - j) * (if j = m - 1 then s else 0) :=
    (heq.trans h3).ge
  have hprod : ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^
      (if j = m - 1 then s else 0))).prod = ⊤ := by
    have h1 : ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^
        (if j = m - 1 then s else 0))).prod = 1 := by
      refine List.prod_eq_one ?_
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, -, rfl⟩ := hx
      by_cases hj : j = m - 1
      · subst hj
        rw [htop, ← Scheme.IdealSheafData.one_eq_top, one_pow]
      · rw [if_neg hj, pow_zero]
    rw [h1, Scheme.IdealSheafData.one_eq_top]
  rw [tunedSheaf_eq_iSup]
  exact top_le_iff.mp (le_trans (le_of_eq hprod.symm)
    (le_iSup (fun c : {c : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
      ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod)
      ⟨fun j => if j = m - 1 then s else 0, hsum⟩))

/- English proof (authored)
The balanced tuned sheaf uses the prescribed tuning exponent as its threshold. Apply the empty-order-locus argument at this threshold to obtain the unit ideal.
-/
theorem balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty (k : Type u) [Field k] [CharZero k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p] (I : X.IdealSheafData) {m : ℕ}
    (hm : 1 ≤ m) (h : orderAtLeastLocus I m = (∅ : Set X)) :
    balancedTunedSheaf k p I m = ⊤ := by
  rw [balancedTunedSheaf_eq]
  exact tunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty k p I hm (tuningExponent m) h

/- English proof (authored)
Use the bounded exponent presentation on both schemes. Smooth pullback commutes with each derivative iterate and preserves powers of ideal sheaves, so it carries each downstairs factor to the corresponding factor upstairs. It also preserves products and the supremum over the same bounded exponent vectors. Thus pullback gives exactly the tuned sheaf of the pulled-back ideal.
-/
theorem tunedSheaf_comap (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] [LocallyOfFiniteType (h ≫ p)]
    (I : X.IdealSheafData) (m s : ℕ) :
    tunedSheaf k (h ≫ p) (I.comap h) m s = (tunedSheaf k p I m s).comap h := by
  rw [tunedSheaf_eq_iSup_fin k (h ≫ p) (I.comap h) m s, tunedSheaf_eq_iSup_fin k p I m s,
    Scheme.IdealSheafData.comap_iSup]
  refine iSup_congr fun t => ?_
  have hfun : (fun j : ℕ =>
        derivIdealSheafIterate k (h ≫ p) j (I.comap h) ^ extendExponentsByZero m s t.1 j)
      = (fun J : X.IdealSheafData => J.comap h) ∘
        (fun j : ℕ => derivIdealSheafIterate k p j I ^ extendExponentsByZero m s t.1 j) := by
    funext j
    show derivIdealSheafIterate k (h ≫ p) j (I.comap h) ^ extendExponentsByZero m s t.1 j
        = (derivIdealSheafIterate k p j I ^ extendExponentsByZero m s t.1 j).comap h
    rw [derivIdealSheafIterate_comap k p h j I, Scheme.IdealSheafData.comap_pow]
  rw [Scheme.IdealSheafData.comap_listProd, List.map_map]
  exact congrArg List.prod
    (congrArg (fun F : ℕ → Y.IdealSheafData => List.map F (List.range m)) hfun)

/- English proof (authored)
Both balanced tuned sheaves use the tuning exponent of the same mark, so their thresholds agree. The smooth pullback identity for tuned sheaves at that threshold gives the claim.
-/
theorem balancedTunedSheaf_comap (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] [LocallyOfFiniteType (h ≫ p)]
    (I : X.IdealSheafData) (m : ℕ) :
    balancedTunedSheaf k (h ≫ p) (I.comap h) m = (balancedTunedSheaf k p I m).comap h := by
  rw [balancedTunedSheaf_eq, balancedTunedSheaf_eq]
  exact tunedSheaf_comap k p h I m (tuningExponent m)

end FunctorialResolution.EmbeddedResolution

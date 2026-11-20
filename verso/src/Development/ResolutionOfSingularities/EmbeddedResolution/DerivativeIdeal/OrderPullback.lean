import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Break down `eq_or_ne a ⊤ with rfl | ha` into its components or cases. Conclude with `Or.inr le_top`. Take `⟨m, rfl⟩` from `ENat.ne_top_iff_exists.1 ha`. Break down `Nat.lt_or_ge r m with hm | hm` into its components or cases. Conclude with `Or.inr (by exact_mod_cast hm)`.

Conclude with `Or.inl (by exact_mod_cast hm)`.
-/
private theorem le_natCast_or_succ_le (a : ℕ∞) (r : ℕ) :
    a ≤ (r : ℕ∞) ∨ ((r + 1 : ℕ) : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · exact Or.inr le_top
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 ha
    rcases Nat.lt_or_ge r m with hm | hm
    · exact Or.inr (by exact_mod_cast hm)
    · exact Or.inl (by exact_mod_cast hm)

/- English proof (translation)
Establish `key : h.appLE U V e ≫ Y.presheaf.germ V y hy = X.presheaf.germ U (h.base y) (e hy) ≫ h.stalkMap y`. Simplify using `only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]`. Conclude with `(Scheme.Hom.germ_stalkMap ..).symm`. Simplify `congrArg CommRingCat.Hom.hom key` using `only [CommRingCat.hom_comp]`.
-/
private theorem germ_comp_appLE {X Y : Scheme.{u}} (h : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ U) (y : Y) (hy : y ∈ V) :
    (Y.presheaf.germ V y hy).hom.comp (h.appLE U V e).hom
      = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) (e hy)).hom := by
  have key : h.appLE U V e ≫ Y.presheaf.germ V y hy
      = X.presheaf.germ U (h.base y) (e hy) ≫ h.stalkMap y := by
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    exact (Scheme.Hom.germ_stalkMap ..).symm
  simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom key

/- English proof (translation)
Take `⟨U, hU, hxU, -⟩` from `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (show h.base y ∈ (⊤ : X.Opens) from trivial)`. Take `⟨V, hV, hyV, e⟩` from `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (show y ∈ h ⁻¹ᵁ U from hxU)`. Establish `hcomp : (Y.presheaf.germ V y hyV).hom.comp (h.appLE U V e).hom = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) hxU).hom` using `germ_comp_appLE h U V e y hyV`. Rewrite using `[stalkIdeal_eq_map_germ (I.comap h) y ⟨V, hV⟩ hyV, stalkIdeal_eq_map_germ I (h.base y) ⟨U, hU⟩ hxU, Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨U, hU⟩ ⟨V, hV⟩ e, Ideal.map_map, Ideal.map_map]`. Conclude with `congrArg (fun φ => Ideal.map φ (I.ideal ⟨U, hU⟩)) hcomp`.
-/
theorem stalkIdeal_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (I : X.IdealSheafData) (y : Y) :
    stalkIdeal (I.comap h) y =
      Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y)) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (show h.base y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V, hV, hyV, e⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (show y ∈ h ⁻¹ᵁ U from hxU)
  have hcomp : (Y.presheaf.germ V y hyV).hom.comp (h.appLE U V e).hom
      = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) hxU).hom :=
    germ_comp_appLE h U V e y hyV
  rw [stalkIdeal_eq_map_germ (I.comap h) y ⟨V, hV⟩ hyV,
    stalkIdeal_eq_map_germ I (h.base y) ⟨U, hU⟩ hxU,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨U, hU⟩ ⟨V, hV⟩ e,
    Ideal.map_map, Ideal.map_map]
  exact congrArg (fun φ => Ideal.map φ (I.ideal ⟨U, hU⟩)) hcomp

/- English proof (translation)
Use `ENat.forall_natCast_le_iff_le.mp fun n hn => ?_` and prove the remaining obligations. Rewrite `hn`, the goal using `[le_orderAt_iff]`. Rewrite using `[stalkIdeal_comap]`. Establish `hmono : Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y)) ≤ Ideal.map (h.stalkMap y).hom (IsLocalRing.maximalIdeal (X.presheaf.stalk (h.base y)) ^ n)` using `Ideal.map_mono hn`. Conclude with `le_trans hmono (le_trans (Ideal.map_pow ..).le (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le ..) n))`.
-/
theorem orderAt_le_orderAt_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (I : X.IdealSheafData) (y : Y) :
    orderAt I (h.base y) ≤ orderAt (I.comap h) y := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_orderAt_iff] at hn ⊢
  rw [stalkIdeal_comap]
  have hmono : Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y))
      ≤ Ideal.map (h.stalkMap y).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (h.base y)) ^ n) := Ideal.map_mono hn
  exact le_trans hmono
    (le_trans (Ideal.map_pow ..).le
      (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le ..) n))

/- English proof (translation)
Establish `h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (J.comap h) y` using `by exact_mod_cast hy`. It suffices to establish `hs : ((1 : ℕ) : ℕ∞) ≤ orderAt J (h.base y) by exact_mod_cast hs`. Rewrite `h1`, the goal using `[le_orderAt_iff]`. Rewrite `h1` using `[stalkIdeal_comap, pow_one]`. Rewrite using `[pow_one]`.

Simplify `Ideal.le_comap_map.trans (Ideal.comap_mono h1)` using `only [IsLocalRing.maximalIdeal_comap]`.
-/
private theorem one_le_orderAt_of_one_le_orderAt_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (J : X.IdealSheafData)
    (y : Y) (hy : (1 : ℕ∞) ≤ orderAt (J.comap h) y) : (1 : ℕ∞) ≤ orderAt J (h.base y) := by
  have h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (J.comap h) y := by exact_mod_cast hy
  suffices hs : ((1 : ℕ) : ℕ∞) ≤ orderAt J (h.base y) by exact_mod_cast hs
  rw [le_orderAt_iff] at h1 ⊢
  rw [stalkIdeal_comap, pow_one] at h1
  rw [pow_one]
  simpa only [IsLocalRing.maximalIdeal_comap] using
    Ideal.le_comap_map.trans (Ideal.comap_mono h1)

/- English proof (translation)
Establish `: LocallyOfFiniteType p` using `inferInstance`. Establish `: LocallyOfFiniteType (h ≫ p)` using `inferInstance`. Use `le_antisymm ?_ (orderAt_le_orderAt_comap h I y)` and prove the remaining obligations. Break down `eq_or_ne (orderAt I (h.base y)) ⊤ with hI | hI` into its components or cases. Rewrite using `[hI]`.

Conclude with `le_top`. Take `⟨r, hr⟩` from `ENat.ne_top_iff_exists.1 hI`. Rewrite using `[← hr]`. Break down `le_natCast_or_succ_le (orderAt (I.comap h) y) r with hle | hlt` into its components or cases. Conclude with `hle`.

It suffices to derive a contradiction. Establish `h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (derivIdealSheafIterate k (h ≫ p) r (I.comap h)) y` using `le_orderAt_derivIdealSheafIterate k (h ≫ p) (I.comap h) y 1 r (by`. Rewrite using `[Nat.add_comm]`. Conclude with `hlt)`. Rewrite `h1` using `[derivIdealSheafIterate_comap k p h r I]`.

Establish `h2 : (1 : ℕ∞) ≤ orderAt ((derivIdealSheafIterate k p r I).comap h) y` using `by exact_mod_cast h1`. Establish `h3` using `one_le_orderAt_of_one_le_orderAt_comap h (derivIdealSheafIterate k p r I) y h2`. Establish `h4 : orderAt (derivIdealSheafIterate k p r I) (h.base y) = ((r - r : ℕ) : ℕ∞)` using `orderAt_derivIdealSheafIterate_eq_sub k p I (h.base y) hr.symm (le_refl r)`. Rewrite `h3` using `[h4, Nat.sub_self]`. Simplify using `at h3`.
-/
theorem orderAt_comap (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] (I : X.IdealSheafData) (y : Y) :
    orderAt (I.comap h) y = orderAt I (h.base y) := by
  have : LocallyOfFiniteType p := inferInstance
  have : LocallyOfFiniteType (h ≫ p) := inferInstance
  refine le_antisymm ?_ (orderAt_le_orderAt_comap h I y)
  rcases eq_or_ne (orderAt I (h.base y)) ⊤ with hI | hI
  · rw [hI]; exact le_top
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 hI
  rw [← hr]
  rcases le_natCast_or_succ_le (orderAt (I.comap h) y) r with hle | hlt
  · exact hle
  exfalso
  have h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (derivIdealSheafIterate k (h ≫ p) r (I.comap h)) y :=
    le_orderAt_derivIdealSheafIterate k (h ≫ p) (I.comap h) y 1 r (by
      rw [Nat.add_comm]; exact hlt)
  rw [derivIdealSheafIterate_comap k p h r I] at h1
  have h2 : (1 : ℕ∞) ≤ orderAt ((derivIdealSheafIterate k p r I).comap h) y := by exact_mod_cast h1
  have h3 := one_le_orderAt_of_one_le_orderAt_comap h (derivIdealSheafIterate k p r I) y h2
  have h4 : orderAt (derivIdealSheafIterate k p r I) (h.base y) = ((r - r : ℕ) : ℕ∞) :=
    orderAt_derivIdealSheafIterate_eq_sub k p I (h.base y) hr.symm (le_refl r)
  rw [h4, Nat.sub_self] at h3
  simp at h3

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Set.mem_preimage, mem_orderAtLeastLocus_iff, orderAt_comap k p h I y]`.
-/
theorem orderAtLeastLocus_comap (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] (I : X.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus (I.comap h) m = ⇑h.base ⁻¹' orderAtLeastLocus I m := by
  ext y
  simp only [Set.mem_preimage, mem_orderAtLeastLocus_iff, orderAt_comap k p h I y]

end FunctorialResolution.EmbeddedResolution

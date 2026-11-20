import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoVan

/- English proof (translation)
Establish `e` using `congrArg (fun φ => φ.hom u) (Proj.awayMap_awayToSection (grK K N) hy hz)`. Simplify using `only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e`. Simplify using `only [evV, RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[e, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]`.
-/
theorem evV_awayMap {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    {x y z : MvPolynomial (Fin (N + 1)) K} {b : ℕ} (hy : y ∈ grK K N b) (hz : z = x * y)
    (V : X.Opens) (h : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) z)
    (h' : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x) (u : HomogeneousLocalization.Away (grK K N) x) :
    evV i z V h (HomogeneousLocalization.awayMap (grK K N) hy hz u) = evV i x V h' u := by
  have e := congrArg (fun φ => φ.hom u) (Proj.awayMap_awayToSection (grK K N) hy hz)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [evV, RingHom.coe_comp, Function.comp_apply]
  rw [e, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/- English proof (translation)
Establish `e` using `congrArg (fun φ => φ.hom ((Proj.awayToSection (grK K N) g).hom u)) (Scheme.Hom.appLE_map i hW (homOfLE hVW).op)`. Conclude with `e.symm`.
-/
theorem evV_res {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    {g : MvPolynomial (Fin (N + 1)) K} {V W : X.Opens} (hVW : V ≤ W)
    (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g)
    (u : HomogeneousLocalization.Away (grK K N) g) :
    evV i g V hV u = resO hVW (evV i g W hW u) := by
  have e := congrArg (fun φ => φ.hom ((Proj.awayToSection (grK K N) g).hom u))
    (Scheme.Hom.appLE_map i hW (homOfLE hVW).op)
  exact e.symm

/- English proof (translation)
Use `ext`. Simplify using `only [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk, Localization.mk_mul]`. Use `Localization.mk_eq_mk_iff.mpr ?_` and prove the remaining obligations. Rewrite using `[Localization.r_iff_exists]`. Choose the witnesses `1`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem away_factor {K : Type} [Field K] {N : ℕ} {x g f : MvPolynomial (Fin (N + 1)) K} {e s : ℕ}
    (hx : x ∈ grK K N 1) (hg : g ∈ grK K N e) (hf : f ∈ grK K N (s • e))
    (hf' : f ∈ grK K N ((s • e) • 1)) (hc : g ^ s ∈ grK K N ((s • e) • 1)) :
    HomogeneousLocalization.awayMap (grK K N) hg (rfl : x * g = x * g)
        (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) f hf') =
      HomogeneousLocalization.awayMap (grK K N) hx (mul_comm x g)
          (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) *
        HomogeneousLocalization.awayMap (grK K N) hg (rfl : x * g = x * g)
          (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) (g ^ s) hc) := by
  ext
  simp only [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr ?_
  rw [Localization.r_iff_exists]
  use 1
  simp
  ring

/- English proof (translation)
Establish `hf' : f ∈ grK K N ((s • e) • 1)` using `by simpa using hf`. Establish `hc : g ^ s ∈ grK K N ((s • e) • 1)`. Use `SetLike.pow_mem_graded s hg` as an intermediate fact. Simplify using `using this`. Use `Ideal.subset_span ⟨s • e, hf', fun j => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hU : ((i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) : Set X).Nonempty`. Establish `hW : ((V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) : Set X).Nonempty` using `nonempty_preirreducible_inter V.isOpen (TopologicalSpace.Opens.isOpen _) hVne hU haveI : Nonempty (V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) := hW.to_subtype`. Establish `hx` using `xv_mem K N j`. Establish `hWU : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)` using `inf_le_right`. Establish `hWV : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤ V` using `inf_le_left`.

Establish `hWg` using `hWV.trans hV`. Establish `hWx : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j * g)`. Rewrite using `[Proj.basicOpen_mul]`. Conclude with `fun y hy => ⟨hWU hy, hWg hy⟩`. Apply `map_injective_of_isIntegral X (homOfLE hWU)` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use `(evV_res i hWU le_rfl hWU _).symm.trans ?_` and prove the remaining obligations. Rewrite using `[← evV_awayMap i hg rfl _ hWx hWU, away_factor hx hg hf hf' hc, map_mul, evV_awayMap i hx (mul_comm _ g) _ hWx hWg, evV_res i hWV hV hWg, h0, map_zero, zero_mul]`. Use `eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 ?_)` and prove the remaining obligations. Use `(X.basicOpen_le _).trans ?_` and prove the remaining obligations.

Introduce `y hy`. Conclude with `(hU ⟨y, hy⟩).elim`.
-/
theorem mem_homIdeal_of_vanish {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    (hX : IsIntegral X) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) {s : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (s • e))
    (V : X.Opens) (hVne : (V : Set X).Nonempty)
    (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g)
    (h0 : evV i g V hV (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0) :
    f ∈ homIdeal i := by
  have hf' : f ∈ grK K N ((s • e) • 1) := by simpa using hf
  have hc : g ^ s ∈ grK K N ((s • e) • 1) := by
    have := SetLike.pow_mem_graded s hg
    simpa using this
  refine Ideal.subset_span ⟨s • e, hf', fun j => ?_⟩
  by_cases hU : ((i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) : Set X).Nonempty
  · have hW : ((V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter V.isOpen (TopologicalSpace.Opens.isOpen _) hVne hU
    haveI : Nonempty (V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) := hW.to_subtype
    have hx := xv_mem K N j
    have hWU : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤
        i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) := inf_le_right
    have hWV : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤ V := inf_le_left
    have hWg := hWV.trans hV
    have hWx : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤
        i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j * g) := by
      rw [Proj.basicOpen_mul]
      exact fun y hy => ⟨hWU hy, hWg hy⟩
    apply map_injective_of_isIntegral X (homOfLE hWU)
    rw [map_zero]
    refine (evV_res i hWU le_rfl hWU _).symm.trans ?_
    rw [← evV_awayMap i hg rfl _ hWx hWU, away_factor hx hg hf hf' hc, map_mul,
      evV_awayMap i hx (mul_comm _ g) _ hWx hWg, evV_res i hWV hV hWg, h0, map_zero, zero_mul]
  · refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 ?_)
    refine (X.basicOpen_le _).trans ?_
    intro y hy
    exact (hU ⟨y, hy⟩).elim

end GlobalTheory.CompanionTheory.GeoVan

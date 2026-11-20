import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoUnit

/- English proof (translation)
Rewrite using `[HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk]`. Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Rewrite using `[HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one, Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]`. Conclude with `⟨1, by simp; ring⟩`.
-/
theorem awayMap_ratio_mul {K : Type} [Field K] {N e : ℕ} {a b : MvPolynomial (Fin (N + 1)) K}
    (ha : a ∈ grK K N e) (hb : b ∈ grK K N e) (hb1 : b ∈ grK K N (1 • e)) (ha1 : a ∈ grK K N (1 • e)) :
    HomogeneousLocalization.awayMap (grK K N) hb (x := a * b) rfl
        (HomogeneousLocalization.Away.mk _ ha 1 b hb1) *
      HomogeneousLocalization.awayMap (grK K N) ha (x := a * b) (mul_comm a b)
        (HomogeneousLocalization.Away.mk _ hb 1 a ha1) = 1 := by
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/- English proof (translation)
Establish `h0 : y 0 ∈ grK K N e` using `(MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hy 0)`. Establish `h1 : y k.succ ∈ grK K N e` using `(MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hy k.succ)`. Establish `h0' : y 0 ∈ grK K N (1 • e)` using `by rw [one_smul]; exact h0`. Establish `h1' : y k.succ ∈ grK K N (1 • e)` using `by rw [one_smul]; exact h1`. Establish `hle : Proj.basicOpen (grK K N) (y 0 * y k.succ) ≤ Proj.basicOpen (grK K N) (y 0)`.

Rewrite using `[Proj.basicOpen_mul]`. Conclude with `inf_le_left`. Establish `hU : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0 * y k.succ)`. Rewrite using `[Proj.basicOpen_mul]`. Conclude with `le_inf (hV.trans (iInf_le _ 0)) (hV.trans (iInf_le _ k.succ))`.

Establish `hu : IsUnit (HomogeneousLocalization.awayMap (grK K N) h1 (x` using `y 0 * y k.succ) rfl (HomogeneousLocalization.Away.mk _ h0 1 (y k.succ) h1')) := isUnit_iff_exists_inv.mpr ⟨_, awayMap_ratio_mul h0 h1 h1' h0'⟩`. Establish `e1` using `Scheme.Hom.map_appLE i hU (homOfLE hle).op`. Establish `e2` using `Proj.awayMap_awayToSection (grK K N) h1 (f := y 0) (x := y 0 * y k.succ) rfl`. Establish `key : tV i y hy V hV k = (Scheme.Hom.appLE i _ V hU).hom ((Proj.awayToSection (grK K N) (y 0 * y k.succ)).hom (HomogeneousLocalization.awayMap (grK K N) h1 (x` using `y 0 * y k.succ) rfl (HomogeneousLocalization.Away.mk _ h0 1 (y k.succ) h1'))) := by`. Unfold `tV yRatio`.

Rewrite using `[← e1, CommRingCat.hom_comp, RingHom.comp_apply]`. Use `congr 1`. Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, ← e2, CommRingCat.hom_comp, RingHom.comp_apply]`. Both sides reduce to the same expression. Rewrite using `[key]`.

Conclude with `(hu.map _).map _`.
-/
theorem tV_isUnit {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) (k : Fin d) : IsUnit (tV i y hy V hV k) := by
  have h0 : y 0 ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hy 0)
  have h1 : y k.succ ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hy k.succ)
  have h0' : y 0 ∈ grK K N (1 • e) := by rw [one_smul]; exact h0
  have h1' : y k.succ ∈ grK K N (1 • e) := by rw [one_smul]; exact h1
  have hle : Proj.basicOpen (grK K N) (y 0 * y k.succ) ≤ Proj.basicOpen (grK K N) (y 0) := by
    rw [Proj.basicOpen_mul]; exact inf_le_left
  have hU : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0 * y k.succ) := by
    rw [Proj.basicOpen_mul]
    exact le_inf (hV.trans (iInf_le _ 0)) (hV.trans (iInf_le _ k.succ))
  have hu : IsUnit (HomogeneousLocalization.awayMap (grK K N) h1 (x := y 0 * y k.succ) rfl
      (HomogeneousLocalization.Away.mk _ h0 1 (y k.succ) h1')) :=
    isUnit_iff_exists_inv.mpr ⟨_, awayMap_ratio_mul h0 h1 h1' h0'⟩
  have e1 := Scheme.Hom.map_appLE i hU (homOfLE hle).op
  have e2 := Proj.awayMap_awayToSection (grK K N) h1 (f := y 0) (x := y 0 * y k.succ) rfl
  have key : tV i y hy V hV k =
      (Scheme.Hom.appLE i _ V hU).hom ((Proj.awayToSection (grK K N) (y 0 * y k.succ)).hom
        (HomogeneousLocalization.awayMap (grK K N) h1 (x := y 0 * y k.succ) rfl
          (HomogeneousLocalization.Away.mk _ h0 1 (y k.succ) h1'))) := by
    unfold tV yRatio
    rw [← e1, CommRingCat.hom_comp, RingHom.comp_apply]
    congr 1
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← e2, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  rw [key]
  exact (hu.map _).map _

end GlobalTheory.CompanionTheory.GeoUnit

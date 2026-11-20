import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChF
open MvPowerSeries

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero (fun p => h p.1 p.2)`.
-/
private lemma gm_hs {R : Type} [CommRing R] {m n d : ℕ} (a : Fin m → Pt R n d)
    (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero (fun p => h p.1 p.2)

/- English proof (translation)
Establish `h` using `gm_hs (m := 2) ![a, b] (by`. Introduce `j i`. Use `fin_cases j`. Conclude with `ha i`. Conclude with `hb i)`.

Unfold `ev gmF`. Rewrite using `[subst_add h, subst_add h, subst_mul h, subst_X h, subst_X h]`. Both sides reduce to the same expression.
-/
private lemma ev_gm {R : Type} [CommRing R] {n r : ℕ} (a b : Pt R n r)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin r) :
    ev ![a, b] (gmF R r i) = a i + b i + a i * b i := by
  have h := gm_hs (m := 2) ![a, b] (by
    intro j i
    fin_cases j
    · exact ha i
    · exact hb i)
  unfold ev gmF
  rw [subst_add h, subst_add h, subst_mul h, subst_X h, subst_X h]
  rfl

/- English proof (translation)
Establish `h` using `gm_hs (m := 1) ![a] (by`. Introduce `j i`. Use `fin_cases j`. Conclude with `ha i)`. Establish `h1` using `ev_one ![a]`.

Unfold `ev at h1 ⊢`. Rewrite using `[subst_add h, h1, subst_X h]`. Both sides reduce to the same expression.
-/
private lemma ev_ch {R : Type} [CommRing R] {n r : ℕ} (a : Pt R n r)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin r) :
    ev ![a] (1 + X ((0 : Fin 1), i) : PS R 1 r) = 1 + a i := by
  have h := gm_hs (m := 1) ![a] (by
    intro j i
    fin_cases j
    exact ha i)
  have h1 := ev_one ![a]
  unfold ev at h1 ⊢
  rw [subst_add h, h1, subst_X h]
  rfl

/- English proof (translation)
Simplify using `[gmF]`.
-/
private lemma gm_const {R : Type} [CommRing R] {r : ℕ} (i : Fin r) :
    constantCoeff (gmF R r i) = 0 := by
  simp [gmF]

/- English proof (translation)
Simplify using `[pt]`.
-/
private lemma pt_const {R : Type} [CommRing R] {n r : ℕ} (j : Fin n) (i : Fin r) :
    constantCoeff (pt R r j i) = 0 := by
  simp [pt]

private def gmLaw (R : Type) [CommRing R] (r : ℕ) : FGLaw R r where
  F := gmF R r
  const := gm_const
  unit i := by
    rw [ev_gm _ _ (by simp) (pt_const _)]
    simp [pt]
  comm i := by
    rw [ev_gm _ _ (pt_const _) (pt_const _)]
    simp only [pt, gmF]
    ring
  assoc i := by
    have h : ∀ (j k : Fin 3) (l : Fin r), constantCoeff (ev (n := 3) ![pt R r j, pt R r k] (gmF R r l)) = 0 := by
      intro j k l
      rw [ev_gm _ _ (pt_const _) (pt_const _)]
      simp [pt]
    rw [ev_gm _ _ (h _ _) (pt_const _), ev_gm _ _ (pt_const _) (h _ _),
      ev_gm _ _ (pt_const _) (pt_const _), ev_gm _ _ (pt_const _) (pt_const _)]
    ring

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => intro i`. Simplify using `[mulF]`. Consider the case `succ N ih`. Introduce `i`.

Simplify using `only [mulF, addOf]`. Rewrite using `[ev_gm _ _ (by intro l; rw [ih]; simp) (pt_const _), ih]`. Simplify using `only [pt]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma mulF_gm (R : Type) [CommRing R] (r : ℕ) (N : ℕ) :
    ∀ i : Fin r, mulF (gmF R r) N i = (1 + X ((0 : Fin 1), i)) ^ N - 1 := by
  induction N with
  | zero => intro i; simp [mulF]
  | succ N ih =>
    intro i
    simp only [mulF, addOf]
    rw [ev_gm _ _ (by intro l; rw [ih]; simp) (pt_const _), ih]
    simp only [pt]
    ring

/- English proof (translation)
Introduce `R _ r`. Use `⟨⟨gmLaw R r, rfl⟩, fun i => ⟨⟨by simp, ?_⟩, ?_⟩, mulF_gm R r⟩` and prove the remaining obligations. Establish `hA : addOf (gmF R r) (pt R (n` using `2) r 0) (pt R (n := 2) r 1) = gmF R r := by`. Use function extensionality and compare the values at `l`. Unfold `addOf`.

Rewrite using `[ev_gm _ _ (pt_const _) (pt_const _)]`. Both sides reduce to the same expression. Rewrite using `[hA, ev_ch _ gm_const, ev_ch _ (pt_const _), ev_ch _ (pt_const _)]`. Simplify using `only [pt, gmF]`. Expand and normalize the polynomial expressions, which then agree.

Use function extensionality and compare the values at `j`. Simplify using `only [dl, map_add, coeff_one, coeff_X, Finsupp.single_eq_zero, one_ne_zero, if_false, zero_add, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), Prod.mk.injEq, true_and, Pi.single_apply]`.
-/
theorem gmLaw_chars_mul : ∀ (R : Type) [CommRing R] (r : ℕ), (∃ Gl : FGLaw R r, Gl.F = gmF R r) ∧ (∀ i : Fin r, IsCh (gmF R r) (1 + MvPowerSeries.X ((0 : Fin 1), i)) ∧ dl (1 + MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 r) = Pi.single i 1) ∧ ∀ (N : ℕ) (i : Fin r), mulF (gmF R r) N i = (1 + MvPowerSeries.X ((0 : Fin 1), i)) ^ N - 1 := by
  intro R _ r
  refine ⟨⟨gmLaw R r, rfl⟩, fun i => ⟨⟨by simp, ?_⟩, ?_⟩, mulF_gm R r⟩
  · have hA : addOf (gmF R r) (pt R (n := 2) r 0) (pt R (n := 2) r 1) = gmF R r := by
      funext l
      unfold addOf
      rw [ev_gm _ _ (pt_const _) (pt_const _)]
      rfl
    rw [hA, ev_ch _ gm_const, ev_ch _ (pt_const _), ev_ch _ (pt_const _)]
    simp only [pt, gmF]
    ring
  · classical
    funext j
    simp only [dl, map_add, coeff_one, coeff_X, Finsupp.single_eq_zero, one_ne_zero, if_false, zero_add,
      Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), Prod.mk.injEq, true_and, Pi.single_apply]

end GlobalTheory.ChF

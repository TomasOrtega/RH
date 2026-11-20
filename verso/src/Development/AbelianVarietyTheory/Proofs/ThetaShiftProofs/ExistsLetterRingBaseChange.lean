import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.LetterMap

def coeffMap {K L : Type} [Field K] [Field L] (f : K →+* L) : LaurentSeries K →+* LaurentSeries L where
  toFun g := HahnSeries.map g f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeffMap_coeff {K L : Type} [Field K] [Field L] (f : K →+* L) (g : LaurentSeries K) (m : ℤ) :
    (coeffMap f g).coeff m = f (g.coeff m) := rfl

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
/- English proof (translation)
Use extensionality with `n`. Express the relevant statement in the definitionally equal form `f ((HahnSeries.ofPowerSeries ℤ K g).coeff n) = _`. Rewrite using `[PowerSeries.coeff_coe, PowerSeries.coeff_coe]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem _root_.GlobalTheory.LetterMap.coeffMap_ofPowerSeries {K L : Type} [Field K] [Field L] (f : K →+* L)
    (g : PowerSeries K) :
    _root_.GlobalTheory.LetterMap.coeffMap f (HahnSeries.ofPowerSeries ℤ K g) =
      HahnSeries.ofPowerSeries ℤ L (PowerSeries.map f g) := by
  ext n
  change f ((HahnSeries.ofPowerSeries ℤ K g).coeff n) = _
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
/- English proof (translation)
Unfold `_root_.Formalism.L2.Pj.arcDet`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `τ _`. Establish `h : (Matrix.of fun i k ↦ (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁))) = (MvPolynomial.rename (Sigma.mk τ)).mapMatrix (Matrix.mvPolynomialX (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (LaurentSeries K₁))`. Use extensionality with `i k`.

Simplify using the standard rewrite rules. Rewrite using `[h, ← AlgHom.map_det]`. Introduce `h0`. Rewrite `h0` using `[map_eq_zero_iff _ (MvPolynomial.rename_injective _ sigma_mk_injective)]`. Conclude with `Matrix.det_mvPolynomialX_ne_zero _ _ h0`.
-/
theorem _root_.GlobalTheory.LetterMap.det_ne_zero (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (K₁ : Type) [Field K₁] :
    _root_.Formalism.L2.Pj.arcDet Dw K₁ ≠ 0 := by
  unfold _root_.Formalism.L2.Pj.arcDet
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have h : (Matrix.of fun i k ↦
      (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁))) =
      (MvPolynomial.rename (Sigma.mk τ)).mapMatrix
        (Matrix.mvPolynomialX (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (LaurentSeries K₁)) := by
    ext i k; simp
  rw [h, ← AlgHom.map_det]
  intro h0
  rw [map_eq_zero_iff _ (MvPolynomial.rename_injective _ sigma_mk_injective)] at h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ h0

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap (MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) (_root_.Formalism.L2.Pj.ArcS Dw K₁))`. Unfold `_root_.Formalism.L2.Pj.ArcS`. Conclude with `IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (_root_.GlobalTheory.LetterMap.det_ne_zero Dw K₁))`. Establish `hex : ∃ Q, algebraMap (MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) (_root_.Formalism.L2.Pj.ArcS Dw K₁) Q = algebraMap _ (_root_.Formalism.L2.Pj.ArcS Dw K₁) P` using `⟨P, rfl⟩`. Unfold `_root_.Formalism.L2.Pj.QAt.arcNum`.

Rewrite using `[dif_pos hex]`. Conclude with `hinj hex.choose_spec`.
-/
theorem _root_.GlobalTheory.LetterMap.num_algebraMap {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {K₁ : Type} [Field K₁]
    (P : MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) :
    _root_.Formalism.L2.Pj.QAt.arcNum (algebraMap _ (_root_.Formalism.L2.Pj.ArcS Dw K₁) P) = P := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) (_root_.Formalism.L2.Pj.ArcS Dw K₁)) := by
    unfold _root_.Formalism.L2.Pj.ArcS
    exact IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (_root_.GlobalTheory.LetterMap.det_ne_zero Dw K₁))
  have hex : ∃ Q, algebraMap (MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) (_root_.Formalism.L2.Pj.ArcS Dw K₁) Q =
      algebraMap _ (_root_.Formalism.L2.Pj.ArcS Dw K₁) P := ⟨P, rfl⟩
  unfold _root_.Formalism.L2.Pj.QAt.arcNum
  rw [dif_pos hex]
  exact hinj hex.choose_spec

/- English proof (translation)
Unfold `arcDet`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Use `congr 1`.

Use extensionality with `i k : 2`. Simplify using the standard rewrite rules.
-/
theorem map_arcDet (Dw : Datum H) {K L : Type} [Field K] [Field L] (f : K →+* L) :
    MvPolynomial.map (coeffMap f) (arcDet Dw K) = arcDet Dw L := by
  unfold arcDet
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i k : 2
  simp

def ringMap (Dw : Datum H) {K L : Type} [Field K] [Field L] (f : K →+* L) : ArcS Dw K →+* ArcS Dw L :=
  IsLocalization.Away.lift (arcDet Dw K)
    (g := (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) (ArcS Dw L)).comp (MvPolynomial.map (coeffMap f)))
    (by
      rw [RingHom.comp_apply, map_arcDet]
      exact IsLocalization.Away.algebraMap_isUnit (arcDet Dw L))

/- English proof (translation)
The claim follows from `IsLocalization.Away.lift_eq _ _ _`.
-/
theorem ringMap_algebraMap (Dw : Datum H) {K L : Type} [Field K] [Field L] (f : K →+* L)
    (P : MvPolynomial (ArcLt Dw) (LaurentSeries K)) :
    ringMap Dw f (algebraMap _ _ P) = algebraMap _ (ArcS Dw L) (MvPolynomial.map (coeffMap f) P) :=
  IsLocalization.Away.lift_eq _ _ _

/- English proof (translation)
Unfold `arcι`. Simplify using `only [RingHom.comp_apply]`. Use `erw [ringMap_algebraMap, MvPolynomial.map_C, coeffMap_ofPowerSeries]`. Apply the tactic sequence `try rfl`.
-/
theorem ringMap_arcι (Dw : Datum H) {K L : Type} [Field K] [Field L] (f : K →+* L) (g : PowerSeries K) :
    ringMap Dw f (arcι Dw K g) = arcι Dw L (PowerSeries.map f g) := by
  unfold arcι
  simp only [RingHom.comp_apply]
  erw [ringMap_algebraMap, MvPolynomial.map_C, coeffMap_ofPowerSeries]
  try rfl

end GlobalTheory.LetterMap

namespace GlobalTheory

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory.LieHt.NrmSq

/- English proof (translation)
The claim follows from `map_sum (AddMonoidHom.mk' (h.form σ x) (h.add_right σ x)) f s`.
-/
theorem form_sum_right {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (h : HermFam K V) (σ : K →+* ℂ) (x : V) {J : Type} (s : Finset J) (f : J → V) :
    h.form σ x (∑ k ∈ s, f k) = ∑ k ∈ s, h.form σ x (f k) :=
  map_sum (AddMonoidHom.mk' (h.form σ x) (h.add_right σ x)) f s

/- English proof (translation)
Rewrite using `[← h.conj_symm σ y, h.add_right, map_add, h.conj_symm, h.conj_symm]`.
-/
theorem form_add_left {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (h : HermFam K V) (σ : K →+* ℂ) (a b y : V) :
    h.form σ (a + b) y = h.form σ a y + h.form σ b y := by
  rw [← h.conj_symm σ y, h.add_right, map_add, h.conj_symm, h.conj_symm]

/- English proof (translation)
Rewrite using `[← h.conj_symm σ y, h.smul_right, map_mul, h.conj_symm]`.
-/
theorem form_smul_left {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (h : HermFam K V) (σ : K →+* ℂ) (c : K) (a y : V) :
    h.form σ (c • a) y = starRingEnd ℂ (σ c) * h.form σ a y := by
  rw [← h.conj_symm σ y, h.smul_right, map_mul, h.conj_symm]

/- English proof (translation)
The claim follows from `map_sum (AddMonoidHom.mk' (fun a => h.form σ a y) (fun a b => form_add_left h σ a b y)) f s`.
-/
theorem form_sum_left {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (h : HermFam K V) (σ : K →+* ℂ) (y : V) {J : Type} (s : Finset J) (f : J → V) :
    h.form σ (∑ k ∈ s, f k) y = ∑ k ∈ s, h.form σ (f k) y :=
  map_sum (AddMonoidHom.mk' (fun a => h.form σ a y) (fun a b => form_add_left h σ a b y)) f s

/- English proof (translation)
Establish `hv : ∀ v : Fin m → K, v = ∑ k, v k • (Pi.single k 1 : Fin m → K)`. Introduce `v`. Use extensionality with `l`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [hv y, hv z]`.

Rewrite using `[form_sum_left]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[form_smul_left, form_sum_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h.smul_right]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_expand {K : Type} [Field K] {m : ℕ} (h : HermFam K (Fin m → K)) (σ : K →+* ℂ)
    (y z : Fin m → K) :
    h.form σ y z = ∑ i, ∑ j, starRingEnd ℂ (σ (y i)) * σ (z j) *
      h.form σ (Pi.single i 1) (Pi.single j 1) := by
  have hv : ∀ v : Fin m → K, v = ∑ k, v k • (Pi.single k 1 : Fin m → K) := by
    intro v; ext l; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv y, hv z]
  rw [form_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [form_smul_left, form_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h.smul_right]; ring

/- English proof (translation)
Simplify using `only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_expand {m g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin m → Fin g → ℂ) (c : Fin m → ℂ) :
    hermForm Hm (∑ k, c k • W k) (∑ k, c k • W k) =
      ∑ j, ∑ i, c j * starRingEnd ℂ (c i) * hermForm Hm (W j) (W i) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.star_def]; ring

end GlobalTheory.LieHt.NrmSq

open GlobalTheory.LieHt.NrmSq in
/- English proof (translation)
Introduce `K K'' _ _ _ _ _ m g h h'' σ Hm W x hBC hH`. Establish `hbase : ∀ i j, h''.form σ (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (W j) (W i)`. Introduce `i j`. Rewrite using `[hBC σ i j, hH i j]`. Establish `hff : h''.form σ x x = (Real.pi : ℂ) * hermForm Hm (∑ k, σ (x k) • W k) (∑ k, σ (x k) • W k)`.

Rewrite using `[form_expand, hermForm_expand, Finset.mul_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hbase]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `HermFam.nrm`. Rewrite using `[hff, Complex.re_ofReal_mul]`.
-/
theorem GlobalTheory.LieHt.nrm_eq_sqrt_pi_hermForm : ∀ (K K'' : Type) [Field K] [NumberField K] [Field K''] [NumberField K''] [Algebra K K''] (m g : ℕ) (h : HermFam K (Fin m → K)) (h'' : HermFam K'' (Fin m → K'')) (σ : K'' →+* ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin m → Fin g → ℂ) (x : Fin m → K''), GlobalTheory.LieHt.IsBC h h'' → (∀ i j, h.form (σ.comp (algebraMap K K'')) (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (W j) (W i)) → h''.nrm σ x = √(Real.pi * (hermForm Hm (∑ k, σ (x k) • W k) (∑ k, σ (x k) • W k)).re) := by
  intro K K'' _ _ _ _ _ m g h h'' σ Hm W x hBC hH
  have hbase : ∀ i j, h''.form σ (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (W j) (W i) := by
    intro i j; rw [hBC σ i j, hH i j]
  have hff : h''.form σ x x = (Real.pi : ℂ) * hermForm Hm (∑ k, σ (x k) • W k) (∑ k, σ (x k) • W k) := by
    rw [form_expand, hermForm_expand, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbase]; ring
  unfold HermFam.nrm
  rw [hff, Complex.re_ofReal_mul]

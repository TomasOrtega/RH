import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EvalFrEqProdDetPowMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

/- English proof (translation)
Establish `hne : ∀ b i, T b i i ≠ 0`. Introduce `b i`. Establish `h1` using `hd b`. Rewrite `h1` using `[Matrix.det_of_isUpperTriangular (hT b)]`. Conclude with `(Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)`.

Set `t : Formalism.L2.Pj.Ix Dw → Kˣ` to `fun o => match o with`. Consider the case `none => 1`. Consider the case `some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)`. Establish `hb : FrBor t z z'`. Use `((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z z' z').1 t).2 ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩` and prove the remaining obligations.

Conclude with `hT τ hij`. Establish `hw` using `(GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 K inferInstance a n F hF t z z' hb`. Rewrite using `[hw]`. Use `congr 1`. Simplify using `only [wchar, Fintype.prod_option, Fintype.prod_sigma, t, Formalism.L2.Pj.ex, Units.val_one, one_pow, _root_.one_mul, Units.val_mk0]`.
-/
theorem evR_frChg_mul_triangular (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (F : Rul Xo c) (hF : F ∈ sec Xo c a n) (z z' : FrPt Xo c K)
    (T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (hT : ∀ b, (T b).BlockTriangular id)
    (hd : ∀ b, (T b).det ≠ 0) (h : FrChg (fun b => (T b).transpose) 1 z z') :
    evR Xo c F z' = (∏ b, ∏ i, T b i i ^ a (b, i)) * evR Xo c F z := by
  have hne : ∀ b i, T b i i ≠ 0 := by
    intro b i
    have h1 := hd b
    rw [Matrix.det_of_isUpperTriangular (hT b)] at h1
    exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
  let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)
  have hb : FrBor t z z' := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z z' z').1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩
    exact hT τ hij
  have hw := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 K inferInstance a n F hF
    t z z' hb
  rw [hw]
  congr 1
  simp only [wchar, Fintype.prod_option, Fintype.prod_sigma, t, Formalism.L2.Pj.ex, Units.val_one, one_pow, _root_.one_mul,
    Units.val_mk0]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c K _ _ _ y a n F hF`. Take `⟨P, N, hP⟩` from `GlobalTheory.LamT.RatFn.exists_poly_div_det E H Dw l Xo c K y a n F hF`. Establish `hrefl : FrMap (AlgHom.id c.F K) y y` using `GlobalTheory.Frames.frMapUniq_refl y`. Establish `hPK : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K), (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y z' → (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr P Y`. Introduce `z' Y hY h`.

Establish `h1` using `hP K (AlgHom.id c.F K) y z' Y (fun b => (hY b).isUnit) hrefl h`. Establish `h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P` using `MvPolynomial.map_id P`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Take `⟨G, hG⟩` from `GlobalTheory.LamT.evalFr_eq_prod_det_pow_mul K (E →+* ℂ) Dw.mult P (fun b i => a (b, i)) N (by`. Introduce `X b t hX ht htri`.

Set `T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K` to `Function.update (fun _ => 1) b t`. Establish `hTb : T b = t` using `Function.update_self ..`. Establish `hTo : ∀ b', b' ≠ b → T b' = 1` using `fun b' h => Function.update_of_ne h ..`. Establish `hTtri : ∀ b', (T b').BlockTriangular id`. Introduce `b'`.

Distinguish the cases in `h : b' = b`. Substitute `h` using the available equality. Rewrite using `[hTb]`. Conclude with `htri`. Rewrite using `[hTo b' h]`.

Conclude with `Matrix.blockTriangular_one`. Establish `hTd : ∀ b', (T b').det ≠ 0`. Introduce `b'`. Distinguish the cases in `h : b' = b`. Substitute `h` using the available equality.

Rewrite using `[hTb]`. Conclude with `ht`. Rewrite using `[hTo b' h]`. Simplify using the standard rewrite rules. Establish `hup : Function.update X b (X b * t) = fun b' => X b' * T b'`.

Use function extensionality and compare the values at `b'`. Distinguish the cases in `h : b' = b`. Substitute `h` using the available equality. Rewrite using `[hTb, Function.update_self]`. Rewrite using `[hTo b' h, Function.update_of_ne h, _root_.mul_one]`.

Take `⟨z₁, h₁, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (X b).transpose) 1 (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)`. Take `⟨z₂, h₂, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1 (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)`. Rewrite `h₁`, `h₂` using `[Units.val_one]`. Establish `h₃` using `(GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y z₁ z₂).2 _ _ _ _ h₁ h₂`. Simplify using `only [← Matrix.transpose_mul, _root_.mul_one] at h₃`.

Establish `e₁` using `hPK z₁ X hX h₁`. Establish `e₂` using `hPK z₂ (fun b' => X b' * T b') (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃`. Establish `e₃` using `evR_frChg_mul_triangular E H Dw l Xo c K a n F hF z₁ z₂ T hTtri hTd h₂`. Establish `p₁ : (∏ b', ∏ i, T b' i i ^ a (b', i)) = ∏ i, t i i ^ a (b, i)`. Rewrite using `[Finset.prod_eq_single b, hTb]`.

Introduce `b' _ h`. Rewrite using `[hTo b' h]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`.

Establish `p₂ : (∏ b', (X b' * T b').det) = (∏ b', (X b').det) * ∏ i, t i i`. Simplify using `only [Matrix.det_mul, Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single b, hTb, Matrix.det_of_isUpperTriangular htri]`. Introduce `b' _ h`.

Rewrite using `[hTo b' h]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`. Rewrite using `[hup, ← e₂, ← e₁, e₃, p₁, p₂]`.

Simplify using `only [pow_add, Finset.prod_mul_distrib, mul_pow, Finset.prod_pow]`. Use the proof step `ring)`. Use `⟨G, fun S _ _ φ z z' Y hY hz hz' => ?_⟩` and prove the remaining obligations. Establish `h1` using `hP S φ z z' Y hY hz hz'`. Rewrite `h1` using `[hG S φ.toRingHom Y]`.

Establish `hu : IsUnit ((∏ b, (Y b).det) ^ N)` using `(IsUnit.prod_univ_iff.2 hY).pow N`. Conclude with `hu.mul_left_cancel h1`.
-/
theorem exists_isFrPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ _ y a n F hF
  obtain ⟨P, N, hP⟩ := GlobalTheory.LamT.RatFn.exists_poly_div_det E H Dw l Xo c K y a n F hF
  have hrefl : FrMap (AlgHom.id c.F K) y y := GlobalTheory.Frames.frMapUniq_refl y
  have hPK : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr P Y := by
    intro z' Y hY h
    have h1 := hP K (AlgHom.id c.F K) y z' Y (fun b => (hY b).isUnit) hrefl h
    have h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P := MvPolynomial.map_id P
    rwa [h2] at h1
  obtain ⟨G, hG⟩ := GlobalTheory.LamT.evalFr_eq_prod_det_pow_mul K (E →+* ℂ) Dw.mult P (fun b i => a (b, i)) N (by
    intro X b t hX ht htri
    let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := Function.update (fun _ => 1) b t
    have hTb : T b = t := Function.update_self ..
    have hTo : ∀ b', b' ≠ b → T b' = 1 := fun b' h => Function.update_of_ne h ..
    have hTtri : ∀ b', (T b').BlockTriangular id := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact htri
      · rw [hTo b' h]; exact Matrix.blockTriangular_one
    have hTd : ∀ b', (T b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact ht
      · rw [hTo b' h]; simp
    have hup : Function.update X b (X b * t) = fun b' => X b' * T b' := by
      funext b'
      by_cases h : b' = b
      · subst h; rw [hTb, Function.update_self]
      · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
    obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (X b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
    obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
    rw [Units.val_one] at h₁ h₂
    have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y z₁ z₂).2 _ _ _ _ h₁ h₂
    simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
    have e₁ := hPK z₁ X hX h₁
    have e₂ := hPK z₂ (fun b' => X b' * T b')
      (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
    have e₃ := evR_frChg_mul_triangular E H Dw l Xo c K a n F hF z₁ z₂ T hTtri hTd h₂
    have p₁ : (∏ b', ∏ i, T b' i i ^ a (b', i)) = ∏ i, t i i ^ a (b, i) := by
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₂ : (∏ b', (X b' * T b').det) = (∏ b', (X b').det) * ∏ i, t i i := by
      simp only [Matrix.det_mul, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single b, hTb, Matrix.det_of_isUpperTriangular htri]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [hup, ← e₂, ← e₁, e₃, p₁, p₂]
    simp only [pow_add, Finset.prod_mul_distrib, mul_pow, Finset.prod_pow]
    ring)
  refine ⟨G, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  have h1 := hP S φ z z' Y hY hz hz'
  rw [hG S φ.toRingHom Y] at h1
  have hu : IsUnit ((∏ b, (Y b).det) ^ N) := (IsUnit.prod_univ_iff.2 hY).pow N
  exact hu.mul_left_cancel h1

end GlobalTheory.LamT

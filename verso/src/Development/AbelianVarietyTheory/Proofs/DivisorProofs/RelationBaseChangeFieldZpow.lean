import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrime
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIffStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLocalModelOverDvrStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitIntegralGeneratorPrincipalLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorAssociatedLocalGeneratorCMLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointEigenbasisChangeDetIntegralAlmostAllPrimeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialIntegerExponentDegreeEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.FrameRelBCZ

open Formalism.L2.LamCM GlobalTheory.Frames GlobalTheory.LamT.FieldPoly

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c K _ _ y₀ e k F hF G hG S _ _ φ z z' Y s hY hz hz'`. Establish `hS : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective`. Use `haveI : Infinite K := inferInstance`. Take `⟨P, N, hP⟩` from `GlobalTheory.FrameDenseZ.exists_poly_div_det_secZ E H Dw l Xo c K y₀ e F hF`.

Establish `hevK : ∀ (n : (E →+* ℂ) → ℕ) (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K), evalFr (∏ b, blockDetPoly K Dw.mult b ^ n b) X = ∏ b, (X b).det ^ n b` using `fun n X => by`. Simplify using `only [← evalFr_blockDetPoly Dw.mult _ X]`. Simplify using `only [evalFr, map_prod, map_pow]`. Establish `hevS : ∀ (n : (E →+* ℂ) → ℕ) (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S), evalFr (MvPolynomial.map φ.toRingHom (∏ b, blockDetPoly K Dw.mult b ^ n b)) X = ∏ b, (X b).det ^ n b` using `fun n X => by`. Simplify using `only [← evalFr_map_blockDetPoly φ.toRingHom Dw.mult _ X]`.

Simplify using `only [evalFr, map_prod, map_pow]`. Establish `hid : (∏ b, blockDetPoly K Dw.mult b ^ N) * G = (∏ b, blockDetPoly K Dw.mult b ^ k b) * P`. Assume the negation of the conclusion as `hne`. Take `⟨X, hX, hX0⟩` from `GlobalTheory.FrameDenseZ.exists_frame_evalFr_ne_zero Dw.mult _ (sub_ne_zero.2 hne)`. Take `⟨y', hy', -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1 (fun b => by rw [Matrix.det_transpose]; exact (hX b).isUnit)`.

Rewrite `hy'` using `[Units.val_one]`. Establish `h1` using `hG y' X hX hy'`. Establish `h2` using `hP K (AlgHom.id c.F K) y₀ y' X (fun b => (hX b).isUnit) (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K K (AlgHom.id c.F K) y₀).2.1 hy'`. Rewrite `h2` using `[show (AlgHom.id c.F K).toRingHom = RingHom.id K from rfl, MvPolynomial.map_id]`. Apply `hX0` to reduce the goal to its premises.

Establish `e1 : evalFr ((∏ b, blockDetPoly K Dw.mult b ^ N) * G - (∏ b, blockDetPoly K Dw.mult b ^ k b) * P) X = evalFr (∏ b, blockDetPoly K Dw.mult b ^ N) X * evalFr G X - evalFr (∏ b, blockDetPoly K Dw.mult b ^ k b) X * evalFr P X`. Simplify using `only [evalFr, map_mul, map_sub]`. Rewrite using `[e1, hevK, hevK, ← h1, ← h2, Finset.prod_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hidS : (∏ b, (Y b).det ^ N) * evalFr (MvPolynomial.map φ.toRingHom G) Y = (∏ b, (Y b).det ^ k b) * evalFr (MvPolynomial.map φ.toRingHom P) Y`.

Establish `h` using `congrArg (fun Q => evalFr (MvPolynomial.map φ.toRingHom Q) Y) hid`. Rewrite using `[← hevS, ← hevS]`. Simplify `h` using `only [evalFr, map_mul]`. Establish `hYt : ∀ b, IsUnit ((Y b).transpose.det)` using `fun b => by`. Rewrite using `[Matrix.det_transpose]`.

Conclude with `(hY b).isUnit`. Take `⟨z1, h1, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (Y b).transpose) 1 hYt`. Take `⟨z2, h2, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z1 (fun _ => 1) s (fun _ => by simp)`. Establish `h3` using `(GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S z z1 z2).2 _ _ _ _ h1 h2`. Simplify using `only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3`.

Establish `e' : z2 = z'` using `(GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (Y b).transpose) s hYt).unique h3 hz'`. Substitute `e'` using the available equality. Set `t : Formalism.L2.Pj.Ix Dw → Sˣ` to `fun i => match i with`. Consider the case `none => s`. Consider the case `some _ => 1`.

Establish `hb : FrBor t z1 z2` using `((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S z1 z2 z2).1 t).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩`. Establish `hw` using `GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF S t z1 z2 hb`. Establish `ht1 : ((∏ i, t i ^ e i : Sˣ) : S) = ((s ^ e none : Sˣ) : S)`. Simplify using `[Fintype.prod_option, t]`. Rewrite `hw` using `[ht1]`.

Establish `hv` using `hP S φ z z1 Y (fun b => (hY b).isUnit) hz h1`. Rewrite using `[hw]`. Establish `hu : (∏ b, (Y b).det ^ N) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hY b)`. Apply `mul_left_cancel₀ hu` to reduce the goal to its premises. Establish `hre : (∏ b, (Y b).det ^ N) * (((s ^ e none : Sˣ) : S) * evalFr (MvPolynomial.map φ.toRingHom G) Y) = ((s ^ e none : Sˣ) : S) * ((∏ b, (Y b).det ^ N) * evalFr (MvPolynomial.map φ.toRingHom G) Y)` using `by ring`.

Rewrite using `[hre, hidS, ← hv, Finset.prod_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem relation_baseChange_field_zpow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      (∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
      ∀ (S : Type) [Field S] [Algebra c.F S] (φ : K →ₐ[c.F] S) (z z' : FrPt Xo c S)
        (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S) (s : Sˣ),
        (∀ b, (Y b).det ≠ 0) → FrMap φ y₀ z → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : S) z z' →
        (∏ b, (Y b).det ^ k b) * evR Xo c F z' =
          ((s ^ e none : Sˣ) : S) * Formalism.L2.LamCM.evalFr (MvPolynomial.map φ.toRingHom G) Y := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k F hF G hG S _ _ φ z z' Y s hY hz hz'
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  haveI : Infinite K := inferInstance
  obtain ⟨P, N, hP⟩ := GlobalTheory.FrameDenseZ.exists_poly_div_det_secZ E H Dw l Xo c K y₀ e F hF

  have hevK : ∀ (n : (E →+* ℂ) → ℕ) (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      evalFr (∏ b, blockDetPoly K Dw.mult b ^ n b) X = ∏ b, (X b).det ^ n b := fun n X => by
    simp only [← evalFr_blockDetPoly Dw.mult _ X]
    simp only [evalFr, map_prod, map_pow]
  have hevS : ∀ (n : (E →+* ℂ) → ℕ) (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S),
      evalFr (MvPolynomial.map φ.toRingHom (∏ b, blockDetPoly K Dw.mult b ^ n b)) X = ∏ b, (X b).det ^ n b :=
    fun n X => by
    simp only [← evalFr_map_blockDetPoly φ.toRingHom Dw.mult _ X]
    simp only [evalFr, map_prod, map_pow]

  have hid : (∏ b, blockDetPoly K Dw.mult b ^ N) * G = (∏ b, blockDetPoly K Dw.mult b ^ k b) * P := by
    by_contra hne
    obtain ⟨X, hX, hX0⟩ := GlobalTheory.FrameDenseZ.exists_frame_evalFr_ne_zero Dw.mult _ (sub_ne_zero.2 hne)
    obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
      (fun b => by rw [Matrix.det_transpose]; exact (hX b).isUnit)
    rw [Units.val_one] at hy'
    have h1 := hG y' X hX hy'
    have h2 := hP K (AlgHom.id c.F K) y₀ y' X (fun b => (hX b).isUnit)
      (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K K (AlgHom.id c.F K) y₀).2.1 hy'
    rw [show (AlgHom.id c.F K).toRingHom = RingHom.id K from rfl, MvPolynomial.map_id] at h2
    apply hX0
    have e1 : evalFr ((∏ b, blockDetPoly K Dw.mult b ^ N) * G - (∏ b, blockDetPoly K Dw.mult b ^ k b) * P) X
        = evalFr (∏ b, blockDetPoly K Dw.mult b ^ N) X * evalFr G X
          - evalFr (∏ b, blockDetPoly K Dw.mult b ^ k b) X * evalFr P X := by
      simp only [evalFr, map_mul, map_sub]
    rw [e1, hevK, hevK, ← h1, ← h2, Finset.prod_pow]
    ring

  have hidS : (∏ b, (Y b).det ^ N) * evalFr (MvPolynomial.map φ.toRingHom G) Y
      = (∏ b, (Y b).det ^ k b) * evalFr (MvPolynomial.map φ.toRingHom P) Y := by
    have h := congrArg (fun Q => evalFr (MvPolynomial.map φ.toRingHom Q) Y) hid
    rw [← hevS, ← hevS]
    simpa only [evalFr, map_mul] using h

  have hYt : ∀ b, IsUnit ((Y b).transpose.det) := fun b => by
    rw [Matrix.det_transpose]; exact (hY b).isUnit
  obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (Y b).transpose) 1 hYt
  obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z1 (fun _ => 1) s (fun _ => by simp)
  have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S z z1 z2).2 _ _ _ _ h1 h2
  simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
  have e' : z2 = z' := (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (Y b).transpose) s hYt).unique h3 hz'
  subst e'
  let t : Formalism.L2.Pj.Ix Dw → Sˣ := fun i => match i with
    | none => s
    | some _ => 1
  have hb : FrBor t z1 z2 := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S z1 z2 z2).1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩
  have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF S t z1 z2 hb
  have ht1 : ((∏ i, t i ^ e i : Sˣ) : S) = ((s ^ e none : Sˣ) : S) := by
    simp [Fintype.prod_option, t]
  rw [ht1] at hw
  have hv := hP S φ z z1 Y (fun b => (hY b).isUnit) hz h1
  rw [hw]
  have hu : (∏ b, (Y b).det ^ N) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hY b)
  apply mul_left_cancel₀ hu
  have hre : (∏ b, (Y b).det ^ N) * (((s ^ e none : Sˣ) : S) * evalFr (MvPolynomial.map φ.toRingHom G) Y) =
      ((s ^ e none : Sˣ) : S) * ((∏ b, (Y b).det ^ N) * evalFr (MvPolynomial.map φ.toRingHom G) Y) := by ring
  rw [hre, hidS, ← hv, Finset.prod_pow]
  ring

end GlobalTheory.FrameRelBCZ

namespace GlobalTheory.FrameHomZ

open Formalism.L2.LamCM GlobalTheory.LamT.FieldPoly GlobalTheory.FrameHom

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c K _ _ y₀ e k F hF G hG μ hμ`. Establish `: CharZero K` using `charZero_of_injective_algebraMap (algebraMap c.F K).injective`. Establish `hS : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Establish `h2 : (2 : K) ≠ 0` using `two_ne_zero`. Establish `hev : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K, evalFr (∏ b, blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det` using `fun Y => by`.

Simplify using `only [← evalFr_blockDetPoly Dw.mult _ Y]`. Simplify using `only [evalFr, map_prod]`. Establish `hDp : (∏ b, blockDetPoly K Dw.mult b) ≠ 0` using `fun h0 => by`. Establish `h1` using `hev fun _ => 1`. Rewrite `h1` using `[h0]`.

Simplify using `[evalFr] at h1`. Use `degree_eq_of_scaling_zpow G _ hDp _ (fun x hx => ?_) μ hμ` and prove the remaining obligations. Set `X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K` to `fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩`. Set `T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K` to `fun b => Matrix.diagonal fun _ => 2`. Establish `hX : ∀ b, (X b).det ≠ 0` using `fun b => by`.

Establish `h1 : (∏ b, (X b).det) ≠ 0` using `by rw [← hev X]; exact hx`. Conclude with `(Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)`. Establish `hTd : ∀ b, (T b).det ≠ 0` using `fun b => by simp [T]`. Take `⟨z₁, h₁, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1 (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)`. Take `⟨z₂, h₂, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1 (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)`.

Rewrite `h₁`, `h₂` using `[Units.val_one]`. Establish `h₃` using `(GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂`. Simplify using `only [← Matrix.transpose_mul, _root_.mul_one] at h₃`. Set `t : Ix Dw → Kˣ` to `fun o => match o with`. Consider the case `none => 1`.

Consider the case `some _ => Units.mk0 2 h2`. Establish `hb : FrBor t z₁ z₂`. Use `((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z₁ z₂ z₂).1 t).2 ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => ?_, h₂⟩` and prove the remaining obligations. Simplify using `[T, Matrix.transpose_apply, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]`. Simplify using `[T, t]`.

Establish `e₁` using `hG z₁ X hX h₁`. Establish `e₂` using `hG z₂ (fun b' => X b' * T b') (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃`. Establish `e₃` using `evR_frBor_of_mem_secZ hS Xo c e hF K t z₁ z₂ hb`. Establish `p₁ : ((∏ i, t i ^ e i : Kˣ) : K) = (2 : K) ^ (∑ b, ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩))`. Rewrite using `[Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]`.

Simplify using `only [t, one_zpow, Units.val_one, _root_.one_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]`. Rewrite using `[← prod_zpow_eq_zpow_sum h2]`. Conclude with `Finset.prod_congr rfl fun b _ => prod_zpow_eq_zpow_sum h2 _ _`. Establish `p₂ : (∏ b, (X b * T b).det ^ k b) = (2 : K) ^ (∑ b, (Dw.mult b : ℤ) * (k b : ℤ)) * ∏ b, (X b).det ^ k b`. Rewrite using `[← prod_zpow_eq_zpow_sum h2, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Simplify using `only [T, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[show ((Dw.mult b : ℤ) * (k b : ℤ)) = ((Dw.mult b * k b : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `p₃ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G`. Unfold `evalFr`. Use `congr 2`. Use function extensionality and compare the values at `v`. Simplify using `only [T, Matrix.mul_diagonal, X, Matrix.of_apply]`.

Conclude with `mul_comm _ _`. Establish `p₄ : evalFr G X = MvPolynomial.eval x G` using `rfl`. Rewrite using `[← p₃, ← e₂, p₂, e₃, p₁, ← p₄, ← e₁, Finset.sum_add_distrib, zpow_add₀ h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frPoly_secZ_degree_eq_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      (∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
      ∀ μ, MvPolynomial.coeff μ G ≠ 0 →
        (μ.degree : ℤ) = ∑ b, ((Dw.mult b : ℤ) * (k b : ℤ) + ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k F hF G hG μ hμ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hev : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K,
      evalFr (∏ b, blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← evalFr_blockDetPoly Dw.mult _ Y]
    simp only [evalFr, map_prod]
  have hDp : (∏ b, blockDetPoly K Dw.mult b) ≠ 0 := fun h0 => by
    have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  refine degree_eq_of_scaling_zpow G _ hDp _ (fun x hx => ?_) μ hμ
  let X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K :=
    fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
  let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.diagonal fun _ => 2
  have hX : ∀ b, (X b).det ≠ 0 := fun b => by
    have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact hx
    exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)
  have hTd : ∀ b, (T b).det ≠ 0 := fun b => by simp [T]
  obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
  obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
  rw [Units.val_one] at h₁ h₂
  have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
  simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
  let t : Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some _ => Units.mk0 2 h2
  have hb : FrBor t z₁ z₂ := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z₁ z₂ z₂).1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => ?_, h₂⟩
    · simp [T, Matrix.transpose_apply, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
    · simp [T, t]
  have e₁ := hG z₁ X hX h₁
  have e₂ := hG z₂ (fun b' => X b' * T b')
    (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
  have e₃ := evR_frBor_of_mem_secZ hS Xo c e hF K t z₁ z₂ hb
  have p₁ : ((∏ i, t i ^ e i : Kˣ) : K) = (2 : K) ^ (∑ b, ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
    rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
    simp only [t, one_zpow, Units.val_one, _root_.one_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [← prod_zpow_eq_zpow_sum h2]
    exact Finset.prod_congr rfl fun b _ => prod_zpow_eq_zpow_sum h2 _ _
  have p₂ : (∏ b, (X b * T b).det ^ k b) = (2 : K) ^ (∑ b, (Dw.mult b : ℤ) * (k b : ℤ)) * ∏ b, (X b).det ^ k b := by
    rw [← prod_zpow_eq_zpow_sum h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Matrix.det_mul]
    simp only [T, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show ((Dw.mult b : ℤ) * (k b : ℤ)) = ((Dw.mult b * k b : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
    ring
  have p₃ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G := by
    unfold evalFr
    congr 2
    funext v
    simp only [T, Matrix.mul_diagonal, X, Matrix.of_apply]
    exact mul_comm _ _
  have p₄ : evalFr G X = MvPolynomial.eval x G := rfl
  rw [← p₃, ← e₂, p₂, e₃, p₁, ← p₄, ← e₁, Finset.sum_add_distrib, zpow_add₀ h2]
  ring

end GlobalTheory.FrameHomZ

namespace GlobalTheory.FrameCoeffLocZ

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ z f La hz e k p T iK hT hiK M`. Introduce `φ yT y' g a hφ hyT hy' ha hg hL hS cl hcl F hF hv G hG μ`. Set `io : c.F →+* T.Fr` to `iK.comp (algebraMap c.F z.K)`. Use `letI := io.toAlgebra`. Establish `hτ : (∏ b, (g b).det ^ k b) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hg b).ne_zero`.

Establish `hyx : yT.x = spMap iK ≫ z.x` using `by rw [hyT.1, hφ, hz.2.2.2.1]`. Establish `main : ∃ w : T.V, MvPolynomial.coeff μ (MvPolynomial.C (a ^ e none) * MvPolynomial.map iK G) * ∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v = (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w`. Use `Formalism.L2.LamCM.coeff_integral_local T.V T.Fr _ Dw.mult (MvPolynomial.C (a ^ e none) * MvPolynomial.map iK G) (fun b => (g b)⁻¹) cl _ inferInstance hT hτ (fun b => (Matrix.isUnit_nonsing_inv_det _ (hg b)).ne_zero) hcl ?_ μ` and prove the remaining obligations. Introduce `W KW _ _ _ _ _ _ _ fW hW hWf _ hfW Y X hX hXY`. Establish `hinj : Function.Injective (algebraMap T.V W)`.

Introduce `x y h`. Apply `IsFractionRing.injective T.V T.Fr` to reduce the goal to its premises. Apply `fW.injective` to reduce the goal to its premises. Rewrite using `[hfW, hfW, h]`. Use `haveI : CharZero W := charZero_of_injective_ringHom hinj`.

Set `T' : Formalism.L2.Pj.CDVR` to `⟨W⟩`. Set `κ : KW →+* T'.Fr` to `((FractionRing.algEquiv W KW).symm : KW ≃ₐ[W] FractionRing W).toRingEquiv.toRingHom`. Establish `hκ : ∀ w : W, κ (algebraMap W KW w) = algebraMap T'.V T'.Fr w` using `fun w => (FractionRing.algEquiv W KW).symm.commutes w`. Set `i : T.Fr →+* T'.Fr` to `κ.comp fW`. Establish `hψ : (algebraMap T'.V T'.Fr).comp (algebraMap T.V W) = i.comp (algebraMap T.V T.Fr)`.

Use extensionality with `x`. Use `show _ = κ (fW _)`. Rewrite using `[hfW, hκ]`. Both sides reduce to the same expression. Use `letI := (i.comp io).toAlgebra`.

Set `iA : T.Fr →ₐ[c.F] T'.Fr` to `{ i with commutes' := fun _ => rfl }`. Take `⟨yW, hyW⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA yT`. Take `⟨y'', hy''⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA y'`. Establish `hc` using `(GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c _ _ iA yT y' yW y'' g a hy' hyW).1 hy''`. Establish `hXt : ∀ b, IsUnit ((X b).transpose : Matrix _ _ T'.V).det` using `fun b => by`.

Rewrite using `[Matrix.det_transpose]`. Conclude with `hX b`. Establish `hXu : ∀ b, IsUnit (((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr)).det` using `fun b => by`. Use `(hXt b).map (algebraMap T'.V T'.Fr)` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis.

Take `⟨w, hw, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T'.Fr y'' _ 1 hXu`. Establish `hint` using `GlobalTheory.LamT.LocClause.integral_baseChange_chg z T T' iK M (algebraMap T.V W) i hψ io iA y' y'' w (fun b => (X b).transpose) rfl (hy'.1.trans hyx) hL hS hy'' hXt hw`. Take `⟨w₀, hw₀⟩` from `GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg E H Dw l Xo c F hv T' (i.comp io) hWf w hint`. Establish `hYX : ∀ b, (Y b).transpose = ((X b).map (algebraMap W KW)).transpose * (g b).map fW` using `fun b => by`. Rewrite using `[← hXY b, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (hg b)]`.

Simplify using the standard rewrite rules. Establish `hYX' : ∀ b, ((Y b).map κ).transpose = ((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr) * (g b).map iA` using `fun b => by`. Rewrite using `[← Matrix.transpose_map, hYX b, Matrix.map_mul]`. Use `congr 1`. Use extensionality with `j k`.

Conclude with `hκ _`. Establish `hdet : ∀ b, ((Y b).map κ).det = algebraMap T'.V T'.Fr (X b).det * i (g b).det` using `fun b => by`. Rewrite using `[← Matrix.det_transpose, hYX' b, Matrix.det_mul]`. Use `congr 1`. Rewrite using `[← Matrix.det_transpose (X b)]`.

Conclude with `(RingHom.map_det _ _).symm`. Conclude with `(RingHom.map_det i (g b)).symm`. Establish `hYd : ∀ b, ((Y b).map κ).det ≠ 0` using `fun b => by`. Rewrite using `[hdet b]`. Conclude with `mul_ne_zero ((hX b).map (algebraMap T'.V T'.Fr)).ne_zero ((map_ne_zero i).2 (hg b).ne_zero)`.

Establish `hsn : (iA a : T'.Fr) ≠ 0` using `(map_ne_zero iA).2 ha`. Establish `hc' : GlobalTheory.Frames.FrChg (fun b => ((Y b).map κ).transpose) ((Units.mk0 (iA a) hsn : T'.Frˣ) : T'.Fr) yW w`. Establish `c2` using `(GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c T'.Fr yW y'' w).2 _ _ _ _ hc hw`. Simplify `c2` using `[hYX']`. Establish `hbc` using `GlobalTheory.FrameRelBCZ.relation_baseChange_field_zpow E H Dw l Xo c z.K z.y e k F hF G hG T'.Fr (iA.comp φ) yW w (fun b => (Y b).map κ) (Units.mk0 (iA a) hsn) hYd (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ iA hyT hyW) hc'`.

Use `⟨(∏ b, (X b).det ^ k b) * w₀, κ.injective ?_⟩` and prove the remaining obligations. Establish `hP : MvPolynomial.map κ (MvPolynomial.map fW (MvPolynomial.C (a ^ e none) * MvPolynomial.map iK G)) = MvPolynomial.C ((iA a) ^ e none) * MvPolynomial.map (iA.comp φ).toRingHom G`. Rewrite using `[map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_map, MvPolynomial.map_map, ← hφ, map_zpow₀, map_zpow₀]`. Both sides reduce to the same expression. Establish `hu : ((Units.mk0 (iA a) hsn ^ e none : T'.Frˣ) : T'.Fr) = (iA a) ^ e none` using `by simp`.

Rewrite using `[GlobalTheory.LamT.LocClause.map_evalFr, hP, Formalism.L2.LamCM.evalFr_C_mul, ← hu, ← hbc, ← hw₀]`. Simplify using `only [hdet, map_mul, map_prod, map_pow, hκ, Finset.prod_mul_distrib, mul_pow]`. Use `show _ = (∏ b, i (g b).det ^ k b) * _`. Expand and normalize the polynomial expressions, which then agree. Take `⟨w, hw⟩` from `main`.

Conclude with `⟨w, by rw [← hw, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]; ring⟩`.
-/
theorem coeff_mul_prod_zpow_mem_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr), T.FinRes →
      (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ (M : GlobalTheory.LamT.LocMod z T iK),
      letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
      ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
        (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
        φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → a ≠ 0 → (∀ b, IsUnit (g b).det) →
        GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → GlobalTheory.LamT.SecInt T M.m1 M.m2 y'.s →
        ∀ cl : ∀ b : E →+* ℂ, Fin (Dw.mult b) → T.Fr,
          (∀ b j i, cl b j * (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
        ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, ∃ w : T.V, iK (MvPolynomial.coeff μ G) * (∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v) * a ^ e none =
          (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k p T iK hT hiK M
  intro φ yT y' g a hφ hyT hy' ha hg hL hS cl hcl F hF hv G hG μ
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  have hτ : (∏ b, (g b).det ^ k b) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hg b).ne_zero
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hφ, hz.2.2.2.1]
  have main : ∃ w : T.V, MvPolynomial.coeff μ (MvPolynomial.C (a ^ e none) * MvPolynomial.map iK G) * ∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v =
      (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w := by
    refine Formalism.L2.LamCM.coeff_integral_local T.V T.Fr _ Dw.mult (MvPolynomial.C (a ^ e none) * MvPolynomial.map iK G) (fun b => (g b)⁻¹) cl _
      inferInstance hT hτ (fun b => (Matrix.isUnit_nonsing_inv_det _ (hg b)).ne_zero) hcl ?_ μ
    intro W KW _ _ _ _ _ _ _ fW hW hWf _ hfW Y X hX hXY
    have hinj : Function.Injective (algebraMap T.V W) := by
      intro x y h
      apply IsFractionRing.injective T.V T.Fr
      apply fW.injective
      rw [hfW, hfW, h]
    haveI : CharZero W := charZero_of_injective_ringHom hinj
    let T' : Formalism.L2.Pj.CDVR := ⟨W⟩
    let κ : KW →+* T'.Fr := ((FractionRing.algEquiv W KW).symm : KW ≃ₐ[W] FractionRing W).toRingEquiv.toRingHom
    have hκ : ∀ w : W, κ (algebraMap W KW w) = algebraMap T'.V T'.Fr w := fun w =>
      (FractionRing.algEquiv W KW).symm.commutes w
    let i : T.Fr →+* T'.Fr := κ.comp fW
    have hψ : (algebraMap T'.V T'.Fr).comp (algebraMap T.V W) = i.comp (algebraMap T.V T.Fr) := by
      ext x
      show _ = κ (fW _)
      rw [hfW, hκ]
      rfl
    letI := (i.comp io).toAlgebra
    let iA : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
    obtain ⟨yW, hyW⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA yT
    obtain ⟨y'', hy''⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA y'
    have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c _ _ iA yT y' yW y'' g a hy' hyW).1 hy''
    have hXt : ∀ b, IsUnit ((X b).transpose : Matrix _ _ T'.V).det := fun b => by
      rw [Matrix.det_transpose]; exact hX b
    have hXu : ∀ b, IsUnit (((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr)).det := fun b => by
      have := (hXt b).map (algebraMap T'.V T'.Fr)
      rwa [RingHom.map_det] at this
    obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T'.Fr y'' _ 1 hXu
    have hint := GlobalTheory.LamT.LocClause.integral_baseChange_chg z T T' iK M (algebraMap T.V W) i hψ io iA y' y'' w
      (fun b => (X b).transpose) rfl (hy'.1.trans hyx) hL hS hy'' hXt hw
    obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg E H Dw l Xo c F hv T' (i.comp io) hWf w hint
    have hYX : ∀ b, (Y b).transpose = ((X b).map (algebraMap W KW)).transpose * (g b).map fW := fun b => by
      rw [← hXY b, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul _ (hg b)]
      simp
    have hYX' : ∀ b, ((Y b).map κ).transpose =
        ((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr) * (g b).map iA := fun b => by
      rw [← Matrix.transpose_map, hYX b, Matrix.map_mul]
      congr 1
      ext j k
      exact hκ _
    have hdet : ∀ b, ((Y b).map κ).det = algebraMap T'.V T'.Fr (X b).det * i (g b).det := fun b => by
      rw [← Matrix.det_transpose, hYX' b, Matrix.det_mul]
      congr 1
      · rw [← Matrix.det_transpose (X b)]; exact (RingHom.map_det _ _).symm
      · exact (RingHom.map_det i (g b)).symm
    have hYd : ∀ b, ((Y b).map κ).det ≠ 0 := fun b => by
      rw [hdet b]
      exact mul_ne_zero ((hX b).map (algebraMap T'.V T'.Fr)).ne_zero ((map_ne_zero i).2 (hg b).ne_zero)
    have hsn : (iA a : T'.Fr) ≠ 0 := (map_ne_zero iA).2 ha
    have hc' : GlobalTheory.Frames.FrChg (fun b => ((Y b).map κ).transpose) ((Units.mk0 (iA a) hsn : T'.Frˣ) : T'.Fr) yW w := by
      have c2 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c T'.Fr yW y'' w).2 _ _ _ _ hc hw
      simpa [hYX'] using c2
    have hbc := GlobalTheory.FrameRelBCZ.relation_baseChange_field_zpow E H Dw l Xo c z.K z.y e k F hF G hG T'.Fr (iA.comp φ) yW w (fun b => (Y b).map κ)
      (Units.mk0 (iA a) hsn) hYd (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ iA hyT hyW) hc'
    refine ⟨(∏ b, (X b).det ^ k b) * w₀, κ.injective ?_⟩
    have hP : MvPolynomial.map κ (MvPolynomial.map fW (MvPolynomial.C (a ^ e none) * MvPolynomial.map iK G)) =
        MvPolynomial.C ((iA a) ^ e none) * MvPolynomial.map (iA.comp φ).toRingHom G := by
      rw [map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_map,
        MvPolynomial.map_map, ← hφ, map_zpow₀, map_zpow₀]
      rfl
    have hu : ((Units.mk0 (iA a) hsn ^ e none : T'.Frˣ) : T'.Fr) = (iA a) ^ e none := by simp
    rw [GlobalTheory.LamT.LocClause.map_evalFr, hP, Formalism.L2.LamCM.evalFr_C_mul, ← hu, ← hbc, ← hw₀]
    simp only [hdet, map_mul, map_prod, map_pow, hκ, Finset.prod_mul_distrib, mul_pow]
    show _ = (∏ b, i (g b).det ^ k b) * _
    ring
  obtain ⟨w, hw⟩ := main
  exact ⟨w, by rw [← hw, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]; ring⟩

end GlobalTheory.FrameCoeffLocZ

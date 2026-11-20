import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AnisoMean
variable {D : D7}

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup H` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup H κ` as an intermediate fact. Set `e : G ≃ᵐ G` to `MeasurableEquiv.mulLeft z`. Establish `hmp : MeasurePreserving e κ κ` using `measurePreserving_mul_left κ z`. Establish `hfd : IsFundamentalDomain H (e '' 𝓝) κ`.

Use `h𝓝.image_of_equiv e.toEquiv (MeasurePreserving.symm e hmp).quasiMeasurePreserving (Equiv.refl _) fun γ x => ?_` and prove the remaining obligations. Use `show z * ((γ : G) * x) = (γ : G) * (z * x)`. Rewrite using `[← mul_assoc, hz γ, mul_assoc]`. Establish `h1 : ∫ n in e '' 𝓝, φ n ∂κ = ∫ n in 𝓝, φ n ∂κ` using `hfd.setIntegral_eq h𝓝 fun γ n => hinv γ n`. Establish `h2 : ∫ n in e '' 𝓝, φ n ∂κ = ∫ n in 𝓝, φ (z * n) ∂κ` using `hmp.setIntegral_image_emb e.measurableEmbedding φ 𝓝`.

Establish `h3 : ∫ n in 𝓝, φ n ∂κ = c * ∫ n in 𝓝, φ (z * n) ∂κ`. Rewrite using `[← MeasureTheory.integral_const_mul]`. Conclude with `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hφ)`. Rewrite `h3` using `[← h2, h1]`. Establish `h4 : (1 - c) * ∫ n in 𝓝, φ n ∂κ = 0` using `by rw [sub_mul, one_mul, ← h3, sub_self]`.

Break down `mul_eq_zero.1 h4 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h).symm hc`. Conclude with `h`.
-/
theorem setIntegral_eq_zero_of_central {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) [Countable H] (κ : Measure G) [κ.IsMulLeftInvariant] {𝓝 : Set G}
    (h𝓝 : IsFundamentalDomain H 𝓝 κ) (φ : G → ℂ) (hinv : ∀ (γ : H) (n : G), φ ((γ : G) * n) = φ n)
    (z : G) (hz : ∀ γ : H, z * γ = γ * z) (c : ℂ) (hc : c ≠ 1) (hφ : ∀ n, φ n = c * φ (z * n)) :
    ∫ n in 𝓝, φ n ∂κ = 0 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup H
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup H κ
  let e : G ≃ᵐ G := MeasurableEquiv.mulLeft z
  have hmp : MeasurePreserving e κ κ := measurePreserving_mul_left κ z
  have hfd : IsFundamentalDomain H (e '' 𝓝) κ := by
    refine h𝓝.image_of_equiv e.toEquiv (MeasurePreserving.symm e hmp).quasiMeasurePreserving (Equiv.refl _) fun γ x => ?_
    show z * ((γ : G) * x) = (γ : G) * (z * x)
    rw [← mul_assoc, hz γ, mul_assoc]
  have h1 : ∫ n in e '' 𝓝, φ n ∂κ = ∫ n in 𝓝, φ n ∂κ := hfd.setIntegral_eq h𝓝 fun γ n => hinv γ n
  have h2 : ∫ n in e '' 𝓝, φ n ∂κ = ∫ n in 𝓝, φ (z * n) ∂κ :=
    hmp.setIntegral_image_emb e.measurableEmbedding φ 𝓝
  have h3 : ∫ n in 𝓝, φ n ∂κ = c * ∫ n in 𝓝, φ (z * n) ∂κ := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hφ)
  rw [← h2, h1] at h3
  have h4 : (1 - c) * ∫ n in 𝓝, φ n ∂κ = 0 := by rw [sub_mul, one_mul, ← h3, sub_self]
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd (sub_eq_zero.1 h).symm hc
  · exact h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := rfl

/- English proof (translation)
Rewrite using `[← adj_eq]`. Conclude with `GlobalTheory.AutFunCounterexample.gram_herm V`.
-/
theorem gram_herm (V : HSp D) : V.gramᴴ = V.gram := by
  rw [← adj_eq]
  exact GlobalTheory.AutFunCounterexample.gram_herm V

/- English proof (translation)
Set `e : Fin n ≃ (Fin a ⊕ Fin b) ⊕ Fin a` to `Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_sum]; omega)`. Establish `hNM : Matrix.fromRows (Matrix.fromRows P1 P2) P3 * Matrix.fromCols (Matrix.fromCols C B) C' = 1`. Rewrite using `[Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul, Matrix.mul_fromCols, f1, f2, f3, f4, f5, f6, f7, f8, f9, Matrix.fromRows_zero, Matrix.fromCols_zero, Matrix.fromBlocks_one, Matrix.fromBlocks_one]`. Establish `hMN` using `(Matrix.mul_eq_one_comm_of_equiv e.symm).1 hNM`. Rewrite `hMN` using `[Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows]`.

Rewrite using `[← add_assoc]`. Conclude with `hMN`.
-/
private theorem mul_add_mul_add_mul_eq_one_of_dual_blocks {K : Type*} [Field K] {n a b : ℕ} (C C' : Matrix (Fin n) (Fin a) K)
    (B : Matrix (Fin n) (Fin b) K) (P1 P3 : Matrix (Fin a) (Fin n) K) (P2 : Matrix (Fin b) (Fin n) K)
    (f1 : P1 * C = 1) (f2 : P1 * B = 0) (f3 : P2 * C = 0) (f4 : P2 * B = 1) (f5 : P1 * C' = 0)
    (f6 : P2 * C' = 0) (f7 : P3 * C = 0) (f8 : P3 * B = 0) (f9 : P3 * C' = 1) (hn : n = b + 2 * a) :
    C * P1 + (B * P2 + C' * P3) = 1 := by
  let e : Fin n ≃ (Fin a ⊕ Fin b) ⊕ Fin a :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_sum]; omega)
  have hNM : Matrix.fromRows (Matrix.fromRows P1 P2) P3 * Matrix.fromCols (Matrix.fromCols C B) C' = 1 := by
    rw [Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul, Matrix.mul_fromCols,
      f1, f2, f3, f4, f5, f6, f7, f8, f9, Matrix.fromRows_zero, Matrix.fromCols_zero, Matrix.fromBlocks_one,
      Matrix.fromBlocks_one]
  have hMN := (Matrix.mul_eq_one_comm_of_equiv e.symm).1 hNM
  rw [Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows] at hMN
  rw [← add_assoc]
  exact hMN

/- English proof (translation)
Take `⟨hfr, hisom, horth, hrank⟩` from `hs`. Establish `hCC : adj D C * V.gram * C = 0` using `hfr.2.2`. Establish `hG` using `gram_herm V`. Establish `hV' : V'.gram⁻¹ * V'.gram = 1` using `Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.AutFunCounterexample.gram_det_ne V'))`. Simplify using `only [adj_eq] at h1 h2 h3 hCC hisom horth ⊢`.

Establish `ct : ∀ {a b : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E) (Y : Matrix (Fin V.rank) (Fin b) D.host.E), Yᴴ * V.gram * X = (Xᴴ * V.gram * Y)ᴴ`. Introduce `a b X Y`. Simplify using `[Matrix.conjTranspose_mul, hG, Matrix.mul_assoc]`. Establish `g1 : C'ᴴ * V.gram * C = 1` using `by rw [ct, h1, Matrix.conjTranspose_one]`. Establish `g3 : V'.gram⁻¹ * Bᴴ * V.gram * C = 0`.

Rewrite using `[show V'.gram⁻¹ * Bᴴ * V.gram * C = V'.gram⁻¹ * (Bᴴ * V.gram * C) by simp only [Matrix.mul_assoc], ct, horth, Matrix.conjTranspose_zero, Matrix.mul_zero]`. Establish `g4 : V'.gram⁻¹ * Bᴴ * V.gram * B = 1`. Rewrite using `[show V'.gram⁻¹ * Bᴴ * V.gram * B = V'.gram⁻¹ * (Bᴴ * V.gram * B) by simp only [Matrix.mul_assoc], hisom, hV']`. Establish `g6 : V'.gram⁻¹ * Bᴴ * V.gram * C' = 0`. Rewrite using `[show V'.gram⁻¹ * Bᴴ * V.gram * C' = V'.gram⁻¹ * (Bᴴ * V.gram * C') by simp only [Matrix.mul_assoc], ct, h3, Matrix.conjTranspose_zero, Matrix.mul_zero]`.

Conclude with `mul_add_mul_add_mul_eq_one_of_dual_blocks C C' B _ _ _ g1 h3 g3 g4 h2 g6 hCC horth h1 hrank`.
-/
theorem frame_identity {V V' : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (h1 : adj D C * V.gram * C' = 1) (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) :
    C * (adj D C' * V.gram) + (B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram)) = 1 := by
  obtain ⟨hfr, hisom, horth, hrank⟩ := hs
  have hCC : adj D C * V.gram * C = 0 := hfr.2.2
  have hG := gram_herm V
  have hV' : V'.gram⁻¹ * V'.gram = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.AutFunCounterexample.gram_det_ne V'))
  simp only [adj_eq] at h1 h2 h3 hCC hisom horth ⊢
  have ct : ∀ {a b : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E) (Y : Matrix (Fin V.rank) (Fin b) D.host.E),
      Yᴴ * V.gram * X = (Xᴴ * V.gram * Y)ᴴ := by
    intro a b X Y
    simp [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc]
  have g1 : C'ᴴ * V.gram * C = 1 := by rw [ct, h1, Matrix.conjTranspose_one]
  have g3 : V'.gram⁻¹ * Bᴴ * V.gram * C = 0 := by
    rw [show V'.gram⁻¹ * Bᴴ * V.gram * C = V'.gram⁻¹ * (Bᴴ * V.gram * C) by simp only [Matrix.mul_assoc], ct, horth,
      Matrix.conjTranspose_zero, Matrix.mul_zero]
  have g4 : V'.gram⁻¹ * Bᴴ * V.gram * B = 1 := by
    rw [show V'.gram⁻¹ * Bᴴ * V.gram * B = V'.gram⁻¹ * (Bᴴ * V.gram * B) by simp only [Matrix.mul_assoc], hisom, hV']
  have g6 : V'.gram⁻¹ * Bᴴ * V.gram * C' = 0 := by
    rw [show V'.gram⁻¹ * Bᴴ * V.gram * C' = V'.gram⁻¹ * (Bᴴ * V.gram * C') by simp only [Matrix.mul_assoc], ct, h3,
      Matrix.conjTranspose_zero, Matrix.mul_zero]
  exact mul_add_mul_add_mul_eq_one_of_dual_blocks C C' B _ _ _ g1 h3 g3 g4 h2 g6 hCC horth h1 hrank
end GlobalTheory.AnisoMean

namespace GlobalTheory.AnisoMean
variable {D : D7}
local infixl:70 " ⬝ " => HMul.hMul

/- English proof (translation)
Take `⟨co, -, hco, -⟩` from `GlobalTheory.DualPairCompare.exists_co D`. Use `⟨w.map fun z => z - GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D (co z), w.map fun z => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D (co z), ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `hco _`. Use extensionality with `i j`.

Conclude with `GlobalTheory.DualPairCompare.finPart_realPt D _`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem exists_fin_add_real {S T : HSp D} (w : WO S T) :
    ∃ u v : WO S T, u.map (infPart D) = 0 ∧ v.map (finPart D) = 0 ∧ w = u + v := by
  obtain ⟨co, -, hco, -⟩ := GlobalTheory.DualPairCompare.exists_co D
  refine ⟨w.map fun z => z - GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D (co z), w.map fun z => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D (co z), ?_, ?_, ?_⟩
  · ext i j
    exact hco _
  · ext i j
    exact GlobalTheory.DualPairCompare.finPart_realPt D _
  · ext i j
    simp

/- English proof (translation)
Take `⟨u, v, hu, hv, rfl⟩` from `exists_fin_add_real w`. Establish `hc` using `hψ.1`. Establish `h1 : IsThetaFunO ψ S T (heisO ψ S T v f)` using `GlobalTheory.WeilVacMove.isTheta_heisO_real hψ hv hf`. Establish `h2` using `GlobalTheory.FinTranslate.isThetaFunO_heisO hc.1 hc.2.1 h1 hu`. Rewrite `h2` using `[GlobalTheory.FinTranslate.heisO_heisO, (GlobalTheory.FinTranslate.symplOH_fin_real hu hv), AddChar.map_zero_eq_one, one_smul]`. Then use the resulting hypothesis.
-/
theorem isTheta_heisO {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) : IsThetaFunO ψ S T (heisO ψ S T w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  have hc := hψ.1
  have h1 : IsThetaFunO ψ S T (heisO ψ S T v f) := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ hv hf
  have h2 := GlobalTheory.FinTranslate.isThetaFunO_heisO hc.1 hc.2.1 h1 hu
  rwa [GlobalTheory.FinTranslate.heisO_heisO, (GlobalTheory.FinTranslate.symplOH_fin_real hu hv), AddChar.map_zero_eq_one, one_smul] at h2

/- English proof (translation)
Establish `h : Algebra.lmul R (TensorProduct F R E) ((1 : R) ⊗ₜ[F] e) = (Algebra.lmul F E e).baseChange R`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Rewrite using `[Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]`.
-/
theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (TensorProduct F R E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  have h : Algebra.lmul R (TensorProduct F R E) ((1 : R) ⊗ₜ[F] e) = (Algebra.lmul F E e).baseChange R := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Conclude with `Finset.sum_comm.trans ((Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm)`.
-/
theorem sum_eq_trace {m n : ℕ} (A : Matrix (Fin m) (Fin m) D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E)
    (x y : Matrix (Fin n) (Fin m) D.host.E) :
    ∑ a, ∑ b, ∑ c, ∑ d, A a b * star (y c b) * G c d * x d a = (A * yᴴ * G * x).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm.trans ((Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm)

/- English proof (translation)
Use `show Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = (1 : AF D.host.F) ⊗ₜ[D.host.F] star e`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.
-/
private theorem cA_incA_eq_incA_star (e : D.host.E) : cA D (incA D e) = incA D (star e) := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) =
    (1 : AF D.host.F) ⊗ₜ[D.host.F] star e
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/- English proof (translation)
Establish `key : hO S T (x.map (incA D)) (y.map (incA D)) = incA D ((S.gram⁻¹ * yᴴ * T.gram * x).trace)`. Rewrite using `[← sum_eq_trace]`. Simplify using `only [hO, Matrix.map_apply, cA_incA_eq_incA_star, ← map_mul, ← map_sum]`. Rewrite using `[symplOH, symplO, key, ← map_mul]`. Rewrite using `[show incA D (D.host.xi0 * (S.gram⁻¹ * yᴴ * T.gram * x).trace) = (1 : AF D.host.F) ⊗ₜ[D.host.F] (D.host.xi0 * (S.gram⁻¹ * yᴴ * T.gram * x).trace) from rfl, trace_one_tmul, ← map_mul]`.
-/
theorem symplOH_rat (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (x.map (incA D)) (y.map (incA D)) = algebraMap D.host.F (AF D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * (S.gram⁻¹ * yᴴ * T.gram * x).trace)) := by
  have key : hO S T (x.map (incA D)) (y.map (incA D)) = incA D ((S.gram⁻¹ * yᴴ * T.gram * x).trace) := by
    rw [← sum_eq_trace]
    simp only [hO, Matrix.map_apply, cA_incA_eq_incA_star, ← map_mul, ← map_sum]
  rw [symplOH, symplO, key, ← map_mul]
  rw [show incA D (D.host.xi0 * (S.gram⁻¹ * yᴴ * T.gram * x).trace) =
    (1 : AF D.host.F) ⊗ₜ[D.host.F] (D.host.xi0 * (S.gram⁻¹ * yᴴ * T.gram * x).trace) from rfl, trace_one_tmul, ← map_mul]

/- English proof (translation)
Rewrite using `[symplOH_rat]`. Conclude with `hψ.2.2.1 _`.
-/
theorem psi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplOH S T (x.map (incA D)) (y.map (incA D))) = 1 := by
  rw [symplOH_rat]
  exact hψ.2.2.1 _

/- English proof (translation)
Rewrite using `[GlobalTheory.FinTranslate.heisO_heisO, psi_rat hψ, one_smul, Matrix.map_add _ (map_add _)]`.
-/
theorem heisO_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (g : WO S T → ℂ) :
    heisO ψ S T (x.map (incA D)) (heisO ψ S T (y.map (incA D)) g) = heisO ψ S T ((x + y).map (incA D)) g := by
  rw [GlobalTheory.FinTranslate.heisO_heisO, psi_rat hψ, one_smul, Matrix.map_add _ (map_add _)]

/- English proof (translation)
Simplify using `only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]`.
-/
theorem mt_mul (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

/- English proof (translation)
Simplify using `only [Formalism.L2.Theta.mt, map_one, Units.val_one]`.
-/
theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

/- English proof (translation)
Unfold `actO`. Rewrite using `[mt_one, Matrix.one_mul, Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]`.
-/
theorem actO_mul_mt (S T : HSp D) (g : GA D S) (w : WO S T) :
    actO S T g 1 (HMul.hMul (w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g)) = w := by
  unfold actO
  rw [mt_one, Matrix.one_mul, Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

/- English proof (translation)
Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem g hg`. Take `⟨h1, h2, -⟩` from `hg`. Prove the components needed by the constructor for the conclusion. Establish `e : (Formalism.L2.Theta.mt V g - 1) ⬝ C.map (incA D) = 0` using `h1`.

Rewrite `e` using `[Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]`. Conclude with `e`. Establish `e : (adj D C * V.gram).map (incA D) ⬝ (Formalism.L2.Theta.mt V g - 1) = 0` using `h2`. Rewrite `e` using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Conclude with `e`.

Consider the case `one => simp only [mt_one, Matrix.one_mul, Matrix.mul_one, and_self]`. Consider the case `mul g h _ _ ihg ihh`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mt_mul, Matrix.mul_assoc, ihh.1, ihg.1]`. Rewrite using `[mt_mul, ← Matrix.mul_assoc, ihg.2, ihh.2]`.

Consider the case `inv g _ ih`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← ih.1]`. Rewrite using `[← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]`. Use `conv_lhs => rw [← ih.2]`.

Rewrite using `[Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]`.
-/
theorem ni_fix {V : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} {g : GA D V} (hg : g ∈ NI V C) :
    Formalism.L2.Theta.mt V g ⬝ C.map (incA D) = C.map (incA D) ∧
      (adj D C * V.gram).map (incA D) ⬝ Formalism.L2.Theta.mt V g = (adj D C * V.gram).map (incA D) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨h1, h2, -⟩ := hg
    constructor
    · have e : (Formalism.L2.Theta.mt V g - 1) ⬝ C.map (incA D) = 0 := h1
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at e
      exact e
    · have e : (adj D C * V.gram).map (incA D) ⬝ (Formalism.L2.Theta.mt V g - 1) = 0 := h2
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at e
      exact e
  | one => simp only [mt_one, Matrix.one_mul, Matrix.mul_one, and_self]
  | mul g h _ _ ihg ihh =>
    refine ⟨?_, ?_⟩
    · rw [mt_mul, Matrix.mul_assoc, ihh.1, ihg.1]
    · rw [mt_mul, ← Matrix.mul_assoc, ihg.2, ihh.2]
  | inv g _ ih =>
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← ih.1]
      rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
    · conv_lhs => rw [← ih.2]
      rw [Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

section Res
variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}

/- English proof (translation)
Simplify using `only [res, Pi.smul_apply, smul_eq_mul]`. Conclude with `MeasureTheory.integral_const_mul c _`.
-/
theorem res_smul (c : ℂ) (f : WO V W → ℂ) (x : WO V' W) :
    res V V' W C B μ 𝓨 (c • f) x = c * res V V' W C B μ 𝓨 f x := by
  simp only [res, Pi.smul_apply, smul_eq_mul]
  exact MeasureTheory.integral_const_mul c _

/- English proof (translation)
Establish `hth : IsThetaFunO ψ V W (heisO ψ V W (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V (n : GA D V))) g)` using `isTheta_heisO hω.std hg _`. Use `conv_lhs => rw [← actO_mul_mt V W (n : GA D V) w, ← hω.om_heis (n : GA D V) 1 _ g hg]`. Conclude with `GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ n _ hth`.
-/
theorem res_om_heis (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χS χT ω)
    (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨) (n : NI V C) {g : WO V W → ℂ} (hg : IsThetaFunO ψ V W g)
    (w : WO V W) :
    res V V' W C B μ 𝓨 (heisO ψ V W w (ω ((n : GA D V), 1) g)) =
      res V V' W C B μ 𝓨 (heisO ψ V W (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D))
        (Formalism.L2.Theta.mt V (n : GA D V))) g) := by
  have hth : IsThetaFunO ψ V W (heisO ψ V W (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D))
      (Formalism.L2.Theta.mt V (n : GA D V))) g) := isTheta_heisO hω.std hg _
  conv_lhs => rw [← actO_mul_mt V W (n : GA D V) w, ← hω.om_heis (n : GA D V) 1 _ g hg]
  exact GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ n _ hth

/- English proof (translation)
Establish `hadd : ∀ P Q : Matrix (Fin W.rank) (Fin V.rank) D.host.E, (P + Q).map (incA D) = P.map (incA D) + Q.map (incA D)` using `fun P Q => Matrix.map_add _ (map_add _) P Q`. Establish `hm : midPart V V' W B (a.map (incA D)) = (a * (V'.gram⁻¹ * adj D B * V.gram)).map (incA D)`. Simplify using `only [midPart, Matrix.map_mul]`. Establish `hi : isoPart V W C (b.map (incA D)) = (b * (adj D C * V.gram)).map (incA D)`. Simplify using `only [isoPart, Matrix.map_mul]`.

Establish `e : x.map (incA D) + (a * (V'.gram⁻¹ * adj D B * V.gram)).map (incA D) + (b * (adj D C * V.gram)).map (incA D) = (b * (adj D C * V.gram) + (a * (V'.gram⁻¹ * adj D B * V.gram) + x)).map (incA D)`. Rewrite using `[hadd, hadd]`. Normalize the expressions using the abelian group laws. Rewrite using `[hm, hi, e, ← heisO_rat hψ.1, ← heisO_rat hψ.1, ← hi, ← hm]`. Establish `h0` using `isTheta_heisO hψ hg (x.map (incA D))`.

Establish `h1` using `isTheta_heisO hψ h0 (midPart V V' W B (a.map (incA D)))`. Take `⟨-, -, -, hIso⟩` from `(GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ).1 _ h1`. Take `⟨-, hR, hMid, -⟩` from `(GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ).1 _ h0`. Rewrite using `[hIso, hMid]`. Establish `hq` using `hR.quasi a 0`.

Rewrite `hq` using `[add_zero, GlobalTheory.FinTranslate.symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul]`. Simplify using `only [heisO, GlobalTheory.FinTranslate.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]`. Conclude with `hq`.
-/
theorem mean_rat_shift (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨) {g : WO V W → ℂ} (hg : IsThetaFunO ψ V W g)
    (x : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (a : Matrix (Fin W.rank) (Fin V'.rank) D.host.E)
    (b : Matrix (Fin W.rank) (Fin r) D.host.E) :
    res V V' W C B μ 𝓨 (heisO ψ V W (x.map (incA D) + midPart V V' W B (a.map (incA D)) +
      isoPart V W C (b.map (incA D))) g) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (x.map (incA D)) g) 0 := by
  have hadd : ∀ P Q : Matrix (Fin W.rank) (Fin V.rank) D.host.E,
      (P + Q).map (incA D) = P.map (incA D) + Q.map (incA D) := fun P Q => Matrix.map_add _ (map_add _) P Q
  have hm : midPart V V' W B (a.map (incA D)) = (a * (V'.gram⁻¹ * adj D B * V.gram)).map (incA D) := by
    simp only [midPart, Matrix.map_mul]
  have hi : isoPart V W C (b.map (incA D)) = (b * (adj D C * V.gram)).map (incA D) := by
    simp only [isoPart, Matrix.map_mul]
  have e : x.map (incA D) + (a * (V'.gram⁻¹ * adj D B * V.gram)).map (incA D) +
      (b * (adj D C * V.gram)).map (incA D) =
      (b * (adj D C * V.gram) + (a * (V'.gram⁻¹ * adj D B * V.gram) + x)).map (incA D) := by
    rw [hadd, hadd]
    abel
  rw [hm, hi, e, ← heisO_rat hψ.1, ← heisO_rat hψ.1, ← hi, ← hm]
  have h0 := isTheta_heisO hψ hg (x.map (incA D))
  have h1 := isTheta_heisO hψ h0 (midPart V V' W B (a.map (incA D)))
  obtain ⟨-, -, -, hIso⟩ := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ).1 _ h1
  obtain ⟨-, hR, hMid, -⟩ := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ).1 _ h0
  rw [hIso, hMid]
  have hq := hR.quasi a 0
  rw [add_zero, GlobalTheory.FinTranslate.symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul] at hq
  simp only [heisO, GlobalTheory.FinTranslate.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
  exact hq

/- English proof (translation)
Establish `hth` using `isTheta_heisO hψ hg w`. Take `⟨-, -, -, hIso⟩` from `(GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ).1 _ hth`. Rewrite using `[← hIso b, GlobalTheory.FinTranslate.heisO_heisO, res_smul]`.
-/
theorem mean_iso_shift (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨) {g : WO V W → ℂ} (hg : IsThetaFunO ψ V W g)
    (w : WO V W) (b : Mx D W.rank r) (x : WO V' W) :
    res V V' W C B μ 𝓨 (heisO ψ V W w g) x = ψ (symplOH V W (isoPart V W C b) w) *
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C b + w) g) x := by
  have hth := isTheta_heisO hψ hg w
  obtain ⟨-, -, -, hIso⟩ := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ).1 _ hth
  rw [← hIso b, GlobalTheory.FinTranslate.heisO_heisO, res_smul]
end Res
end GlobalTheory.AnisoMean

namespace GlobalTheory.AnisoMean
variable {D : D7}
local infixl:70 " ⬝ " => HMul.hMul

local notation "𝕚⟨" M "⟩" => (Matrix.map M (incA D) : Matrix _ _ (AE D))

/- English proof (translation)
Establish `h0 : (g - 1) * C = 0` using `by rw [Matrix.sub_mul, hfix, Matrix.one_mul, sub_self]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hid, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Use `_ = T + T * (g - 1) * B * R + T * (g - 1) * C' * P := by`.

Rewrite using `[Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc (T * (g - 1)) C P', Matrix.mul_assoc T (g - 1) C, h0, Matrix.mul_zero, Matrix.zero_mul, zero_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, add_assoc]`.
-/
theorem decomp_generic {A : Type*} [CommRing A] {w N n' r : ℕ} (T : Matrix (Fin w) (Fin N) A)
    (g : Matrix (Fin N) (Fin N) A) (C C' : Matrix (Fin N) (Fin r) A) (B : Matrix (Fin N) (Fin n') A)
    (P' P : Matrix (Fin r) (Fin N) A) (R : Matrix (Fin n') (Fin N) A)
    (hid : C * P' + (B * R + C' * P) = 1) (hfix : g * C = C) :
    T * g = T + T * (g - 1) * B * R + T * (g - 1) * C' * P := by
  have h0 : (g - 1) * C = 0 := by rw [Matrix.sub_mul, hfix, Matrix.one_mul, sub_self]
  calc T * g = T + T * (g - 1) * (C * P' + (B * R + C' * P)) := by
        rw [hid, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
        abel
    _ = T + T * (g - 1) * B * R + T * (g - 1) * C' * P := by
        rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc (T * (g - 1)) C P', Matrix.mul_assoc T (g - 1) C, h0,
          Matrix.mul_zero, Matrix.zero_mul, zero_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, add_assoc]

/- English proof (translation)
Establish `hid : 𝕚⟨C⟩ * 𝕚⟨P'⟩ + (𝕚⟨B⟩ * 𝕚⟨R⟩ + 𝕚⟨C'⟩ * 𝕚⟨P⟩) = (1 : Matrix (Fin N) (Fin N) (AE D))`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _), ← Matrix.map_add _ (map_add _), hE, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[decomp_generic _ g _ _ _ _ _ _ hid hfix, hu]`. Establish `hs : 𝕚⟨u⟩ - 1 = 𝕚⟨u - 1⟩`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]`.

Rewrite using `[hs]`. Simplify using `only [← Matrix.map_mul]`.
-/
theorem rationalMatrix_decomposition_isotropicFrame {N n' r w : ℕ} (C C' : Matrix (Fin N) (Fin r) D.host.E)
    (B : Matrix (Fin N) (Fin n') D.host.E) (P' P : Matrix (Fin r) (Fin N) D.host.E)
    (R : Matrix (Fin n') (Fin N) D.host.E) (hE : C * P' + (B * R + C' * P) = 1)
    (y : Matrix (Fin w) (Fin r) D.host.E) (g : Matrix (Fin N) (Fin N) (AE D))
    (hfix : g ⬝ 𝕚⟨C⟩ = 𝕚⟨C⟩) (u : Matrix (Fin N) (Fin N) D.host.E) (hu : g = 𝕚⟨u⟩) :
    𝕚⟨y * P'⟩ ⬝ g = 𝕚⟨y * P'⟩ + 𝕚⟨y * P' * (u - 1) * B⟩ ⬝ 𝕚⟨R⟩ + 𝕚⟨y * P' * (u - 1) * C'⟩ ⬝ 𝕚⟨P⟩ := by
  have hid : 𝕚⟨C⟩ * 𝕚⟨P'⟩ + (𝕚⟨B⟩ * 𝕚⟨R⟩ + 𝕚⟨C'⟩ * 𝕚⟨P⟩) = (1 : Matrix (Fin N) (Fin N) (AE D)) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _),
      ← Matrix.map_add _ (map_add _), hE, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [decomp_generic _ g _ _ _ _ _ _ hid hfix, hu]
  have hs : 𝕚⟨u⟩ - 1 = 𝕚⟨u - 1⟩ := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hs]
  simp only [← Matrix.map_mul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, _, rationalMatrix_decomposition_isotropicFrame C C' B _ _ _ (frame_identity hs h1 h2 h3) y _ hfix u hu⟩`.
-/
theorem rat_decomp {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (h1 : adj D C * V.gram * C' = 1) (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (γ : GA D V)
    (hfix : Formalism.L2.Theta.mt V γ ⬝ C.map (incA D) = C.map (incA D))
    (u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hu : Formalism.L2.Theta.mt V γ = u.map (incA D)) :
    ∃ (a : Matrix (Fin W.rank) (Fin V'.rank) D.host.E) (b : Matrix (Fin W.rank) (Fin r) D.host.E),
      (y * (adj D C' * V.gram)).map (incA D) ⬝ Formalism.L2.Theta.mt V γ =
        (y * (adj D C' * V.gram)).map (incA D) + midPart V V' W B (a.map (incA D)) +
          isoPart V W C (b.map (incA D)) := ⟨_, _, rationalMatrix_decomposition_isotropicFrame C C' B _ _ _ (frame_identity hs h1 h2 h3) y _ hfix u hu⟩

/- English proof (translation)
Rewrite using `[add_mul, one_mul, mul_sub, mul_one, h, sub_zero, sub_add_cancel]`.
-/
theorem one_add_mul_one_sub {R : Type*} [Ring R] {m : R} (h : m * m = 0) : (1 + m) * (1 - m) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, h, sub_zero, sub_add_cancel]

/- English proof (translation)
Rewrite using `[sub_mul, one_mul, mul_add, mul_one, h, add_zero, add_sub_cancel_right]`.
-/
theorem one_sub_mul_one_add {R : Type*} [Ring R] {m : R} (h : m * m = 0) : (1 - m) * (1 + m) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, h, add_zero, add_sub_cancel_right]

/- English proof (translation)
Establish `e : (1 + Y) * J * (1 + m) = J + (Y * J + J * m) + Y * J * m` using `by noncomm_ring`. Rewrite using `[e, e1, e2, add_zero, add_zero]`.
-/
theorem unit_form {R : Type*} [Ring R] {Y J m : R} (e1 : Y * J + J * m = 0) (e2 : Y * J * m = 0) :
    (1 + Y) * J * (1 + m) = J := by
  have e : (1 + Y) * J * (1 + m) = J + (Y * J + J * m) + Y * J * m := by noncomm_ring
  rw [e, e1, e2, add_zero, add_zero]

/- English proof (translation)
Break down `eq_or_ne i j with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm, map_zero]`.
-/
theorem cA_one (N : ℕ) (i j : Fin N) :
    cA D ((1 : Matrix (Fin N) (Fin N) (AE D)) i j) = (1 : Matrix (Fin N) (Fin N) (AE D)) j i := by
  rcases eq_or_ne i j with rfl | h
  · simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm, map_zero]

/- English proof (translation)
Use `show Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = (1 : AF D.host.F) ⊗ₜ[D.host.F] star e`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.
-/
private theorem cA_incA_apply_eq_incA_star (e : D.host.E) : cA D (incA D e) = incA D (star e) := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) =
    (1 : AF D.host.F) ⊗ₜ[D.host.F] star e
  rw [Algebra.TensorProduct.map_tmul]
  rfl

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Set `Y : Matrix (Fin V.rank) (Fin V.rank) (AE D)` to `a • X.map (incA D)`. Establish `hYY : Y * Y = 0`. Simplify using `only [Y, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, hXX, Matrix.map_zero _ (map_zero _), smul_zero]`. Set `u : GL (Fin V.rank) (AE D)` to `⟨1 + Y, 1 - Y, one_add_mul_one_sub hYY, one_sub_mul_one_add hYY⟩`. Establish `hσa : ∀ (b : AF D.host.F) (w : AE D), cA D (b • w) = b • cA D w`.

Introduce `b w`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.smul_def]`. Use `congr 1`. Use `show Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig (b ⊗ₜ[D.host.F] (1 : D.host.E)) = b ⊗ₜ[D.host.F] (1 : D.host.E)`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`.

Both sides reduce to the same expression. Establish `hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (1 + Y) = 1 + a • (Xᴴ).map (incA D)`. Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Y, Matrix.conjTranspose_apply]`. Rewrite using `[map_add]`.

Use `congr 1`. Conclude with `cA_one (D := D) V.rank j i`. Establish `h3 : Xᴴ * V.gram * X = 0`. Establish `h` using `congrArg (· * X) hsk`. Simplify using `only [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, hXX, Matrix.mul_zero, add_zero] at h`.

Rewrite using `[Matrix.mul_assoc]`. Conclude with `h`. Establish `hmem : u ∈ HR (AF D.host.F) D.sp.cm.sig V.gram` using `by show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (1 + Y) * JR (AF D.host.F) V.gram * (1 + Y) = JR (AF D.host.F) V.gram`. Rewrite using `[hc]`. Apply `unit_form` to reduce the goal to its premises.

Use `show a • (Xᴴ).map (incA D) * V.gram.map (incA D) + V.gram.map (incA D) * (a • X.map (incA D)) = 0`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _), hsk, Matrix.map_zero _ (map_zero _), smul_zero]`. Use `show a • (Xᴴ).map (incA D) * V.gram.map (incA D) * (a • X.map (incA D)) = 0`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, h3, Matrix.map_zero _ (map_zero _), smul_zero]`. Conclude with `⟨⟨u, hmem⟩, rfl⟩`.
-/
theorem exists_central (V : HSp D) (X : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hXX : X * X = 0)
    (hsk : Xᴴ * V.gram + V.gram * X = 0) (a : AF D.host.F) :
    ∃ z : GA D V, Formalism.L2.Theta.mt V z = 1 + a • X.map (incA D) := by
  let Y : Matrix (Fin V.rank) (Fin V.rank) (AE D) := a • X.map (incA D)
  have hYY : Y * Y = 0 := by
    simp only [Y, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, hXX, Matrix.map_zero _ (map_zero _), smul_zero]
  let u : GL (Fin V.rank) (AE D) := ⟨1 + Y, 1 - Y, one_add_mul_one_sub hYY, one_sub_mul_one_add hYY⟩
  have hσa : ∀ (b : AF D.host.F) (w : AE D), cA D (b • w) = b • cA D w := by
    intro b w
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr 1
    show Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig (b ⊗ₜ[D.host.F] (1 : D.host.E)) =
      b ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (1 + Y) = 1 + a • (Xᴴ).map (incA D) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Y,
      Matrix.conjTranspose_apply]
    rw [map_add]
    congr 1
    exact cA_one (D := D) V.rank j i
  have h3 : Xᴴ * V.gram * X = 0 := by
    have h := congrArg (· * X) hsk
    simp only [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, hXX, Matrix.mul_zero, add_zero] at h
    rw [Matrix.mul_assoc]
    exact h
  have hmem : u ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (1 + Y) * JR (AF D.host.F) V.gram * (1 + Y) =
      JR (AF D.host.F) V.gram
    rw [hc]
    apply unit_form
    · show a • (Xᴴ).map (incA D) * V.gram.map (incA D) + V.gram.map (incA D) * (a • X.map (incA D)) = 0
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ← Matrix.map_mul, ← Matrix.map_mul,
        ← Matrix.map_add _ (map_add _), hsk, Matrix.map_zero _ (map_zero _), smul_zero]
    · show a • (Xᴴ).map (incA D) * V.gram.map (incA D) * (a • X.map (incA D)) = 0
      simp only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, h3, Matrix.map_zero _ (map_zero _), smul_zero]
  exact ⟨⟨u, hmem⟩, rfl⟩

/- English proof (translation)
Simplify using `[Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]`.
-/
theorem trace_mul_single {r : ℕ} (M : Matrix (Fin r) (Fin r) D.host.E) (i j : Fin r) (c : D.host.E) :
    (M * Matrix.single j i c).trace = M i j * c := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_star, neg_sub]`.
-/
private theorem conjTranspose_single_sub_single_star {r : ℕ} (i j : Fin r) (a : D.host.E) :
    (Matrix.single j i a - Matrix.single i j (star a))ᴴ = -(Matrix.single j i a - Matrix.single i j (star a)) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_star, neg_sub]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `h0 (Matrix.ext h)`. Establish `hx : star D.host.xi0 = -D.host.xi0` using `GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D`.

Use `set t := (D.host.xi0 * M i j)⁻¹ with ht`. Use `⟨Matrix.single j i t - Matrix.single i j (star t), ?_, ?_⟩` and prove the remaining obligations. Conclude with `conjTranspose_single_sub_single_star i j t`. Establish `hMji : M j i = star (M i j)`. Use `congrFun (congrFun hM j) i` as an intermediate fact.

Rewrite `this` using `[Matrix.conjTranspose_apply]`. Conclude with `this.symm`. Rewrite using `[Matrix.mul_sub, Matrix.trace_sub, trace_mul_single, trace_mul_single, hMji]`. Establish `h1 : D.host.xi0 * (M i j * t) = 1`. Rewrite using `[ht, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) hij)]`.

Establish `h2 : D.host.xi0 * (star (M i j) * star t) = -1`. Use `congrArg star h1` as an intermediate fact. Rewrite `this` using `[star_mul, star_mul, hx, star_one]`. Take the linear combination `-this`. Rewrite using `[mul_sub, h1, h2, sub_neg_eq_add, show (1 : D.host.E) + 1 = algebraMap D.host.F D.host.E 2 by`.

Rewrite using `[map_ofNat]`. Use the proof step `norm_num, Algebra.trace_algebraMap, D.sp.cm.deg2]`. Evaluate the numerical expressions.
-/
theorem exists_skew {r : ℕ} (M : Matrix (Fin r) (Fin r) D.host.E) (hM : Mᴴ = M) (h0 : M ≠ 0) :
    ∃ S₀ : Matrix (Fin r) (Fin r) D.host.E, S₀ᴴ = -S₀ ∧
      Algebra.trace D.host.F D.host.E (D.host.xi0 * (M * S₀).trace) ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Matrix.ext h)
  have hx : star D.host.xi0 = -D.host.xi0 := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  set t := (D.host.xi0 * M i j)⁻¹ with ht
  refine ⟨Matrix.single j i t - Matrix.single i j (star t), ?_, ?_⟩
  · exact conjTranspose_single_sub_single_star i j t
  · have hMji : M j i = star (M i j) := by
      have := congrFun (congrFun hM j) i
      rw [Matrix.conjTranspose_apply] at this
      exact this.symm
    rw [Matrix.mul_sub, Matrix.trace_sub, trace_mul_single, trace_mul_single, hMji]
    have h1 : D.host.xi0 * (M i j * t) = 1 := by
      rw [ht, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) hij)]
    have h2 : D.host.xi0 * (star (M i j) * star t) = -1 := by
      have := congrArg star h1
      rw [star_mul, star_mul, hx, star_one] at this
      linear_combination -this
    rw [mul_sub, h1, h2, sub_neg_eq_add, show (1 : D.host.E) + 1 = algebraMap D.host.F D.host.E 2 by
      rw [map_ofNat]; norm_num, Algebra.trace_algebraMap, D.sp.cm.deg2]
    norm_num

/- English proof (translation)
Establish `hG : V.gram⁻¹ * V.gram = 1` using `Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.AutFunCounterexample.gram_det_ne V))`. Simplify using `only [adj_eq] at h1 ⊢`. Establish `h1' : Cᴴ * (V.gram * C') = 1` using `by rw [← Matrix.mul_assoc]; exact h1`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_herm, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc V.gram⁻¹ V.gram, hG, Matrix.one_mul, Matrix.trace_mul_comm C']`.

Simplify using `only [Matrix.mul_assoc, h1', Matrix.mul_one]`.
-/
theorem pairing_trace {V W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    (h1 : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E)
    (S₀ : Matrix (Fin r) (Fin r) D.host.E) :
    (V.gram⁻¹ * (y * (adj D C' * V.gram))ᴴ * W.gram * (y * S₀ * (adj D C * V.gram))).trace =
      ((adj D y * W.gram * y) * S₀).trace := by
  have hG : V.gram⁻¹ * V.gram = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.AutFunCounterexample.gram_det_ne V))
  simp only [adj_eq] at h1 ⊢
  have h1' : Cᴴ * (V.gram * C') = 1 := by rw [← Matrix.mul_assoc]; exact h1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_herm, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V.gram⁻¹ V.gram, hG, Matrix.one_mul, Matrix.trace_mul_comm C']
  simp only [Matrix.mul_assoc, h1', Matrix.mul_one]

/- English proof (translation)
Take `⟨h1, h2⟩` from `ni_fix hg`. Establish `hX : (C * S₀ * (adj D C * V.gram)).map (incA D) = C.map (incA D) * S₀.map (incA D) * (adj D C * V.gram).map (incA D)`. Simplify using `only [Matrix.map_mul]`. Rewrite using `[hX, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]`. Use `congr 2`.

Rewrite using `[Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]`.
-/
theorem central_comm {V : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (S₀ : Matrix (Fin r) (Fin r) D.host.E)
    (a : AF D.host.F) {g : GA D V} (hg : g ∈ NI V C) :
    (1 + a • (C * S₀ * (adj D C * V.gram)).map (incA D)) ⬝ Formalism.L2.Theta.mt V g =
      Formalism.L2.Theta.mt V g ⬝ (1 + a • (C * S₀ * (adj D C * V.gram)).map (incA D)) := by
  obtain ⟨h1, h2⟩ := ni_fix hg
  have hX : (C * S₀ * (adj D C * V.gram)).map (incA D) =
      C.map (incA D) * S₀.map (incA D) * (adj D C * V.gram).map (incA D) := by
    simp only [Matrix.map_mul]
  rw [hX, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  congr 2
  rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]
end GlobalTheory.AnisoMean

namespace GlobalTheory.AnisoMean
variable {D : D7}
local infixl:70 " ⬝ " => HMul.hMul

/- English proof (translation)
Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc P C, h, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]`.
-/
theorem sq_zero_generic {R : Type*} [Ring R] {N r : ℕ} (C : Matrix (Fin N) (Fin r) R) (S₀ : Matrix (Fin r) (Fin r) R)
    (P : Matrix (Fin r) (Fin N) R) (h : P * C = 0) : (C * S₀ * P) * (C * S₀ * P) = 0 := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P C, h, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]

/- English proof (translation)
Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, hS, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`. Conclude with `neg_add_cancel _`.
-/
theorem skew_generic {N r : ℕ} (G : Matrix (Fin N) (Fin N) D.host.E) (hG : Gᴴ = G)
    (C : Matrix (Fin N) (Fin r) D.host.E) (S₀ : Matrix (Fin r) (Fin r) D.host.E) (hS : S₀ᴴ = -S₀) :
    (C * S₀ * (Cᴴ * G))ᴴ * G + G * (C * S₀ * (Cᴴ * G)) = 0 := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, hS, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc]
  exact neg_add_cancel _

/- English proof (translation)
Rewrite `h1`, the goal using `[adj_eq]`. Establish `h` using `congrArg Matrix.conjTranspose h1`. Simplify `h` using `[Matrix.conjTranspose_mul, gram_herm, Matrix.mul_assoc]`.
-/
theorem dual_one {V : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    (h1 : adj D C * V.gram * C' = 1) : adj D C' * V.gram * C = 1 := by
  rw [adj_eq] at h1 ⊢
  have h := congrArg Matrix.conjTranspose h1
  simpa [Matrix.conjTranspose_mul, gram_herm, Matrix.mul_assoc] using h

/- English proof (translation)
Establish `hm : (matHom V z).1 - 1 = a • (C * S₀ * (adj D C * V.gram)).map (incA D)`. Rewrite using `[show ((matHom V z).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = Formalism.L2.Theta.mt V z from rfl, hz, add_sub_cancel_left]`. Establish `hCC : adj D C * V.gram * C = 0` using `hC.2.2`. Unfold `NI`. Apply `Subgroup.subset_closure` to reduce the goal to its premises.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ((matHom V z).1 - 1) ⬝ C.map (incA D) = 0`. Rewrite using `[hm, Matrix.smul_mul, ← Matrix.map_mul, Matrix.mul_assoc, hCC, Matrix.mul_zero, Matrix.map_zero _ (map_zero _), smul_zero]`. Use `show (adj D C * V.gram).map (incA D) ⬝ ((matHom V z).1 - 1) = 0`. Rewrite using `[hm, Matrix.mul_smul, ← Matrix.map_mul, show adj D C * V.gram * (C * S₀ * (adj D C * V.gram)) = adj D C * V.gram * C * S₀ * (adj D C * V.gram) by simp only [Matrix.mul_assoc], hCC, Matrix.zero_mul, Matrix.zero_mul, Matrix.map_zero _ (map_zero _), smul_zero]`.

Introduce `x hx`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `h0 : (C * S₀ * (adj D C * V.gram)).mulVec x = 0`. Rewrite using `[← Matrix.mulVec_mulVec]`. Rewrite using `[show (adj D C * V.gram).mulVec x = 0 from hx, Matrix.mulVec_zero]`.

Establish `key : ((C * S₀ * (adj D C * V.gram)).map (incA D)).mulVec (fun i => incA D (x i)) = 0`. Use extensionality with `i`. Use `congrFun h0 i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this ⊢`. Rewrite using `[← map_zero (incA D), ← this, map_sum]`.

Simplify using `only [map_mul]`. Use `show ((matHom V z).1 - 1).mulVec _ = _`. Rewrite using `[hm, Matrix.smul_mulVec, key, smul_zero, Matrix.mulVec_zero]`.
-/
theorem central_mem_NI {V : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C)
    (S₀ : Matrix (Fin r) (Fin r) D.host.E) (a : AF D.host.F) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = 1 + a • (C * S₀ * (adj D C * V.gram)).map (incA D)) : z ∈ NI V C := by
  have hm : (matHom V z).1 - 1 = a • (C * S₀ * (adj D C * V.gram)).map (incA D) := by
    rw [show ((matHom V z).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = Formalism.L2.Theta.mt V z from rfl, hz,
      add_sub_cancel_left]
  have hCC : adj D C * V.gram * C = 0 := hC.2.2
  unfold NI
  apply Subgroup.subset_closure
  refine ⟨?_, ?_, ?_⟩
  · show ((matHom V z).1 - 1) ⬝ C.map (incA D) = 0
    rw [hm, Matrix.smul_mul, ← Matrix.map_mul, Matrix.mul_assoc, hCC, Matrix.mul_zero,
      Matrix.map_zero _ (map_zero _), smul_zero]
  · show (adj D C * V.gram).map (incA D) ⬝ ((matHom V z).1 - 1) = 0
    rw [hm, Matrix.mul_smul, ← Matrix.map_mul, show adj D C * V.gram * (C * S₀ * (adj D C * V.gram)) =
      adj D C * V.gram * C * S₀ * (adj D C * V.gram) by simp only [Matrix.mul_assoc], hCC, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.map_zero _ (map_zero _), smul_zero]
  · intro x hx
    refine ⟨0, ?_⟩
    have h0 : (C * S₀ * (adj D C * V.gram)).mulVec x = 0 := by
      rw [← Matrix.mulVec_mulVec]
      rw [show (adj D C * V.gram).mulVec x = 0 from hx, Matrix.mulVec_zero]
    have key : ((C * S₀ * (adj D C * V.gram)).map (incA D)).mulVec (fun i => incA D (x i)) = 0 := by
      ext i
      have := congrFun h0 i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this ⊢
      rw [← map_zero (incA D), ← this, map_sum]
      simp only [map_mul]
    show ((matHom V z).1 - 1).mulVec _ = _
    rw [hm, Matrix.smul_mulVec, key, smul_zero, Matrix.mulVec_zero]

/- English proof (translation)
Establish `hd` using `dual_one h1`. Rewrite using `[hz, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, add_comm]`. Use `congr 1`. Simplify using `only [isoPart, Matrix.smul_mul, ← Matrix.map_mul]`. Use `congr 2`.

Rewrite using `[Matrix.mul_assoc y, ← Matrix.mul_assoc (adj D C' * V.gram), ← Matrix.mul_assoc (adj D C' * V.gram), hd, Matrix.one_mul, Matrix.mul_assoc]`.
-/
theorem iso_mt_central {V W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    (h1 : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E)
    (S₀ : Matrix (Fin r) (Fin r) D.host.E) (a : AF D.host.F) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = 1 + a • (C * S₀ * (adj D C * V.gram)).map (incA D)) :
    (y * (adj D C' * V.gram)).map (incA D) ⬝ Formalism.L2.Theta.mt V z =
      isoPart V W C (a • (y * S₀).map (incA D)) + (y * (adj D C' * V.gram)).map (incA D) := by
  have hd := dual_one h1
  rw [hz, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, add_comm]
  congr 1
  simp only [isoPart, Matrix.smul_mul, ← Matrix.map_mul]
  congr 2
  rw [Matrix.mul_assoc y, ← Matrix.mul_assoc (adj D C' * V.gram), ← Matrix.mul_assoc (adj D C' * V.gram), hd,
    Matrix.one_mul, Matrix.mul_assoc]

end GlobalTheory.AnisoMean

open GlobalTheory.AnisoMean in
/- English proof (translation)
Introduce `D V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hμ κ 𝓝 hκ h𝓝 y hy f hf`. Establish `hψ : IsStdChar D ψ (-1)` using `hω.std`. Establish `: IsTopologicalGroup (GA D V)` using `GlobalTheory.AutFunCounterexample.topGroup_GA D V`. Establish `: BorelSpace (NI V C)` using `GlobalTheory.AutFunCounterexample.borel_NI D V C`. Establish `: Countable (GQ V)` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram`.

Establish `: Countable (NIQ V C)` using `Function.Injective.countable (f := fun γ : NIQ V C => (⟨((γ : NI V C) : GA D V), Subgroup.mem_subgroupOf.1 γ.2⟩ : GQ V)) fun a b h => by`. Simplify using `only [Subtype.mk.injEq] at h`. Conclude with `Subtype.ext (Subtype.ext h)`. Establish `hCC : adj D C * V.gram * C = 0` using `hs.frame.2.2`. Establish `hrat : ∀ g : GA D V, g ∈ GQ V → ∃ u : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V g = u.map (incA D)`.

Introduce `g hg`. Establish `hg' : (matHom V g : GL (Fin V.rank) (AE D)) ∈ HFin (AF D.host.F) D.sp.cm.sig V.gram` using `Subgroup.mem_subgroupOf.1 hg`. Take `⟨x, -, hx⟩` from `Subgroup.mem_map.1 hg'`. Use `⟨x.1, ?_⟩` and prove the remaining obligations. Use `show ((matHom V g : GL (Fin V.rank) (AE D)) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = _`.

Rewrite using `[← hx]`. Both sides reduce to the same expression. Establish `hM : (adj D y * W.gram * y)ᴴ = adj D y * W.gram * y`. Rewrite using `[adj_eq]`. Simplify using `[Matrix.conjTranspose_mul, gram_herm, Matrix.mul_assoc]`.

Take `⟨S₀, hS₀, htr⟩` from `exists_skew _ hM hy`. Establish `ht : (1 / 2 : D.host.F) * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((adj D y * W.gram * y) * S₀).trace) ≠ 0` using `mul_ne_zero (by norm_num) htr`. Take `⟨b, hb⟩` from `hψ.1.2.2.2`. Set `a : AF D.host.F` to `b * algebraMap D.host.F (AF D.host.F) ((1 / 2 : D.host.F) * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((adj D y * W.gram * y) * S₀).trace))⁻¹`. Establish `ha : a * algebraMap D.host.F (AF D.host.F) ((1 / 2 : D.host.F) * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((adj D y * W.gram * y) * S₀).trace)) = b`.

Simplify using `only [a]`. Rewrite using `[mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, mul_one]`. Establish `hXX : (C * S₀ * (adj D C * V.gram)) * (C * S₀ * (adj D C * V.gram)) = 0` using `sq_zero_generic C S₀ (adj D C * V.gram) hCC`. Establish `hsk : (C * S₀ * (adj D C * V.gram))ᴴ * V.gram + V.gram * (C * S₀ * (adj D C * V.gram)) = 0`. Rewrite using `[adj_eq]`.

Conclude with `skew_generic V.gram (gram_herm V) C S₀ hS₀`. Take `⟨z, hz⟩` from `exists_central V _ hXX hsk a`. Establish `hzN : z ∈ NI V C` using `central_mem_NI hs.frame S₀ a hz`. Establish `hω_mul : ∀ g h : GA D V, ω (g * h, 1) = ω (g, 1) * ω (h, 1)` using `fun g h => by`. Rewrite using `[← map_mul, Prod.mk_mul_mk, one_mul]`.

Establish `hw0 : isoPart V W C' (y.map (incA D)) = (y * (adj D C' * V.gram)).map (incA D)`. Simplify using `only [isoPart, Matrix.map_mul]`. Rewrite using `[hw0]`. Use `setIntegral_eq_zero_of_central (NIQ V C) κ h𝓝 (fun n : NI V C => res V V' W C B μ 𝓨 (heisO ψ V W ((y * (adj D C' * V.gram)).map (incA D)) (ω ((n : GA D V), 1) f)) 0) ?_ ⟨z, hzN⟩ ?_ (ψ (symplOH V W (isoPart V W C (a • (y * S₀).map (incA D))) ((y * (adj D C' * V.gram)).map (incA D) …` and prove the remaining obligations. Introduce `γ n`.

Establish `hF : IsThetaFunO ψ V W (ω ((n : GA D V), 1) f)` using `hω.om_pres _ _ hf`. Use `show res V V' W C B μ 𝓨 (heisO ψ V W _ (ω ((((γ : NI V C) * n : NI V C) : GA D V), 1) f)) 0 = _`. Rewrite using `[Subgroup.coe_mul, hω_mul, Module.End.mul_apply, res_om_heis hs hω hμ (γ : NI V C) hF]`. Take `⟨u0, hu0⟩` from `hrat _ (Subgroup.mem_subgroupOf.1 γ.2)`. Take `⟨a1, b1, hab⟩` from `rat_decomp hs h1 h2 h3 y _ (ni_fix (γ : NI V C).2).1 u0 hu0`.

Rewrite using `[hab]`. Conclude with `mean_rat_shift hs hψ hμ hF _ a1 b1`. Introduce `γ`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `GlobalTheory.AutFunCounterexample.GA_ext V` to reduce the goal to its premises.

Use `show Formalism.L2.Theta.mt V (z * ((γ : NI V C) : GA D V)) = Formalism.L2.Theta.mt V (((γ : NI V C) : GA D V) * z)`. Rewrite using `[mt_mul, mt_mul, hz]`. Conclude with `central_comm S₀ a (γ : NI V C).2`. Rewrite using `[show isoPart V W C (a • (y * S₀).map (incA D)) = a • (y * S₀ * (adj D C * V.gram)).map (incA D) by`. Simplify using `only [isoPart, Matrix.smul_mul, Matrix.map_mul],`.

Use the proof step `GlobalTheory.FinTranslate.symplOH_smul_left, symplOH_rat, pairing_trace h1, ha]`. Conclude with `hb`. Introduce `n`. Establish `hF : IsThetaFunO ψ V W (ω ((n : GA D V), 1) f)` using `hω.om_pres _ _ hf`. Use `show _ = _ * res V V' W C B μ 𝓨 (heisO ψ V W _ (ω (((⟨z, hzN⟩ * n : NI V C) : GA D V), 1) f)) 0`.

Rewrite using `[Subgroup.coe_mul, hω_mul, Module.End.mul_apply, res_om_heis hs hω hμ (⟨z, hzN⟩ : NI V C) hF]`. Use `show _ = _ * res V V' W C B μ 𝓨 (heisO ψ V W ((y * (adj D C' * V.gram)).map (incA D) * Formalism.L2.Theta.mt V z) _) 0`. Rewrite using `[iso_mt_central h1 y S₀ a hz]`. Conclude with `mean_iso_shift hs hψ hμ hF _ _ _`.
-/
theorem GlobalTheory.AnisoMean.aniso_mean_zero : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, adj D y * W.gram * y ≠ 0 → ∀ f, IsThetaFunO ψ V W f → ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω ((n : GA D V), 1) f)) 0 ∂κ = 0 := by
  intro D V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hμ κ 𝓝 hκ h𝓝 y hy f hf
  have hψ : IsStdChar D ψ (-1) := hω.std
  have : IsTopologicalGroup (GA D V) := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  have : BorelSpace (NI V C) := GlobalTheory.AutFunCounterexample.borel_NI D V C
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : Countable (NIQ V C) :=
    Function.Injective.countable (f := fun γ : NIQ V C =>
      (⟨((γ : NI V C) : GA D V), Subgroup.mem_subgroupOf.1 γ.2⟩ : GQ V))
      fun a b h => by
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (Subtype.ext h)
  have hCC : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hrat : ∀ g : GA D V, g ∈ GQ V →
      ∃ u : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V g = u.map (incA D) := by
    intro g hg
    have hg' : (matHom V g : GL (Fin V.rank) (AE D)) ∈ HFin (AF D.host.F) D.sp.cm.sig V.gram :=
      Subgroup.mem_subgroupOf.1 hg
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 hg'
    refine ⟨x.1, ?_⟩
    show ((matHom V g : GL (Fin V.rank) (AE D)) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = _
    rw [← hx]
    rfl
  have hM : (adj D y * W.gram * y)ᴴ = adj D y * W.gram * y := by
    rw [adj_eq]
    simp [Matrix.conjTranspose_mul, gram_herm, Matrix.mul_assoc]
  obtain ⟨S₀, hS₀, htr⟩ := exists_skew _ hM hy
  have ht : (1 / 2 : D.host.F) * Algebra.trace D.host.F D.host.E
      (D.host.xi0 * ((adj D y * W.gram * y) * S₀).trace) ≠ 0 := mul_ne_zero (by norm_num) htr
  obtain ⟨b, hb⟩ := hψ.1.2.2.2
  let a : AF D.host.F := b * algebraMap D.host.F (AF D.host.F) ((1 / 2 : D.host.F) *
    Algebra.trace D.host.F D.host.E (D.host.xi0 * ((adj D y * W.gram * y) * S₀).trace))⁻¹
  have ha : a * algebraMap D.host.F (AF D.host.F) ((1 / 2 : D.host.F) *
      Algebra.trace D.host.F D.host.E (D.host.xi0 * ((adj D y * W.gram * y) * S₀).trace)) = b := by
    simp only [a]
    rw [mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, mul_one]
  have hXX : (C * S₀ * (adj D C * V.gram)) * (C * S₀ * (adj D C * V.gram)) = 0 :=
    sq_zero_generic C S₀ (adj D C * V.gram) hCC
  have hsk : (C * S₀ * (adj D C * V.gram))ᴴ * V.gram + V.gram * (C * S₀ * (adj D C * V.gram)) = 0 := by
    rw [adj_eq]
    exact skew_generic V.gram (gram_herm V) C S₀ hS₀
  obtain ⟨z, hz⟩ := exists_central V _ hXX hsk a
  have hzN : z ∈ NI V C := central_mem_NI hs.frame S₀ a hz
  have hω_mul : ∀ g h : GA D V, ω (g * h, 1) = ω (g, 1) * ω (h, 1) := fun g h => by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have hw0 : isoPart V W C' (y.map (incA D)) = (y * (adj D C' * V.gram)).map (incA D) := by
    simp only [isoPart, Matrix.map_mul]
  rw [hw0]
  refine setIntegral_eq_zero_of_central (NIQ V C) κ h𝓝
    (fun n : NI V C => res V V' W C B μ 𝓨 (heisO ψ V W ((y * (adj D C' * V.gram)).map (incA D))
      (ω ((n : GA D V), 1) f)) 0) ?_ ⟨z, hzN⟩ ?_
    (ψ (symplOH V W (isoPart V W C (a • (y * S₀).map (incA D))) ((y * (adj D C' * V.gram)).map (incA D)))) ?_ ?_
  · intro γ n
    have hF : IsThetaFunO ψ V W (ω ((n : GA D V), 1) f) := hω.om_pres _ _ hf
    show res V V' W C B μ 𝓨 (heisO ψ V W _ (ω ((((γ : NI V C) * n : NI V C) : GA D V), 1) f)) 0 = _
    rw [Subgroup.coe_mul, hω_mul, Module.End.mul_apply, res_om_heis hs hω hμ (γ : NI V C) hF]
    obtain ⟨u0, hu0⟩ := hrat _ (Subgroup.mem_subgroupOf.1 γ.2)
    obtain ⟨a1, b1, hab⟩ := rat_decomp hs h1 h2 h3 y _ (ni_fix (γ : NI V C).2).1 u0 hu0
    rw [hab]
    exact mean_rat_shift hs hψ hμ hF _ a1 b1
  · intro γ
    apply Subtype.ext
    apply GlobalTheory.AutFunCounterexample.GA_ext V
    show Formalism.L2.Theta.mt V (z * ((γ : NI V C) : GA D V)) = Formalism.L2.Theta.mt V (((γ : NI V C) : GA D V) * z)
    rw [mt_mul, mt_mul, hz]
    exact central_comm S₀ a (γ : NI V C).2
  · rw [show isoPart V W C (a • (y * S₀).map (incA D)) = a • (y * S₀ * (adj D C * V.gram)).map (incA D) by
        simp only [isoPart, Matrix.smul_mul, Matrix.map_mul],
      GlobalTheory.FinTranslate.symplOH_smul_left, symplOH_rat, pairing_trace h1, ha]
    exact hb
  · intro n
    have hF : IsThetaFunO ψ V W (ω ((n : GA D V), 1) f) := hω.om_pres _ _ hf
    show _ = _ * res V V' W C B μ 𝓨 (heisO ψ V W _ (ω (((⟨z, hzN⟩ * n : NI V C) : GA D V), 1) f)) 0
    rw [Subgroup.coe_mul, hω_mul, Module.End.mul_apply, res_om_heis hs hω hμ (⟨z, hzN⟩ : NI V C) hF]
    show _ = _ * res V V' W C B μ 𝓨 (heisO ψ V W ((y * (adj D C' * V.gram)).map (incA D) * Formalism.L2.Theta.mt V z) _) 0
    rw [iso_mt_central h1 y S₀ a hz]
    exact mean_iso_shift hs hψ hμ hF _ _ _

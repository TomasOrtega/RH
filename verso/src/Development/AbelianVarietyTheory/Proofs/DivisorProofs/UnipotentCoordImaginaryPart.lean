import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditive
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicComplementDetNonzeroStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

open GlobalTheory.ThK.UnipDom.Additive in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ Y Y₁ H hCM hskew hiso`. Take `⟨hn, hxx, hyy, hxy, horth, hgram, _, hcY₁⟩` from `hiso`. Take `⟨w0⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Use `set τ : E →+* ℂ := (B.emb w0).1`. Establish `hinv : ∀ e, σ (σ e) = e`.

Introduce `e`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hCM.2.2.2, hCM.2.2.2, star_star]`. Establish `hsk : ∀ v v' : Fin n → E, form σ Y.J v' v = -σ (form σ Y.J v v')`. Introduce `v v'`.

Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, map_neg, hinv]`. Simplify using `only [Finset.mul_sum, hskew, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hdet : Y₁.J.det ≠ 0`. Introduce `h0`. Establish `hM0 : (Complex.I • Y₁.J.map τ).det = 0`. Rewrite using `[Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]`. Take `⟨v, hv, hMv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hM0`.

Establish `hpos` using `(hcY₁ w0).2.2 (star v) (by simpa using hv)`. Rewrite `hpos` using `[star_star, hMv, dotProduct_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ hpos`. Establish `hM : Matrix.vecMulVec H.x (Y.J *ᵥ fun i => σ (H.y i)) - Matrix.vecMulVec H.y (Y.J *ᵥ fun i => σ (H.x i)) + H.ι * (Y₁.Jᵀ)⁻¹ * (Y.J * H.ι.map σ)ᵀ = 1` using `GlobalTheory.T.hyperbolic_complement_det_nonzero F E σ hinv n n₁ Y.J Y₁.J H.x H.y H.ι hn hskew hxx hyy hxy horth hgram hdet`. Establish `hcont : Continuous (cA σ)` using `GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ`.

Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `⟨fun a => -((fun k => cA σ (a k)) ⬝ᵥ fun k => cA σ ((incM F (Y₁.Jᵀ)⁻¹ *ᵥ fun j => cA σ (a j)) k)), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Continuous fun a : Fin n₁ → AE F E => fun k => cA σ (a k)` using `continuous_pi fun k => hcont.comp (continuous_apply k)`. Establish `h2 : Continuous fun a : Fin n₁ → AE F E => incM F (Y₁.Jᵀ)⁻¹ *ᵥ fun j => cA σ (a j)` using `continuous_const.matrix_mulVec h1`.

Establish `h3 : Continuous fun a : Fin n₁ → AE F E => fun k => cA σ ((incM F (Y₁.Jᵀ)⁻¹ *ᵥ fun j => cA σ (a j)) k)` using `continuous_pi fun k => hcont.comp ((continuous_apply k).comp h2)`. Conclude with `(h1.dotProduct h3).neg`. Introduce `u hu`. Establish `hU : (mat u)ᵀ * incM F Y.J * (mat u).map (cA σ) = incM F Y.J` using `u.2`. Establish `hcv : ∀ {m : ℕ} (v : Fin m → AE F E) (A : Matrix (Fin n) (Fin m) (AE F E)), (fun i => cA σ ((A *ᵥ v) i)) = A.map (cA σ) *ᵥ fun i => cA σ (v i)`.

Introduce `m v A`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (cA σ).toRingHom A v i`. Establish `hfU : ∀ v v', fA σ Y.J (mat u *ᵥ v) (mat u *ᵥ v') = fA σ Y.J v v'`. Introduce `v v'`.

Simplify using `only [fA]`. Rewrite using `[hcv, Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU]`. Establish `fA_add_r : ∀ v w₁ w₂, fA σ Y.J v (w₁ + w₂) = fA σ Y.J v w₁ + fA σ Y.J v w₂`. Introduce `v w₁ w₂`. Simplify using `only [fA]`.

Rewrite using `[show (fun i => cA σ ((w₁ + w₂) i)) = (fun i => cA σ (w₁ i)) + fun i => cA σ (w₂ i) by funext i; simp, Matrix.mulVec_add, dotProduct_add]`. Establish `fA_smul_r : ∀ v w (a : AE F E), fA σ Y.J v (a • w) = cA σ a * fA σ Y.J v w`. Introduce `v w a`. Simplify using `only [fA]`. Rewrite using `[show (fun i => cA σ ((a • w) i)) = cA σ a • fun i => cA σ (w i) by funext i; simp, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.

Establish `hcV : ∀ {m : ℕ} (v : Fin m → E), (fun i => cA σ (incV F v i)) = incV F fun i => σ (v i)`. Introduce `m v`. Use function extensionality and compare the values at `i`. Simplify using `only [incV]`. Conclude with `cA_inclR σ (v i)`.

Use `set w := mat u *ᵥ incV F H.y with hw`. Establish `hxfix` using `(unip_spec hu).1`. Establish `hwx : fA σ Y.J w (incV F H.x) = -1`. Rewrite using `[hw, ← hxfix, hfU, fA_incV, hsk, hxy, map_one, map_neg, map_one]`. Establish `hwy : fA σ Y.J w w = 0` using `by rw [hw, hfU, fA_incV, hyy, map_zero]`.

Establish `hs : ∀ k, fA σ Y.J w (incM F H.ι *ᵥ Pi.single k 1) = cA σ (coA σ Y.J H u k)`. Introduce `k`. Take `⟨a, ha⟩` from `(unip_spec hu).2 (Pi.single k 1)`. Establish `hval : fA σ Y.J (incM F H.ι *ᵥ Pi.single k 1 + a • incV F H.x) (incV F H.y) = a`. Rewrite using `[fA_add_left, fA_smul_left, fA_incV, hxy, map_one, mul_one, single_eq_incV, incM_mulVec_incV, fA_incV, (horth _).2, map_zero, zero_add]`.

Establish `hco : coA σ Y.J H u k = a` using `by simp only [coA]; rw [ha, hval]`. Establish `h0 : fA σ Y.J w (mat u *ᵥ (incM F H.ι *ᵥ Pi.single k 1)) = 0`. Rewrite using `[hw, hfU, single_eq_incV, incM_mulVec_incV, fA_incV, hsk, (horth _).2, map_zero, neg_zero, map_zero]`. Rewrite `h0` using `[ha, fA_add_r, fA_smul_r, hwx]`. Rewrite using `[hco]`.

Take the linear combination `h0`. Use `set c := coC σ Y.J H u with hc`. Establish `hwc : fA σ Y.J w (incV F H.y) = c` using `rfl`. Use `set s : Fin n₁ → AE F E := fun k => cA σ (coA σ Y.J H u k) with hs_def`. Establish `hcol : ∀ k, (Y.J *ᵥ fun i => σ ((H.ι *ᵥ Pi.single k 1) i)) = fun i => (Y.J * H.ι.map σ) i k`.

Introduce `k`. Rewrite using `[Matrix.mulVec_single_one]`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`. Establish `hQ : (incM F (Y.J * H.ι.map σ))ᵀ *ᵥ w = s`.

Use function extensionality and compare the values at `k`. Rewrite using `[hs_def]`. Simplify using `only`. Rewrite using `[← hs k, single_eq_incV, incM_mulVec_incV]`. Simplify using `only [fA]`.

Rewrite using `[hcV, incM_mulVec_incV, hcol, Matrix.mulVec_transpose, dotProduct_comm]`. Simplify using `[Matrix.vecMul, dotProduct, incM, incV, mul_comm]`. Establish `hvm : ∀ (a r : Fin n → E), (inclR (F` using `F) (AF F)).mapMatrix (Matrix.vecMulVec a r) *ᵥ w = (incV F r ⬝ᵥ w) • incV F a := by`. Introduce `a r`. Rewrite using `[show (inclR (F := F) (AF F)).mapMatrix (Matrix.vecMulVec a r) = Matrix.vecMulVec (incV F a) (incV F r) by`.

Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec, incV], Matrix.vecMulVec_mulVec, op_smul_eq_smul]`. Establish `hdy : incV F (Y.J *ᵥ fun i => σ (H.y i)) ⬝ᵥ w = c`. Rewrite using `[← hwc, dotProduct_comm]`. Simplify using `only [fA]`.

Rewrite using `[hcV, incM_mulVec_incV]`. Establish `hdx : incV F (Y.J *ᵥ fun i => σ (H.x i)) ⬝ᵥ w = -1`. Rewrite using `[← hwx, dotProduct_comm]`. Simplify using `only [fA]`. Rewrite using `[hcV, incM_mulVec_incV]`.

Establish `hrec : w = c • incV F H.x + incV F H.y + incM F H.ι *ᵥ (incM F (Y₁.Jᵀ)⁻¹ *ᵥ s)`. Establish `h` using `congrArg (fun A => (inclR (F := F) (AF F)).mapMatrix A *ᵥ w) hM`. Simplify using `only [map_add, map_sub, map_mul, map_one, Matrix.one_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hvm, hdy, hdx] at h`. Rewrite using `[← hQ]`. Use `conv_lhs => rw [← h]`.

Simplify using `only [RingHom.mapMatrix_apply, incM, Matrix.transpose_map, neg_smul, one_smul, sub_neg_eq_add]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.transpose_map]`. Establish `hι : fA σ Y.J w (incM F H.ι *ᵥ (incM F (Y₁.Jᵀ)⁻¹ *ᵥ s)) = s ⬝ᵥ fun k => cA σ ((incM F (Y₁.Jᵀ)⁻¹ *ᵥ s) k)`. Simplify using `only [fA]`. Rewrite using `[hcv, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]`.

Rewrite using `[show incM F Y.J * (incM F H.ι).map (cA σ) = incM F (Y.J * H.ι.map σ) by`. Use extensionality with `i j`. Simplify using `[incM, Matrix.mul_apply, cA_inclR, map_sum, map_mul]]`. Rewrite using `[hQ]`. Establish `hfin` using `congrArg (fA σ Y.J w) hrec`.

Rewrite `hfin` using `[fA_add_r, fA_add_r, fA_smul_r, hwx, hwc, hι, hwy]`. Use `show c - cA σ c = -(s ⬝ᵥ fun k => cA σ ((incM F (Y₁.Jᵀ)⁻¹ *ᵥ s) k))`. Take the linear combination `(-1 : AE F E) * hfin`.
-/
theorem GlobalTheory.ThK.UnipDom.coC_sub_conj_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ → ∃ g : (Fin n₁ → AE F E) → AE F E, Continuous g ∧ ∀ u ∈ unip σ Y H, coC σ Y.J H u - cA σ (coC σ Y.J H u) = g (coA σ Y.J H u) := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H hCM hskew hiso
  obtain ⟨hn, hxx, hyy, hxy, horth, hgram, _, hcY₁⟩ := hiso
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ : E →+* ℂ := (B.emb w0).1
  have hinv : ∀ e, σ (σ e) = e := by
    intro e
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hsk : ∀ v v' : Fin n → E, form σ Y.J v' v = -σ (form σ Y.J v v') := by
    intro v v'
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, map_neg, hinv]
    simp only [Finset.mul_sum, hskew, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdet : Y₁.J.det ≠ 0 := by
    intro h0
    have hM0 : (Complex.I • Y₁.J.map τ).det = 0 := by
      rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hM0
    have hpos := (hcY₁ w0).2.2 (star v) (by simpa using hv)
    rw [star_star, hMv, dotProduct_zero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  have hM : Matrix.vecMulVec H.x (Y.J *ᵥ fun i => σ (H.y i)) - Matrix.vecMulVec H.y (Y.J *ᵥ fun i => σ (H.x i)) + H.ι * (Y₁.Jᵀ)⁻¹ * (Y.J * H.ι.map σ)ᵀ = 1 :=
    GlobalTheory.T.hyperbolic_complement_det_nonzero F E σ hinv n n₁ Y.J Y₁.J H.x H.y H.ι hn hskew hxx hyy hxy horth hgram hdet
  have hcont : Continuous (cA σ) := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine ⟨fun a => -((fun k => cA σ (a k)) ⬝ᵥ fun k => cA σ ((incM F (Y₁.Jᵀ)⁻¹ *ᵥ fun j => cA σ (a j)) k)), ?_, ?_⟩
  · have h1 : Continuous fun a : Fin n₁ → AE F E => fun k => cA σ (a k) :=
      continuous_pi fun k => hcont.comp (continuous_apply k)
    have h2 : Continuous fun a : Fin n₁ → AE F E => incM F (Y₁.Jᵀ)⁻¹ *ᵥ fun j => cA σ (a j) :=
      continuous_const.matrix_mulVec h1
    have h3 : Continuous fun a : Fin n₁ → AE F E => fun k => cA σ ((incM F (Y₁.Jᵀ)⁻¹ *ᵥ fun j => cA σ (a j)) k) :=
      continuous_pi fun k => hcont.comp ((continuous_apply k).comp h2)
    exact (h1.dotProduct h3).neg
  intro u hu
  have hU : (mat u)ᵀ * incM F Y.J * (mat u).map (cA σ) = incM F Y.J := u.2
  have hcv : ∀ {m : ℕ} (v : Fin m → AE F E) (A : Matrix (Fin n) (Fin m) (AE F E)),
      (fun i => cA σ ((A *ᵥ v) i)) = A.map (cA σ) *ᵥ fun i => cA σ (v i) := by
    intro m v A; funext i; exact RingHom.map_mulVec (cA σ).toRingHom A v i
  have hfU : ∀ v v', fA σ Y.J (mat u *ᵥ v) (mat u *ᵥ v') = fA σ Y.J v v' := by
    intro v v'
    simp only [fA]
    rw [hcv, Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_comm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU]
  have fA_add_r : ∀ v w₁ w₂, fA σ Y.J v (w₁ + w₂) = fA σ Y.J v w₁ + fA σ Y.J v w₂ := by
    intro v w₁ w₂
    simp only [fA]
    rw [show (fun i => cA σ ((w₁ + w₂) i)) = (fun i => cA σ (w₁ i)) + fun i => cA σ (w₂ i) by funext i; simp,
      Matrix.mulVec_add, dotProduct_add]
  have fA_smul_r : ∀ v w (a : AE F E), fA σ Y.J v (a • w) = cA σ a * fA σ Y.J v w := by
    intro v w a
    simp only [fA]
    rw [show (fun i => cA σ ((a • w) i)) = cA σ a • fun i => cA σ (w i) by funext i; simp,
      Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hcV : ∀ {m : ℕ} (v : Fin m → E), (fun i => cA σ (incV F v i)) = incV F fun i => σ (v i) := by
    intro m v; funext i; simp only [incV]; exact cA_inclR σ (v i)
  set w := mat u *ᵥ incV F H.y with hw
  have hxfix := (unip_spec hu).1
  have hwx : fA σ Y.J w (incV F H.x) = -1 := by
    rw [hw, ← hxfix, hfU, fA_incV, hsk, hxy, map_one, map_neg, map_one]
  have hwy : fA σ Y.J w w = 0 := by rw [hw, hfU, fA_incV, hyy, map_zero]
  have hs : ∀ k, fA σ Y.J w (incM F H.ι *ᵥ Pi.single k 1) = cA σ (coA σ Y.J H u k) := by
    intro k
    obtain ⟨a, ha⟩ := (unip_spec hu).2 (Pi.single k 1)
    have hval : fA σ Y.J (incM F H.ι *ᵥ Pi.single k 1 + a • incV F H.x) (incV F H.y) = a := by
      rw [fA_add_left, fA_smul_left, fA_incV, hxy, map_one, mul_one, single_eq_incV, incM_mulVec_incV, fA_incV,
        (horth _).2, map_zero, zero_add]
    have hco : coA σ Y.J H u k = a := by simp only [coA]; rw [ha, hval]
    have h0 : fA σ Y.J w (mat u *ᵥ (incM F H.ι *ᵥ Pi.single k 1)) = 0 := by
      rw [hw, hfU, single_eq_incV, incM_mulVec_incV, fA_incV, hsk, (horth _).2, map_zero, neg_zero, map_zero]
    rw [ha, fA_add_r, fA_smul_r, hwx] at h0
    rw [hco]; linear_combination h0
  set c := coC σ Y.J H u with hc
  have hwc : fA σ Y.J w (incV F H.y) = c := rfl
  set s : Fin n₁ → AE F E := fun k => cA σ (coA σ Y.J H u k) with hs_def
  have hcol : ∀ k, (Y.J *ᵥ fun i => σ ((H.ι *ᵥ Pi.single k 1) i)) = fun i => (Y.J * H.ι.map σ) i k := by
    intro k
    rw [Matrix.mulVec_single_one]
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hQ : (incM F (Y.J * H.ι.map σ))ᵀ *ᵥ w = s := by
    funext k
    rw [hs_def]; dsimp only; rw [← hs k, single_eq_incV, incM_mulVec_incV]
    simp only [fA]
    rw [hcV, incM_mulVec_incV, hcol, Matrix.mulVec_transpose, dotProduct_comm]
    simp [Matrix.vecMul, dotProduct, incM, incV, mul_comm]
  have hvm : ∀ (a r : Fin n → E), (inclR (F := F) (AF F)).mapMatrix (Matrix.vecMulVec a r) *ᵥ w = (incV F r ⬝ᵥ w) • incV F a := by
    intro a r
    rw [show (inclR (F := F) (AF F)).mapMatrix (Matrix.vecMulVec a r) = Matrix.vecMulVec (incV F a) (incV F r) by
      ext i j; simp [Matrix.vecMulVec, incV], Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  have hdy : incV F (Y.J *ᵥ fun i => σ (H.y i)) ⬝ᵥ w = c := by
    rw [← hwc, dotProduct_comm]; simp only [fA]; rw [hcV, incM_mulVec_incV]
  have hdx : incV F (Y.J *ᵥ fun i => σ (H.x i)) ⬝ᵥ w = -1 := by
    rw [← hwx, dotProduct_comm]; simp only [fA]; rw [hcV, incM_mulVec_incV]
  have hrec : w = c • incV F H.x + incV F H.y + incM F H.ι *ᵥ (incM F (Y₁.Jᵀ)⁻¹ *ᵥ s) := by
    have h := congrArg (fun A => (inclR (F := F) (AF F)).mapMatrix A *ᵥ w) hM
    simp only [map_add, map_sub, map_mul, map_one, Matrix.one_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, hvm, hdy, hdx] at h
    rw [← hQ]
    conv_lhs => rw [← h]
    simp only [RingHom.mapMatrix_apply, incM, Matrix.transpose_map, neg_smul, one_smul, sub_neg_eq_add]
    rw [Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.transpose_map]
  have hι : fA σ Y.J w (incM F H.ι *ᵥ (incM F (Y₁.Jᵀ)⁻¹ *ᵥ s)) = s ⬝ᵥ fun k => cA σ ((incM F (Y₁.Jᵀ)⁻¹ *ᵥ s) k) := by
    simp only [fA]
    rw [hcv, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [show incM F Y.J * (incM F H.ι).map (cA σ) = incM F (Y.J * H.ι.map σ) by
      ext i j; simp [incM, Matrix.mul_apply, cA_inclR, map_sum, map_mul]]
    rw [hQ]
  have hfin := congrArg (fA σ Y.J w) hrec
  rw [fA_add_r, fA_add_r, fA_smul_r, hwx, hwc, hι, hwy] at hfin
  show c - cA σ c = -(s ⬝ᵥ fun k => cA σ ((incM F (Y₁.Jᵀ)⁻¹ *ᵥ s) k))
  linear_combination (-1 : AE F E) * hfin

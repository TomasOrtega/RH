import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardEvaluationGoodModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationAGaussianIntegral
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

/- English proof (translation)
Establish `hz : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(c / 2) * ((s : ℂ) * s)) * y s) 0 t` using `fun t => by`. Establish `h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t` using `Complex.ofRealCLM.hasDerivAt`. Establish `h1` using `(((h0.mul h0).const_mul (-(c / 2))).cexp).mul (h t)`. Use `h1.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc` using `is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) 1 0`. Simplify using `only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, one_mul] at hc`. Rewrite using `[← hc, ← mul_assoc, ← Complex.exp_add]`. Simplify using the standard rewrite rules.
-/
private theorem ode_lin (y : ℝ → ℂ) (c : ℂ) (h : ∀ t : ℝ, HasDerivAt y (c * t * y t) t) :
    y 1 = Complex.exp (c / 2) * y 0 := by
  have hz : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(c / 2) * ((s : ℂ) * s)) * y s) 0 t := fun t => by
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h1 := (((h0.mul h0).const_mul (-(c / 2))).cexp).mul (h t)
    refine h1.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) 1 0
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Complex.exp_add]
  simp

/- English proof (translation)
Use extensionality with `y`. Establish `hlin : ∀ x c : κ → mixedEmbedding.mixedSpace F, lin c x = ((trP F κ x c : ℝ) : ℂ)` using `fun x c => rfl`. Establish `hL : ∀ x c : κ → mixedEmbedding.mixedSpace F, linL c x = trP F κ x c` using `fun x c => by`. Rewrite using `[linL_apply]`. Both sides reduce to the same expression.

Establish `hadd : trP F κ (y + w.1) b = trP F κ y b + trP F κ w.1 b`. Simplify using `[trP, add_mul, Finset.sum_add_distrib, map_add]`. Use `set φ : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun z => Complex.exp (-(2 * Real.pi * Complex.I) * ((trP F κ z w.2 + trP F κ w.1 w.2 / 2 : ℝ) : ℂ)) with hφdef`. Establish `hS : ∀ h : (κ → mixedEmbedding.mixedSpace F) → ℂ, schrF (trP F κ) w h = fun z => φ z * h (z + w.1)` using `fun h => rfl`. Establish `h1 : HasFDerivAt (fun z => ((trP F κ z w.2 + trP F κ w.1 w.2 / 2 : ℝ) : ℂ)) (Complex.ofRealCLM.comp (linL w.2)) y`.

Use `Complex.ofRealCLM.hasFDerivAt.comp y ((linL w.2).hasFDerivAt.add_const (trP F κ w.1 w.2 / 2))` as an intermediate fact. Conclude with `this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by simp [hL])`. Establish `hφ : HasFDerivAt φ (Complex.exp (-(2 * Real.pi * Complex.I) * ((trP F κ y w.2 + trP F κ w.1 w.2 / 2 : ℝ) : ℂ)) • ((-(2 * Real.pi * Complex.I)) • Complex.ofRealCLM.comp (linL w.2))) y` using `(h1.const_mul (-(2 * Real.pi * Complex.I))).cexp`. Establish `hf : HasFDerivAt (fun z => f (z + w.1)) (fderiv ℝ f (y + w.1)) y`. Use `(f.differentiableAt (x := y + w.1)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const w.1)` as an intermediate fact.

Conclude with `this`. Establish `hgd : fderiv ℝ g y a = φ y * fderiv ℝ f (y + w.1) a + f (y + w.1) * (φ y * (-(2 * Real.pi * Complex.I) * ((trP F κ a w.2 : ℝ) : ℂ)))`. Establish `hm : HasFDerivAt (fun z => φ z * f (z + w.1)) _ y` using `hφ.mul hf`. Rewrite using `[hg, hS, hm.fderiv]`. Simplify using `[hL, hφdef]`.

Establish `hgy : g y = φ y * f (y + w.1)` using `by rw [hg, hS]`. Establish `hg'y : g' y = φ y * dOp a b f (y + w.1)` using `by rw [hg', hS]`. Rewrite using `[hg'y, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, dOp_apply, dOp_apply, hgd, hgy, hlin, hlin, hadd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem conj_explicit {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (a b : κ → mixedEmbedding.mixedSpace F)
    (f g g' : SInf F κ) (hg : ⇑g = schrF (trP F κ) w ⇑f) (hg' : ⇑g' = schrF (trP F κ) w ⇑(dOp a b f)) :
    g' = dOp a b g + (2 * Real.pi * Complex.I * ((trP F κ a w.2 - trP F κ w.1 b : ℝ) : ℂ)) • g := by
  ext y
  have hlin : ∀ x c : κ → mixedEmbedding.mixedSpace F, lin c x = ((trP F κ x c : ℝ) : ℂ) := fun x c => rfl
  have hL : ∀ x c : κ → mixedEmbedding.mixedSpace F, linL c x = trP F κ x c := fun x c => by
    rw [linL_apply]; rfl
  have hadd : trP F κ (y + w.1) b = trP F κ y b + trP F κ w.1 b := by
    simp [trP, add_mul, Finset.sum_add_distrib, map_add]
  set φ : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun z =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((trP F κ z w.2 + trP F κ w.1 w.2 / 2 : ℝ) : ℂ)) with hφdef
  have hS : ∀ h : (κ → mixedEmbedding.mixedSpace F) → ℂ, schrF (trP F κ) w h = fun z => φ z * h (z + w.1) :=
    fun h => rfl
  have h1 : HasFDerivAt (fun z => ((trP F κ z w.2 + trP F κ w.1 w.2 / 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (linL w.2)) y := by
    have := Complex.ofRealCLM.hasFDerivAt.comp y ((linL w.2).hasFDerivAt.add_const (trP F κ w.1 w.2 / 2))
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by simp [hL])
  have hφ : HasFDerivAt φ (Complex.exp (-(2 * Real.pi * Complex.I) * ((trP F κ y w.2 + trP F κ w.1 w.2 / 2 : ℝ) : ℂ)) •
      ((-(2 * Real.pi * Complex.I)) • Complex.ofRealCLM.comp (linL w.2))) y :=
    (h1.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have hf : HasFDerivAt (fun z => f (z + w.1)) (fderiv ℝ f (y + w.1)) y := by
    have := (f.differentiableAt (x := y + w.1)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const w.1)
    exact this
  have hgd : fderiv ℝ g y a = φ y * fderiv ℝ f (y + w.1) a
      + f (y + w.1) * (φ y * (-(2 * Real.pi * Complex.I) * ((trP F κ a w.2 : ℝ) : ℂ))) := by
    have hm : HasFDerivAt (fun z => φ z * f (z + w.1)) _ y := hφ.mul hf
    rw [hg, hS, hm.fderiv]
    simp [hL, hφdef]
  have hgy : g y = φ y * f (y + w.1) := by rw [hg, hS]
  have hg'y : g' y = φ y * dOp a b f (y + w.1) := by rw [hg', hS]
  rw [hg'y, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, dOp_apply, dOp_apply, hgd, hgy,
    hlin, hlin, hadd]
  push_cast
  ring

/- English proof (translation)
Establish `hP` using `isPairing_trP (F := F) κ`. Establish `hL : ∀ x, linL b x = trP F κ x b` using `fun x => by rw [linL_apply]; rfl`. Set `S : ℝ → SInf F κ →L[ℂ] SInf F κ` to `fun t => (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linL b x + t ^ 2 * (trP F κ a b / 2) : ℝ) : ℂ)))).comp (SchwartzMap.compSubConstCLM ℂ (-(t • a)))`. Establish `hS : ∀ t f x, S t f x = Complex.exp (-(2 * Real.pi * Complex.I) * ((t * trP F κ x b + t ^ 2 * (trP F κ a b / 2) : ℝ) : ℂ)) * f (x + t • a)` using `fun t f x => by`. Simplify using `only [S, ContinuousLinearMap.comp_apply]`.

Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.HeisDer.hasTemperateGrowth_phase _ _ _), SchwartzMap.compSubConstCLM_apply, smul_eq_mul, sub_neg_eq_add, hL]`. Establish `hS' : ∀ t f, ⇑(S t f) = schrF (trP F κ) (t • a, t • b) ⇑f` using `fun t f => by`. Use function extensionality and compare the values at `x`. Rewrite using `[hS]`. Simplify using `only [schrF, hP.smulL, hP.smulR]`.

Use `congr 4`. Expand and normalize the polynomial expressions, which then agree. Establish `hadd : ∀ t h, S (t + h) g = S t (S h g)` using `fun t h => by`. Use extensionality with `x`. Rewrite using `[hS, hS, hS, ← mul_assoc, ← Complex.exp_add, hP.addL, hP.smulL, add_smul, add_assoc]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : ∀ T : SInf F κ →L[ℂ] ℂ, HasDerivAt (fun t : ℝ => T (S t g)) (T (dOp a b g)) 0` using `fun T => by`. Establish `h` using `GlobalTheory.HeisDer.hasDerivAt_heis a (linL b) (trP F κ a b / 2) g T`.

Establish `e : (fun x => ((linL b x : ℝ) : ℂ)) = lin b` using `funext fun x => by rw [linL_apply]; rfl`. Rewrite `h` using `[e]`. Conclude with `h`. Use `⟨Complex.exp (z * (2 * Real.pi * Complex.I * ((trP F κ a' b - trP F κ a b' : ℝ) : ℂ)) / 2), fun T hT => ?_⟩` and prove the remaining obligations. Establish `key` using `ode_lin (fun t => T (S t g)) (z * (2 * Real.pi * Complex.I * ((trP F κ a' b - trP F κ a b' : ℝ) : ℂ))) fun t => by`.

Establish `h1` using `hd (T.comp (S t))`. Establish `h2 : HasDerivAt (fun s : ℝ => (T.comp (S t)) (S (s - t) g)) ((T.comp (S t)) (dOp a b g)) t`. Rewrite `h1` using `[← sub_self t]`. Conclude with `h1.comp_sub_const t t`. Establish `e : (fun s : ℝ => (T.comp (S t)) (S (s - t) g)) = fun s => T (S s g)`.

Use function extensionality and compare the values at `s`. Rewrite using `[ContinuousLinearMap.comp_apply, ← hadd, add_sub_cancel]`. Rewrite `h2` using `[e]`. Use `h2.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply, hv, map_smul, map_smul, conj_explicit (t • a, t • b) a' b' g (S t g) _ (hS' t g) (hS' t _), map_add, hT, map_smul]`.

Simplify using `only [hP.smulL, hP.smulR, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : S 1 g = g₁` using `DFunLike.coe_injective (by`. Express the relevant statement in the definitionally equal form `⇑(S 1 g) = ⇑g₁`.

Rewrite using `[hS', hg₁, one_smul, one_smul])`. Establish `e0 : S 0 g = g`. Use extensionality with `x`. Rewrite using `[hS]`. Simplify using the standard rewrite rules.

Simplify `key` using `only [e1, e0]`.
-/
private theorem line_core {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (a b a' b' : κ → mixedEmbedding.mixedSpace F) (z : ℂ) (g g₁ : SInf F κ)
    (hv : dOp a b g = z • dOp a' b' g) (hg₁ : ⇑g₁ = schrF (trP F κ) (a, b) ⇑g) :
    ∃ c : ℂ, ∀ T : SInf F κ →L[ℂ] ℂ, (∀ f, T (dOp a' b' f) = 0) → T g₁ = c * T g := by
  have hP := isPairing_trP (F := F) κ
  have hL : ∀ x, linL b x = trP F κ x b := fun x => by rw [linL_apply]; rfl
  let S : ℝ → SInf F κ →L[ℂ] SInf F κ := fun t =>
    (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) *
      ((t * linL b x + t ^ 2 * (trP F κ a b / 2) : ℝ) : ℂ)))).comp (SchwartzMap.compSubConstCLM ℂ (-(t • a)))
  have hS : ∀ t f x, S t f x = Complex.exp (-(2 * Real.pi * Complex.I) *
      ((t * trP F κ x b + t ^ 2 * (trP F κ a b / 2) : ℝ) : ℂ)) * f (x + t • a) := fun t f x => by
    simp only [S, ContinuousLinearMap.comp_apply]
    rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.HeisDer.hasTemperateGrowth_phase _ _ _),
      SchwartzMap.compSubConstCLM_apply, smul_eq_mul, sub_neg_eq_add, hL]
  have hS' : ∀ t f, ⇑(S t f) = schrF (trP F κ) (t • a, t • b) ⇑f := fun t f => by
    funext x
    rw [hS]
    simp only [schrF, hP.smulL, hP.smulR]
    congr 4
    ring
  have hadd : ∀ t h, S (t + h) g = S t (S h g) := fun t h => by
    ext x
    rw [hS, hS, hS, ← mul_assoc, ← Complex.exp_add, hP.addL, hP.smulL, add_smul, add_assoc]
    congr 2
    push_cast
    ring
  have hd : ∀ T : SInf F κ →L[ℂ] ℂ, HasDerivAt (fun t : ℝ => T (S t g)) (T (dOp a b g)) 0 := fun T => by
    have h := GlobalTheory.HeisDer.hasDerivAt_heis a (linL b) (trP F κ a b / 2) g T
    have e : (fun x => ((linL b x : ℝ) : ℂ)) = lin b := funext fun x => by rw [linL_apply]; rfl
    rw [e] at h
    exact h
  refine ⟨Complex.exp (z * (2 * Real.pi * Complex.I * ((trP F κ a' b - trP F κ a b' : ℝ) : ℂ)) / 2), fun T hT => ?_⟩
  have key := ode_lin (fun t => T (S t g)) (z * (2 * Real.pi * Complex.I * ((trP F κ a' b - trP F κ a b' : ℝ) : ℂ)))
    fun t => by
      have h1 := hd (T.comp (S t))
      have h2 : HasDerivAt (fun s : ℝ => (T.comp (S t)) (S (s - t) g)) ((T.comp (S t)) (dOp a b g)) t := by
        rw [← sub_self t] at h1
        exact h1.comp_sub_const t t
      have e : (fun s : ℝ => (T.comp (S t)) (S (s - t) g)) = fun s => T (S s g) := by
        funext s
        rw [ContinuousLinearMap.comp_apply, ← hadd, add_sub_cancel]
      rw [e] at h2
      refine h2.congr_deriv ?_
      rw [ContinuousLinearMap.comp_apply, hv, map_smul, map_smul,
        conj_explicit (t • a, t • b) a' b' g (S t g) _ (hS' t g) (hS' t _), map_add, hT, map_smul]
      simp only [hP.smulL, hP.smulR, smul_eq_mul]
      push_cast
      ring
  have e1 : S 1 g = g₁ := DFunLike.coe_injective (by
    change ⇑(S 1 g) = ⇑g₁
    rw [hS', hg₁, one_smul, one_smul])
  have e0 : S 0 g = g := by
    ext x
    rw [hS]
    simp
  simpa only [e1, e0] using key

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' hC hT hG e hE ei ev hev hpe l _ g hg`. Establish `hψ : IsStd B.ψ` using `hT.base.std`. Establish `hM : G.M.IsGood B.ψ` using `hT.geo.hM`. Take `⟨y, z, hv⟩` from `GlobalTheory.ThK.VacDualPart.dOp_dual_vac F E σ B b a' G G₁ H H' X om om' hC hT g hg (l.1 • incV F H.x) 0`. Establish `hs : Matrix.vecMulVec (l.1 • incV F H.x) (incV F H'.y) + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ (0 : Fin (b + a') → AE F E)) = shiftA H H' l`.

Rewrite using `[Matrix.mulVec_zero]`. Use extensionality with `i j`. Simplify using `only [shiftA, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]`. Rewrite using `[mul_assoc]`. Conclude with `(congrArg _ (mul_zero (incV F H.y i))).trans (add_zero _)`.

Rewrite `hv` using `[hs]`. Establish `k` using `GlobalTheory.ThK.EvPolKill.ei_dOp_coordI_eq_zero F E σ B _ _ _ _ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι (isoA H H') e hψ hM hG hE ei ev hev hpe`. Establish `h1` using `k (Matrix.vecMulVec y (incV F H'.x)) (fun t => Or.inl ⟨realAd F t • y, by rw [Matrix.smul_vecMulVec]⟩)`. Establish `h2` using `k (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z)) (fun t => Or.inr ⟨realAd F t • z, by rw [Matrix.mulVec_smul, Matrix.vecMulVec_smul]⟩)`. Establish `hadd : ∀ (p q p' q' : Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) f, dOp (p + p') (q + q') f = dOp p q f + dOp p' q' f` using `fun p q p' q' f => by`.

Use extensionality with `x`. Simplify using `only [dOp_apply, SchwartzMap.add_apply, map_add, lin, Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hc⟩` from `line_core _ _ _ _ _ g _ hv (locOpInf_rho G.M.co hψ (shiftA H H' l) g).2`.

Use `⟨c, SchwartzMap.ext fun x => ?_⟩` and prove the remaining obligations. Use `hc (((BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).comp ei) fun f => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply, coordI_add, Prod.fst_add, Prod.snd_add, hadd, map_add, h1, h2, add_zero, map_zero]`.
-/
theorem _root_.GlobalTheory.T.configuration_a_local_evaluation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), CfgA B G G₁ H H' → IsTriple B G X om om' →
    G₁.M.IsGood B.ψ → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      (∀ v, ev v (G.M.vac v) = G₁.M.vac v) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ l ∈ idelesAt E (evI F), ∀ g, GaussD G.M B.emb g →
      ∃ c : ℂ, ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) g) = c • ei g := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' hC hT hG e hE ei ev hev hpe l _ g hg
  have hψ : IsStd B.ψ := hT.base.std
  have hM : G.M.IsGood B.ψ := hT.geo.hM
  obtain ⟨y, z, hv⟩ := GlobalTheory.ThK.VacDualPart.dOp_dual_vac F E σ B b a' G G₁ H H' X om om' hC hT g hg (l.1 • incV F H.x) 0
  have hs : Matrix.vecMulVec (l.1 • incV F H.x) (incV F H'.y) +
      Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ (0 : Fin (b + a') → AE F E)) = shiftA H H' l := by
    rw [Matrix.mulVec_zero]
    ext i j
    simp only [shiftA, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul]
    rw [mul_assoc]
    exact (congrArg _ (mul_zero (incV F H.y i))).trans (add_zero _)
  rw [hs] at hv
  have k := GlobalTheory.ThK.EvPolKill.ei_dOp_coordI_eq_zero F E σ B _ _ _ _ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι (isoA H H') e hψ hM hG hE ei ev hev hpe
  have h1 := k (Matrix.vecMulVec y (incV F H'.x)) (fun t => Or.inl ⟨realAd F t • y, by rw [Matrix.smul_vecMulVec]⟩)
  have h2 := k (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z))
    (fun t => Or.inr ⟨realAd F t • z, by rw [Matrix.mulVec_smul, Matrix.vecMulVec_smul]⟩)
  have hadd : ∀ (p q p' q' : Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) f,
      dOp (p + p') (q + q') f = dOp p q f + dOp p' q' f := fun p q p' q' f => by
    ext x
    simp only [dOp_apply, SchwartzMap.add_apply, map_add, lin, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    push_cast
    ring
  obtain ⟨c, hc⟩ := line_core _ _ _ _ _ g _ hv (locOpInf_rho G.M.co hψ (shiftA H H' l) g).2
  refine ⟨c, SchwartzMap.ext fun x => ?_⟩
  refine hc (((BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).comp ei) fun f => ?_
  rw [ContinuousLinearMap.comp_apply, coordI_add, Prod.fst_add, Prod.snd_add, hadd, map_add, h1, h2, add_zero, map_zero]

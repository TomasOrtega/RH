import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

noncomputable section

namespace GlobalTheory.TorusTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

abbrev finPart : AE F E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

/- English proof (translation)
Establish `key : ∀ z : AE F E, z = LinearMap.rTensor E (LinearMap.inl F (Ainf F) (Af F)) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) + LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F)) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero, map_zero, map_zero, add_zero]`. Conclude with `rfl`.

Consider the case `tmul x y`. Simplify using `only [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, AlgHom.id_apply, ← TensorProduct.add_tmul]`. Use `congr 1`. Conclude with `Prod.ext (by change x.1 = x.1 + 0; simp) (by change x.2 = 0 + x.2; simp)`. Consider the case `add x y hx hy`.

Rewrite using `[map_add, map_add, map_add, map_add, add_add_add_comm, ← hx, ← hy]`. Conclude with `rfl`. Establish `e : ∀ (w : InfinitePlace F) (z : AE F E), Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) = compInf F E w z` using `fun w z => by`. Rewrite using `[← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]`. Both sides reduce to the same expression.

Establish `hinf : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z = Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z'` using `GlobalTheory.AutFunCompare.infTens_ext fun w => (infEmb_bijective h (Classical.arbitrary (EmbOver E w))).1 (by rw [e, e]; exact hi w _)`. Rewrite using `[key z, key z', hinf]`. Conclude with `congrArg _ (congrArg (LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F))) hf)`.
-/
theorem ae_ext {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {z z' : AE F E} (hf : finPart F E z = finPart F E z')
    (hi : ∀ (w : InfinitePlace F) (τ : EmbOver E w), infEmb τ (compInf F E w z) = infEmb τ (compInf F E w z')) :
    z = z' := by
  have key : ∀ z : AE F E, z = LinearMap.rTensor E (LinearMap.inl F (Ainf F) (Af F))
        (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F))
        (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero, add_zero]; exact rfl
    | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, AlgHom.id_apply, ← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (by change x.1 = x.1 + 0; simp) (by change x.2 = 0 + x.2; simp)
    | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, add_add_add_comm, ← hx, ← hy]; exact rfl
  have e : ∀ (w : InfinitePlace F) (z : AE F E), Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) = compInf F E w z := fun w z => by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  have hinf : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z = Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z' :=
    GlobalTheory.AutFunCompare.infTens_ext fun w => (infEmb_bijective h (Classical.arbitrary (EmbOver E w))).1
      (by rw [e, e]; exact hi w _)
  rw [key z, key z', hinf]
  exact congrArg _ (congrArg (LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F))) hf)

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply]`. Establish `: sndA F (realAd F s) = 0` using `rfl`. Simplify using `[this]`.
-/
theorem finPart_realAd_smul (s : ℝ) (x : AE F E) : finPart F E (realAd F s • x) = 0 := by
  rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply]
  have : sndA F (realAd F s) = 0 := rfl
  simp [this]

/- English proof (translation)
Use `h.1` as an intermediate fact. Establish `hw : w.IsReal` using `IsTotallyReal.isReal w`. Rewrite using `[Algebra.smul_def, map_mul, map_mul, Algebra.TensorProduct.algebraMap_apply]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F s)) * τ.1 1 = _`.

Rewrite using `[map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedEmbedding.mixedSpace F) s) w) = s`. Establish `hy` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (algebraMap ℝ (mixedEmbedding.mixedSpace F) s)`. Rewrite `hy` using `[InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`.

Use `congrFun (congrArg Prod.fst hy) ⟨w, hw⟩` as an intermediate fact. Simplify using `using this`.
-/
theorem infEmb_realAd_smul {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (w : InfinitePlace F) (τ : EmbOver E w) (s : ℝ) (x : AE F E) :
    infEmb τ (compInf F E w (realAd F s • x)) = (s : ℂ) * infEmb τ (compInf F E w x) := by
  have := h.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [Algebra.smul_def, map_mul, map_mul, Algebra.TensorProduct.algebraMap_apply]
  congr 1
  change InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F s)) * τ.1 1 = _
  rw [map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  congr 1
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedEmbedding.mixedSpace F) s) w) = s
  have hy := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (algebraMap ℝ (mixedEmbedding.mixedSpace F) s)
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hy
  have := congrFun (congrArg Prod.fst hy) ⟨w, hw⟩
  simpa using this

end GlobalTheory.TorusTranslate

namespace GlobalTheory.TorusTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `congrFun (congrFun h k) i` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.mul_diagonal]`. Simplify `this` using `[Matrix.mulVec, dotProduct]`.
-/
theorem mulVec_col {n q : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin q) ℂ} {d : Fin q → ℂ}
    (h : A * B = B * Matrix.diagonal d) (i : Fin q) : A *ᵥ (fun k => B k i) = fun k => B k i * d i := by
  funext k
  have := congrFun (congrFun h k) i
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at this
  simpa [Matrix.mulVec, dotProduct] using this

end GlobalTheory.TorusTranslate

namespace GlobalTheory.TorusTranslate

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J hJ q Xf Yf t a ha a' ha'`. Establish `hMa : mat a' = (HA.mat (AF F) σ ((1 : E) • J.map σ) a).1` using `congrArg Units.val ha'`. Establish `hfin : ∀ v : Fin n → AE F E, ∀ k, finPart F E (((mat a' - 1) *ᵥ v) k) = 0` using `fun v k => by`. Rewrite using `[RingHom.map_mulVec]`. Establish `h0 : (mat a' - 1).map (finPart F E) = 0` using `Matrix.ext fun i j => by`.

Use `congrArg (fun g : GL (Fin n) (Af F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) (MonoidHom.mem_ker.1 ha.1)` as an intermediate fact. Rewrite using `[Matrix.map_apply, Matrix.sub_apply, map_sub, hMa]`. Establish `e1 : finPart F E ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Rewrite using `[e1]`.

Conclude with `sub_eq_zero.2 this`. Rewrite using `[h0, Matrix.zero_mulVec]`. Both sides reduce to the same expression. Establish `harch : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (v : Fin n → AE F E) k, infEmb τ (compInf F E w (((mat a' - 1) *ᵥ v) k)) = (GlobalTheory.Orb.archMat σ ((1 : E) • J.map σ) τ (projArch σ ((1 : E) • J.map σ) w a) *ᵥ (fun j => infEmb τ (compInf F E w (v j)))) k - infEmb τ (compInf …` using `fun w τ v k => by`. Establish `e : ((infEmb τ).comp (compInf F E w)) (((mat a' - 1) *ᵥ v) k) = _` using `RingHom.map_mulVec _ _ _ _`.

Use `e.trans ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.sub_mulVec, Pi.sub_apply, hMa]`. Use `congr 1`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`. Both sides reduce to the same expression.

Establish `h0 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (x : E), infEmb τ (compInf F E w (inclR (F` using `F) (AF F) x)) = τ.1 x := fun w τ x => by`. Express the relevant statement in the definitionally equal form `infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _`. Simplify using the standard rewrite rules. Use `⟨fun i => funext fun k => ae_ext h ?_ ?_, fun i => funext fun k => ae_ext h ?_ ?_, fun z hx hy => funext fun k => ae_ext h ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[hfin, Pi.smul_apply, finPart_realAd_smul]`.

Introduce `w τ`. Rewrite using `[harch, Pi.smul_apply, infEmb_realAd_smul h]`. Simplify using `only [incV, h0]`. Establish `hc` using `mulVec_col (ha.2 w τ).1 i`. Simplify using `only [Matrix.map_apply] at hc`.

Rewrite using `[hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfin, Pi.smul_apply, finPart_realAd_smul]`. Introduce `w τ`.

Rewrite using `[harch, Pi.smul_apply, infEmb_realAd_smul h]`. Simplify using `only [incV, h0]`. Establish `hc` using `mulVec_col (ha.2 w τ).2.1 i`. Simplify using `only [Matrix.map_apply] at hc`. Rewrite using `[hc]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfin, Pi.zero_apply, map_zero]`. Introduce `w τ`. Establish `hc : ∀ (Z : Matrix (Fin n) (Fin q) E), (∀ i, form σ J z (fun k => Z k i) = 0) → (Formalism.UG.cT (σ : E →+* E) Z * ((1 : E) • J.map σ)) *ᵥ z = 0` using `fun Z hZ => funext fun i => by`.

Rewrite using `[Pi.zero_apply, ← hZ i]`. Simplify using `only [one_smul, Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, form, RingHom.coe_coe, hJ, Pi.zero_apply]`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`. Use `first`. Consider the case `exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Consider the case `(rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)`. Establish `e` using `(ha.2 w τ).2.2 z (hc Xf hx) (hc Yf hy)`. Rewrite using `[harch, Pi.zero_apply, map_zero, map_zero]`. Simplify using `only [incV, h0]`. Rewrite using `[e, sub_self]`.
-/
theorem isTorusU_of_isTorusElt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) →
    ∀ (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E) (t : Fin q → ℝ) (a : GAd σ ((1 : E) • J.map σ)),
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • J.map σ) Xf Yf t a →
      ∀ a' : UA σ J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • J.map σ) a →
      IsTorusU (fun i k => Xf k i) (fun i k => Yf k i) t a' := by
  intro F E _ _ _ _ _ σ h n J hJ q Xf Yf t a ha a' ha'
  have hMa : mat a' = (HA.mat (AF F) σ ((1 : E) • J.map σ) a).1 := congrArg Units.val ha'

  have hfin : ∀ v : Fin n → AE F E, ∀ k, finPart F E (((mat a' - 1) *ᵥ v) k) = 0 := fun v k => by
    rw [RingHom.map_mulVec]
    have h0 : (mat a' - 1).map (finPart F E) = 0 := Matrix.ext fun i j => by
      have := congrArg (fun g : GL (Fin n) (Af F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)
        (MonoidHom.mem_ker.1 ha.1)
      rw [Matrix.map_apply, Matrix.sub_apply, map_sub, hMa]
      have e1 : finPart F E ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j := by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [e1]
      exact sub_eq_zero.2 this
    rw [h0, Matrix.zero_mulVec]
    rfl

  have harch : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (v : Fin n → AE F E) k,
      infEmb τ (compInf F E w (((mat a' - 1) *ᵥ v) k)) =
        (GlobalTheory.Orb.archMat σ ((1 : E) • J.map σ) τ (projArch σ ((1 : E) • J.map σ) w a) *ᵥ
          (fun j => infEmb τ (compInf F E w (v j)))) k - infEmb τ (compInf F E w (v k)) := fun w τ v k => by
    have e : ((infEmb τ).comp (compInf F E w)) (((mat a' - 1) *ᵥ v) k) = _ := RingHom.map_mulVec _ _ _ _
    refine e.trans ?_
    rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mulVec, Pi.sub_apply, hMa]
    congr 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rfl
  have h0 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (x : E), infEmb τ (compInf F E w (inclR (F := F) (AF F) x)) = τ.1 x :=
    fun w τ x => by
      change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
      simp
  refine ⟨fun i => funext fun k => ae_ext h ?_ ?_, fun i => funext fun k => ae_ext h ?_ ?_, fun z hx hy => funext fun k => ae_ext h ?_ ?_⟩
  · rw [hfin, Pi.smul_apply, finPart_realAd_smul]
  · intro w τ
    rw [harch, Pi.smul_apply, infEmb_realAd_smul h]
    simp only [incV, h0]
    have hc := mulVec_col (ha.2 w τ).1 i
    simp only [Matrix.map_apply] at hc
    rw [hc]
    push_cast
    ring
  · rw [hfin, Pi.smul_apply, finPart_realAd_smul]
  · intro w τ
    rw [harch, Pi.smul_apply, infEmb_realAd_smul h]
    simp only [incV, h0]
    have hc := mulVec_col (ha.2 w τ).2.1 i
    simp only [Matrix.map_apply] at hc
    rw [hc]
    push_cast
    ring
  · rw [hfin, Pi.zero_apply, map_zero]
  · intro w τ
    have hc : ∀ (Z : Matrix (Fin n) (Fin q) E), (∀ i, form σ J z (fun k => Z k i) = 0) →
        (Formalism.UG.cT (σ : E →+* E) Z * ((1 : E) • J.map σ)) *ᵥ z = 0 := fun Z hZ => funext fun i => by
      rw [Pi.zero_apply, ← hZ i]
      simp only [one_smul, Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply,
        Matrix.transpose_apply, form, RingHom.coe_coe, hJ, Pi.zero_apply]
      simp only [Finset.sum_mul, Finset.mul_sum]
      first
        | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    have e := (ha.2 w τ).2.2 z (hc Xf hx) (hc Yf hy)
    rw [harch, Pi.zero_apply, map_zero, map_zero]
    simp only [incV, h0]
    rw [e, sub_self]

end GlobalTheory.TorusTranslate

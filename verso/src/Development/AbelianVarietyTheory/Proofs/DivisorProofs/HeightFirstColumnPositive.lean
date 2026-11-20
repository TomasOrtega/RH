import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain

noncomputable section
namespace GlobalTheory.EisMidHt
open GlobalTheory.Doubling (absEv absEw unitFin unitInf)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J L v k hk u`. Unfold `normFin`. Use `congr 1`. Use extensionality with `c`. Use `exists_congr fun l => and_congr_left fun _ => ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_smul]`. Conclude with `(mem_stabLoc.1 hk _).symm`.
-/
theorem normFin_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (v : HeightOneSpectrum (𝓞 F)) (k : GLoc σ J v), k ∈ stabLoc σ J L v → ∀ u : Fin n → Fv F v ⊗[F] E,
      normFin F L v ((matHom _ σ J k).1 *ᵥ u) = normFin F L v u := by
  intro F E _ _ _ _ _ σ n J L v k hk u
  unfold normFin
  congr 1
  ext c
  refine exists_congr fun l => and_congr_left fun _ => ?_
  rw [← Matrix.mulVec_smul]
  exact (mem_stabLoc.1 hk _).symm

/- English proof (translation)
Introduce `F E _ _ _ _ _ n L v μ u`. Unfold `normFin`. Establish `hμ : 0 < absEv F E v μ`. Use `pos_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Use `map_mul (absEv F E v) μ μ⁻¹` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel, map_one, h0, zero_mul]`. Conclude with `one_ne_zero this`. Establish `hset : {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • ((μ : Fv F v ⊗[F] E) • u) ∈ latLoc F L v ∧ c = absEv F E v l} = (OrderIso.mulLeft₀ (absEv F E v μ) hμ) '' {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • u ∈ latLoc F L v ∧ …`. Use extensionality with `c`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨l, hl, rfl⟩`. Use `⟨absEv F E v (μ⁻¹ * l), ⟨μ⁻¹ * l, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_rev, inv_inv, Units.val_mul, mul_smul]` and apply the resulting hypothesis. Simplify using `[map_mul, ← mul_assoc, ← map_mul]`. Introduce and unpack `⟨_, ⟨l, hl, rfl⟩, rfl⟩`.

Use `⟨μ * l, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_rev, Units.val_mul, mul_smul, ← mul_smul ((μ⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E), Units.inv_mul, one_smul]` and apply the resulting hypothesis. Simplify using `[map_mul]`. Rewrite using `[hset]`. Break down `Set.eq_empty_or_nonempty {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • u ∈ latLoc F L v ∧ c = absEv F E v l} with hS | hS` into its components or cases.

Rewrite using `[hS, Set.image_empty, NNReal.sInf_empty, mul_zero]`. Rewrite using `[sInf_image', ← OrderIso.map_csInf _ hS (OrderBot.bddBelow _)]`. Both sides reduce to the same expression.
-/
theorem normFin_unit_smul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (μ : (Fv F v ⊗[F] E)ˣ) (u : Fin n → Fv F v ⊗[F] E),
      normFin F L v ((μ : Fv F v ⊗[F] E) • u) = absEv F E v μ * normFin F L v u := by
  intro F E _ _ _ _ _ n L v μ u
  unfold normFin
  have hμ : 0 < absEv F E v μ := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have := map_mul (absEv F E v) μ μ⁻¹
    rw [mul_inv_cancel, map_one, h0, zero_mul] at this
    exact one_ne_zero this
  have hset : {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • ((μ : Fv F v ⊗[F] E) • u) ∈
      latLoc F L v ∧ c = absEv F E v l} = (OrderIso.mulLeft₀ (absEv F E v μ) hμ) ''
      {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • u ∈ latLoc F L v ∧ c = absEv F E v l} := by
    ext c
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨absEv F E v (μ⁻¹ * l), ⟨μ⁻¹ * l, ?_, rfl⟩, ?_⟩
      · rwa [mul_inv_rev, inv_inv, Units.val_mul, mul_smul]
      · simp [map_mul, ← mul_assoc, ← map_mul]
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨μ * l, ?_, ?_⟩
      · rwa [mul_inv_rev, Units.val_mul, mul_smul, ← mul_smul ((μ⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E), Units.inv_mul, one_smul]
      · simp [map_mul]
  rw [hset]
  rcases Set.eq_empty_or_nonempty {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • u ∈
      latLoc F L v ∧ c = absEv F E v l} with hS | hS
  · rw [hS, Set.image_empty, NNReal.sInf_empty, mul_zero]
  · rw [sInf_image', ← OrderIso.map_csInf _ hS (OrderBot.bddBelow _)]
    rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ n a w μ u`. Unfold `normInf`. Simplify using `only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, ← Finset.mul_sum, norm_mul, mul_pow, GlobalTheory.Doubling.absEw_apply, NNReal.coe_pow, coe_nnnorm]`.
-/
theorem normInf_unit_smul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F) (μ : (w.Completion ⊗[F] E)ˣ) (u : Fin n → w.Completion ⊗[F] E),
      normInf a w ((μ : w.Completion ⊗[F] E) • u) = absEw F E w μ * normInf a w u := by
  intro F E _ _ _ _ _ n a w μ u
  unfold normInf
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, ← Finset.mul_sum, norm_mul, mul_pow,
    GlobalTheory.Doubling.absEw_apply, NNReal.coe_pow, coe_nnnorm]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J hCM a w k hk u`. Establish `hU` using `mem_stabArch.1 hk`. Use `set B := Formalism.UG.bc (compInf F E w) a`. Use `set U := B⁻¹ * matHom _ σ J k * B`. Establish `hU' : Formalism.UG.cT (sigR _ σ) U.1 * U.1 = 1`.

Use `hU` as an intermediate fact. Express the relevant statement in the definitionally equal form `Formalism.UG.cT (sigR _ σ) U.1 * 1 * U.1 = 1 at this`. Rewrite `this` using `[Matrix.mul_one]`. Then use the resulting hypothesis. Establish `e1 : (B⁻¹).1 *ᵥ ((matHom _ σ J k).1 *ᵥ u) = U.1 *ᵥ ((B⁻¹).1 *ᵥ u)`. Simplify using `only [U, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]`.

Rewrite using `[← Units.val_mul B, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Establish `key : ∀ z : Fin n → w.Completion ⊗[F] E, ∑ i, Algebra.norm w.Completion ((U.1 *ᵥ z) i) = ∑ i, Algebra.norm w.Completion (z i)`. Introduce `z`. Apply `(algebraMap w.Completion (w.Completion ⊗[F] E)).injective` to reduce the goal to its premises. Simplify using `only [map_sum, GlobalTheory.Doubling.algebraMap_norm_eq hCM]`.

Establish `h2 : ∀ y : Fin n → w.Completion ⊗[F] E, ∑ i, y i * sigR _ σ (y i) = (fun i => sigR _ σ (y i)) ⬝ᵥ y` using `fun y => by`. Simplify using `only [dotProduct]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Rewrite using `[h2, h2]`. Establish `h3 : (fun i => sigR _ σ ((U.1 *ᵥ z) i)) = (fun i => sigR _ σ (z i)) ᵥ* (Formalism.UG.cT (sigR _ σ) U.1)`.

Use function extensionality and compare the values at `i`. Rewrite using `[RingHom.map_mulVec, Formalism.UG.cT, Matrix.vecMul_transpose]`. Both sides reduce to the same expression. Rewrite using `[h3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU', Matrix.one_mulVec]`. Unfold `normInf`.

Simplify using `only`. Rewrite using `[e1, key]`.
-/
theorem normInf_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E), IsCMExt F E σ → ∀ (a : GL (Fin n) (AF F ⊗[F] E))
    (w : InfinitePlace F) (k : GArch σ J w), k ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a) →
      ∀ u : Fin n → w.Completion ⊗[F] E, normInf a w ((matHom _ σ J k).1 *ᵥ u) = normInf a w u := by
  intro F E _ _ _ _ _ σ n J hCM a w k hk u
  have hU := mem_stabArch.1 hk
  set B := Formalism.UG.bc (compInf F E w) a
  set U := B⁻¹ * matHom _ σ J k * B
  have hU' : Formalism.UG.cT (sigR _ σ) U.1 * U.1 = 1 := by
    have := hU
    change Formalism.UG.cT (sigR _ σ) U.1 * 1 * U.1 = 1 at this
    rwa [Matrix.mul_one] at this
  have e1 : (B⁻¹).1 *ᵥ ((matHom _ σ J k).1 *ᵥ u) = U.1 *ᵥ ((B⁻¹).1 *ᵥ u) := by
    simp only [U, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [← Units.val_mul B, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have key : ∀ z : Fin n → w.Completion ⊗[F] E,
      ∑ i, Algebra.norm w.Completion ((U.1 *ᵥ z) i) = ∑ i, Algebra.norm w.Completion (z i) := by
    intro z
    apply (algebraMap w.Completion (w.Completion ⊗[F] E)).injective
    simp only [map_sum, GlobalTheory.Doubling.algebraMap_norm_eq hCM]
    have h2 : ∀ y : Fin n → w.Completion ⊗[F] E, ∑ i, y i * sigR _ σ (y i) =
        (fun i => sigR _ σ (y i)) ⬝ᵥ y := fun y => by
      simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h2, h2]
    have h3 : (fun i => sigR _ σ ((U.1 *ᵥ z) i)) = (fun i => sigR _ σ (z i)) ᵥ* (Formalism.UG.cT (sigR _ σ) U.1) := by
      funext i
      rw [RingHom.map_mulVec, Formalism.UG.cT, Matrix.vecMul_transpose]
      rfl
    rw [h3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU', Matrix.one_mulVec]
  unfold normInf
  simp only
  rw [e1, key]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n hCM a w x hx`. Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Unfold `normInf`. Simplify using `only`. Use `set B' := (Formalism.UG.bc (compInf F E w) a)⁻¹`.

Use `set xw : Fin n → w.Completion ⊗[F] E := fun i => compInf F E w (adVec F x i)`. Use `pow_pos (norm_pos_iff.2 fun hs => hx ?_) _` and prove the remaining obligations. Establish `h1 : ∑ i, infEmb τ ((B'.1 *ᵥ xw) i) * starRingEnd ℂ (infEmb τ ((B'.1 *ᵥ xw) i)) = 0`. Use `congrArg (fun s => infEmb τ (algebraMap _ (w.Completion ⊗[F] E) s)) hs` as an intermediate fact. Simplify using `only [map_sum, GlobalTheory.Doubling.algebraMap_norm_eq hCM, map_mul, map_zero] at this`.

Simplify `this` using `only [infEmb_sigR hCM]`. Establish `h4 : ∑ i, Complex.normSq (infEmb τ ((B'.1 *ᵥ xw) i)) = 0`. Establish `h3 : ((∑ i, Complex.normSq (infEmb τ ((B'.1 *ᵥ xw) i)) : ℝ) : ℂ) = 0`. Simplify `h1` using `[Complex.mul_conj]`. Conclude with `h3` after adjusting the coercions.

Establish `h2 : ∀ i, infEmb τ ((B'.1 *ᵥ xw) i) = 0` using `fun i => Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1 h4 i (Finset.mem_univ _))`. Establish `h5 : (B'.1.map (infEmb τ)) *ᵥ (fun i => infEmb τ (xw i)) = 0` using `funext fun i => (RingHom.map_mulVec (infEmb τ) B'.1 xw i).symm.trans (h2 i)`. Establish `hdet : (B'.1.map (infEmb τ)).det ≠ 0`. Establish `e : (B'.1.map (infEmb τ)).det = infEmb τ B'.1.det` using `(RingHom.map_det (infEmb τ) B'.1).symm`. Rewrite using `[e]`.

Conclude with `((Matrix.isUnits_det_units B').map (infEmb τ)).ne_zero`. Establish `h6` using `Matrix.eq_zero_of_mulVec_eq_zero hdet h5`. Use function extensionality and compare the values at `i`. Establish `h7` using `congrFun h6 i`. Simplify using `[xw, adVec, compInf, inclR, infEmb_tmul] at h7`.

Conclude with `h7`.
-/
theorem normInf_adVec_pos : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ}, IsCMExt F E σ → ∀ (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F) (x : Fin n → E),
      x ≠ 0 → 0 < normInf a w (fun i => compInf F E w (adVec F x i)) := by
  intro F E _ _ _ _ _ σ n hCM a w x hx
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  unfold normInf
  simp only
  set B' := (Formalism.UG.bc (compInf F E w) a)⁻¹
  set xw : Fin n → w.Completion ⊗[F] E := fun i => compInf F E w (adVec F x i)
  refine pow_pos (norm_pos_iff.2 fun hs => hx ?_) _
  have h1 : ∑ i, infEmb τ ((B'.1 *ᵥ xw) i) * starRingEnd ℂ (infEmb τ ((B'.1 *ᵥ xw) i)) = 0 := by
    have := congrArg (fun s => infEmb τ (algebraMap _ (w.Completion ⊗[F] E) s)) hs
    simp only [map_sum, GlobalTheory.Doubling.algebraMap_norm_eq hCM, map_mul, map_zero] at this
    simpa only [infEmb_sigR hCM] using this
  have h4 : ∑ i, Complex.normSq (infEmb τ ((B'.1 *ᵥ xw) i)) = 0 := by
    have h3 : ((∑ i, Complex.normSq (infEmb τ ((B'.1 *ᵥ xw) i)) : ℝ) : ℂ) = 0 := by
      simpa [Complex.mul_conj] using h1
    exact_mod_cast h3
  have h2 : ∀ i, infEmb τ ((B'.1 *ᵥ xw) i) = 0 := fun i => Complex.normSq_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1 h4 i (Finset.mem_univ _))
  have h5 : (B'.1.map (infEmb τ)) *ᵥ (fun i => infEmb τ (xw i)) = 0 := funext fun i =>
    (RingHom.map_mulVec (infEmb τ) B'.1 xw i).symm.trans (h2 i)
  have hdet : (B'.1.map (infEmb τ)).det ≠ 0 := by
    have e : (B'.1.map (infEmb τ)).det = infEmb τ B'.1.det := (RingHom.map_det (infEmb τ) B'.1).symm
    rw [e]
    exact ((Matrix.isUnits_det_units B').map (infEmb τ)).ne_zero
  have h6 := Matrix.eq_zero_of_mulVec_eq_zero hdet h5
  funext i
  have h7 := congrFun h6 i
  simp [xw, adVec, compInf, inclR, infEmb_tmul] at h7
  exact h7

/- English proof (translation)
Establish `h1 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) t) ∈ intLoc F E v`. Rewrite using `[GlobalTheory.Doubling.algebraMap_norm_eq hCM]`. Conclude with `mul_mem ht (sigR_mem_intLoc σ ht)`. Establish `h2` using `absFin_le_one_of_mem_intLoc h1`. Rewrite `h2` using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, absFin_tmul_one]`. Then use the resulting hypothesis.
-/
theorem norm_le_one_of_mem_intLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} {t : Fv F v ⊗[F] E} (ht : t ∈ intLoc F E v) :
    ‖Algebra.norm (Fv F v) t‖₊ ≤ 1 := by
  have h1 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) t) ∈ intLoc F E v := by
    rw [GlobalTheory.Doubling.algebraMap_norm_eq hCM]
    exact mul_mem ht (sigR_mem_intLoc σ ht)
  have h2 := absFin_le_one_of_mem_intLoc h1
  rwa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, absFin_tmul_one] at h2

/- English proof (translation)
Use `pos_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Use `map_mul (absEv F E v) μ μ⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, map_one, h0, zero_mul]`. Conclude with `one_ne_zero this`.
-/
theorem absEv_pos {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (μ : (Fv F v ⊗[F] E)ˣ) : 0 < absEv F E v μ := by
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have := map_mul (absEv F E v) μ μ⁻¹
  rw [mul_inv_cancel, map_one, h0, zero_mul] at this
  exact one_ne_zero this

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y L a hCM hJ hW hA`. Use `set x := firstColumn X with hxdef`. Establish `hxy : ∑ j, ∑ i, σ (X i 0) * J i j * Y j 0 = 1`. Establish `h1` using `congrFun (congrFun hW.xy 0) 0`. Simplify `h1` using `[Matrix.mul_apply, Formalism.UG.cT, Finset.sum_mul]`.

Establish `hx0 : x ≠ 0`. Introduce `e`. Rewrite using `[Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => by`. Rewrite `hxy` using `[show X i 0 = 0 from congrFun e i, map_zero, zero_mul, zero_mul]]`. Conclude with `zero_ne_one hxy`.

Establish `hy0 : firstColumn Y ≠ 0`. Introduce `e`. Rewrite using `[Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => by`. Rewrite `hxy` using `[show Y j 0 = 0 from congrFun e j, mul_zero]]`. Conclude with `zero_ne_one hxy`.

Use `haveI := hA.lat`. Choose the witnesses or unpack the hypotheses as in `⟨d, hd, hdx⟩ : ∃ d : E, d ≠ 0 ∧ d • x ∈ L := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Set `φ : (Fin n → E) →ₗ[E] E` to `(LinearMap.proj 0).comp (Matrix.mulVecLin (Formalism.UG.cT (σ : E →+* E) Y * J))`.

Establish `hφL : ∀ z ∈ L, φ z = 0` using `fun z hz => by`. Assume the negation of the conclusion as `hne`. Establish `hmem : φ z • x ∈ L` using `(hA.split z hz 0).1`. Conclude with `hc _ hne hmem`. Establish `hφ0 : ∀ z, φ z = 0`.

Establish `h1 : Submodule.span E (L : Set (Fin n → E)) ≤ LinearMap.ker φ` using `Submodule.span_le.2 fun z hz => hφL z hz`. Rewrite `h1` using `[Submodule.IsLattice.span_eq_top]`. Conclude with `fun z => h1 trivial`. Establish `h2 : J.transpose *ᵥ (fun k => σ (Y k 0)) = 0`. Use function extensionality and compare the values at `j`.

Use `hφ0 (Pi.single j 1)` as an intermediate fact. Simplify using `only [φ, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_proj, Function.eval, Matrix.mulVec_single_one] at this`. Simplify `this` using `[Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, mul_comm]`. Establish `h3` using `Matrix.eq_zero_of_mulVec_eq_zero (by rw [Matrix.det_transpose]; exact hJ.2) h2`. Conclude with `hy0 (funext fun k => (map_eq_zero (σ : E →+* E)).1 (congrFun h3 k))`.

Choose the witnesses or unpack the hypotheses as in `⟨z, hz, hc⟩ : ∃ z ∈ L, hE σ J z x ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Set `S : Submodule E (Fin n → E)` to `{ carrier := {z | hE σ J z x = 0} add_mem' := fun {z z'} (h : hE σ J z x = 0) (h' : hE σ J z' x = 0) => by`. Express the relevant statement in the definitionally equal form `hE σ J (z + z') x = 0`.

Simplify using `only [hE, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib] at h h' ⊢`. Rewrite using `[h, h', add_zero]`. Use the proof step `zero_mem' := by change hE σ J 0 x = 0; simp [hE, Formalism.UG.hform]`. Use the proof step `smul_mem' := fun c z (h : hE σ J z x = 0) => by`. Express the relevant statement in the definitionally equal form `hE σ J (c • z) x = 0`.

Simplify using `only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul] at h ⊢`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring`.

Use `_ = 0 := by rw [h, mul_zero] }`. Establish `h1 : Submodule.span E (L : Set (Fin n → E)) ≤ S` using `Submodule.span_le.2 fun z hz => hc z hz`. Rewrite `h1` using `[Submodule.IsLattice.span_eq_top]`. Establish `h2 : J *ᵥ x = 0`. Use function extensionality and compare the values at `i`.

Establish `: hE σ J (Pi.single i 1) x = 0` using `h1 (Submodule.mem_top)`. Simplify `this` using `[hE, Formalism.UG.hform, Pi.single_apply, Matrix.mulVec, dotProduct]`. Conclude with `hx0 (Matrix.eq_zero_of_mulVec_eq_zero hJ.2 h2)`. Use `set c := hE σ J z x with hcdef`. Set `cu : Eˣ` to `Units.mk0 c hc`.

Set `du : Eˣ` to `Units.mk0 d hd`. Set `loc : ∀ v : HeightOneSpectrum (𝓞 F), Eˣ →* (Fv F v ⊗[F] E)ˣ` to `fun v => Units.map (inclR (F := F) (Fv F v)).toMonoidHom`. Set `glob : Eˣ →* (AF F ⊗[F] E)ˣ` to `Units.map (inclR (F := F) (AF F)).toMonoidHom`. Establish `hloc : ∀ v (e : Eˣ), unitFin F E v (glob e) = loc v e` using `fun v e => Units.ext (by simp [glob, loc, GlobalTheory.Doubling.unitFin, compFin, inclR])`. Establish `hxv : ∀ v, (fun i => compFin F E v (adVec F x i)) = fun i => inclR (F` using `F) (Fv F v) (x i) := fun v =>`.

Use function extensionality and compare the values at `fun i => by simp [adVec, compFin, inclR]`. Establish `hmem : ∀ v, ((((loc v du)⁻¹)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • (fun i => inclR (F` using `F) (Fv F v) (x i)) ∈ latLoc F L v := by`. Introduce `v`. Rewrite using `[inv_inv]`. Use `tmul_mem_latLoc (F := F) (v := v) (one_mem (v.adicCompletionIntegers F)) hdx` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[loc, du, inclR, Algebra.TensorProduct.tmul_mul_tmul]`. Establish `hupper : ∀ v, normFin F L v (fun i => inclR (F` using `F) (Fv F v) (x i)) * absEv F E v (loc v du) ≤ 1 := by`. Introduce `v`.

Establish `h1 : normFin F L v (fun i => inclR (F` using `F) (Fv F v) (x i)) ≤ absEv F E v (loc v du)⁻¹ := csInf_le (OrderBot.bddBelow _) ⟨_, hmem v, rfl⟩`. Rewrite `h1` using `[map_inv]`. Combine the equalities or inequalities in the displayed calculation. Establish `hlower : ∀ v, absEv F E v (loc v cu) ≤ normFin F L v (fun i => inclR (F` using `F) (Fv F v) (x i)) := by`. Introduce `v`.

Use `le_csInf ⟨_, (loc v du)⁻¹, hmem v, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, hl, rfl⟩`. Rewrite `hl` using `[hA.dual v]`. Establish `h2` using `hl (fun i => (1 : Fv F v) ⊗ₜ[F] z i) (tmul_mem_latLoc (one_mem _) hz)`. Rewrite `h2` using `[hLin_smul_left]`.

Establish `h3 : hLin σ J (Fv F v) (fun i => inclR (F` using `F) (Fv F v) (x i)) (fun i => (1 : Fv F v) ⊗ₜ[F] z i) = inclR (F := F) (Fv F v) c := by`. Simplify using `[hLin, hR, Formalism.UG.hform, JR, sigR, inclR, hcdef, hE, map_sum, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite `h2` using `[h3]`. Establish `h5 : absEv F E v (l⁻¹ * loc v cu) ≤ 1` using `norm_le_one_of_mem_intLoc hCM h2`. Rewrite `h5` using `[map_mul, map_inv]`.

Establish `hl0` using `absEv_pos v l`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hl0.ne', one_mul]`. Use `_ ≤ absEv F E v l * 1 := mul_le_mul_right h5 _`. Use `_ = _ := mul_one _`.

Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Use `((GlobalTheory.Doubling.finite_mulSupport_absEv (glob cu)).union (GlobalTheory.Doubling.finite_mulSupport_absEv (glob du))).subset ?_` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Function.mem_mulSupport, not_or, not_not, hloc] at hn`.

Apply `hv` to reduce the goal to its premises. Simplify using `only [hxv v]`. Establish `h1` using `hupper v`. Rewrite `h1` using `[hn.2, mul_one]`. Establish `h2` using `hlower v`.

Rewrite `h2` using `[hn.1]`. Conclude with `le_antisymm h1 h2`. Rewrite using `[hxv v]`. Conclude with `(absEv_pos v _).trans_le (hlower v)`.
-/
theorem normFin_first_column_finite_pos : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → GlobalTheory.EisLine.IsAdapted σ J X Y L a →
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        normFin F L v (fun i => compFin F E v (adVec F (firstColumn X) i))).Finite ∧
      ∀ v, 0 < normFin F L v (fun i => compFin F E v (adVec F (firstColumn X) i)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a hCM hJ hW hA
  set x := firstColumn X with hxdef
  have hxy : ∑ j, ∑ i, σ (X i 0) * J i j * Y j 0 = 1 := by
    have h1 := congrFun (congrFun hW.xy 0) 0
    simpa [Matrix.mul_apply, Formalism.UG.cT, Finset.sum_mul] using h1
  have hx0 : x ≠ 0 := by
    intro e
    rw [Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => by
      rw [show X i 0 = 0 from congrFun e i, map_zero, zero_mul, zero_mul]] at hxy
    exact zero_ne_one hxy
  have hy0 : firstColumn Y ≠ 0 := by
    intro e
    rw [Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => by
      rw [show Y j 0 = 0 from congrFun e j, mul_zero]] at hxy
    exact zero_ne_one hxy
  haveI := hA.lat

  obtain ⟨d, hd, hdx⟩ : ∃ d : E, d ≠ 0 ∧ d • x ∈ L := by
    by_contra hc
    push Not at hc
    let φ : (Fin n → E) →ₗ[E] E := (LinearMap.proj 0).comp (Matrix.mulVecLin (Formalism.UG.cT (σ : E →+* E) Y * J))
    have hφL : ∀ z ∈ L, φ z = 0 := fun z hz => by
      by_contra hne
      have hmem : φ z • x ∈ L := (hA.split z hz 0).1
      exact hc _ hne hmem
    have hφ0 : ∀ z, φ z = 0 := by
      have h1 : Submodule.span E (L : Set (Fin n → E)) ≤ LinearMap.ker φ := Submodule.span_le.2 fun z hz => hφL z hz
      rw [Submodule.IsLattice.span_eq_top] at h1
      exact fun z => h1 trivial
    have h2 : J.transpose *ᵥ (fun k => σ (Y k 0)) = 0 := by
      funext j
      have := hφ0 (Pi.single j 1)
      simp only [φ, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_proj,
        Function.eval, Matrix.mulVec_single_one] at this
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, mul_comm] using this
    have h3 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [Matrix.det_transpose]; exact hJ.2) h2
    exact hy0 (funext fun k => (map_eq_zero (σ : E →+* E)).1 (congrFun h3 k))

  obtain ⟨z, hz, hc⟩ : ∃ z ∈ L, hE σ J z x ≠ 0 := by
    by_contra hc
    push Not at hc
    let S : Submodule E (Fin n → E) :=
      { carrier := {z | hE σ J z x = 0}
        add_mem' := fun {z z'} (h : hE σ J z x = 0) (h' : hE σ J z' x = 0) => by
          change hE σ J (z + z') x = 0
          simp only [hE, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib] at h h' ⊢
          rw [h, h', add_zero]
        zero_mem' := by change hE σ J 0 x = 0; simp [hE, Formalism.UG.hform]
        smul_mem' := fun c z (h : hE σ J z x = 0) => by
          change hE σ J (c • z) x = 0
          simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul] at h ⊢
          calc _ = (σ : E →+* E) c * ∑ i, ∑ j, (σ : E →+* E) (z i) * J i j * x j := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun i _ => by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [h, mul_zero] }
    have h1 : Submodule.span E (L : Set (Fin n → E)) ≤ S := Submodule.span_le.2 fun z hz => hc z hz
    rw [Submodule.IsLattice.span_eq_top] at h1
    have h2 : J *ᵥ x = 0 := by
      funext i
      have : hE σ J (Pi.single i 1) x = 0 := h1 (Submodule.mem_top)
      simpa [hE, Formalism.UG.hform, Pi.single_apply, Matrix.mulVec, dotProduct] using this
    exact hx0 (Matrix.eq_zero_of_mulVec_eq_zero hJ.2 h2)
  set c := hE σ J z x with hcdef
  let cu : Eˣ := Units.mk0 c hc
  let du : Eˣ := Units.mk0 d hd
  let loc : ∀ v : HeightOneSpectrum (𝓞 F), Eˣ →* (Fv F v ⊗[F] E)ˣ := fun v =>
    Units.map (inclR (F := F) (Fv F v)).toMonoidHom
  let glob : Eˣ →* (AF F ⊗[F] E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom
  have hloc : ∀ v (e : Eˣ), unitFin F E v (glob e) = loc v e := fun v e =>
    Units.ext (by simp [glob, loc, GlobalTheory.Doubling.unitFin, compFin, inclR])
  have hxv : ∀ v, (fun i => compFin F E v (adVec F x i)) = fun i => inclR (F := F) (Fv F v) (x i) := fun v =>
    funext fun i => by simp [adVec, compFin, inclR]
  have hmem : ∀ v, ((((loc v du)⁻¹)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) •
      (fun i => inclR (F := F) (Fv F v) (x i)) ∈ latLoc F L v := by
    intro v
    rw [inv_inv]
    have := tmul_mem_latLoc (F := F) (v := v) (one_mem (v.adicCompletionIntegers F)) hdx
    convert this using 1
    funext i
    simp [loc, du, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  have hupper : ∀ v, normFin F L v (fun i => inclR (F := F) (Fv F v) (x i)) * absEv F E v (loc v du) ≤ 1 := by
    intro v
    have h1 : normFin F L v (fun i => inclR (F := F) (Fv F v) (x i)) ≤ absEv F E v (loc v du)⁻¹ :=
      csInf_le (OrderBot.bddBelow _) ⟨_, hmem v, rfl⟩
    rw [map_inv] at h1
    calc _ ≤ (absEv F E v (loc v du))⁻¹ * absEv F E v (loc v du) := mul_le_mul_left h1 _
      _ = 1 := inv_mul_cancel₀ (absEv_pos v _).ne'
  have hlower : ∀ v, absEv F E v (loc v cu) ≤ normFin F L v (fun i => inclR (F := F) (Fv F v) (x i)) := by
    intro v
    refine le_csInf ⟨_, (loc v du)⁻¹, hmem v, rfl⟩ ?_
    rintro _ ⟨l, hl, rfl⟩
    rw [hA.dual v] at hl
    have h2 := hl (fun i => (1 : Fv F v) ⊗ₜ[F] z i) (tmul_mem_latLoc (one_mem _) hz)
    rw [hLin_smul_left] at h2
    have h3 : hLin σ J (Fv F v) (fun i => inclR (F := F) (Fv F v) (x i)) (fun i => (1 : Fv F v) ⊗ₜ[F] z i) =
        inclR (F := F) (Fv F v) c := by
      simp [hLin, hR, Formalism.UG.hform, JR, sigR, inclR, hcdef, hE, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
    rw [h3] at h2
    have h5 : absEv F E v (l⁻¹ * loc v cu) ≤ 1 := norm_le_one_of_mem_intLoc hCM h2
    rw [map_mul, map_inv] at h5
    have hl0 := absEv_pos v l
    calc absEv F E v (loc v cu) = absEv F E v l * ((absEv F E v l)⁻¹ * absEv F E v (loc v cu)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hl0.ne', one_mul]
      _ ≤ absEv F E v l * 1 := mul_le_mul_right h5 _
      _ = _ := mul_one _
  refine ⟨?_, fun v => ?_⟩
  · refine ((GlobalTheory.Doubling.finite_mulSupport_absEv (glob cu)).union
      (GlobalTheory.Doubling.finite_mulSupport_absEv (glob du))).subset ?_
    intro v hv
    by_contra hn
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not, hloc] at hn
    apply hv
    simp only [hxv v]
    have h1 := hupper v
    rw [hn.2, mul_one] at h1
    have h2 := hlower v
    rw [hn.1] at h2
    exact le_antisymm h1 h2
  · rw [hxv v]
    exact (absEv_pos v _).trans_le (hlower v)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y L a h hS`. Take `⟨hCM, -, hJ, -, hW, hA, hI⟩` from `hS`. Establish `hx0 : firstColumn X ≠ 0`. Introduce `e`. Establish `h1` using `congrFun (congrFun hW.xy 0) 0`.

Establish `h2 : (Formalism.UG.cT (σ : E →+* E) X * J * Y) 0 0 = 0`. Simplify using `only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_zero fun i _ => by rw [show X i 0 = 0 from congrFun e i, map_zero, zero_mul], zero_mul]`. Rewrite `h1` using `[h2]`.

Simplify using `at h1`. Take `⟨hfin, hpos⟩` from `normFin_first_column_finite_pos σ J X Y L a hCM hJ hW hA`. Use `set u := adVec F (firstColumn X) with hu`. Establish `hfinR : (Function.mulSupport fun v => (normFin F L v (fun i => compFin F E v (u i)) : ℝ)).Finite` using `hfin.subset (fun v hv => fun e => hv (by simp [e]))`. Use `⟨mul_pos ?_ (Finset.prod_pos fun w _ => normInf_adVec_pos σ hCM a w _ hx0), fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[finprod_eq_prod _ hfinR]`. Conclude with `Finset.prod_pos fun v _ => by exact_mod_cast hpos v`. Take `⟨p, l, hpl, k, hk, rfl⟩` from `hI.1 g`. Rewrite using `[hI.2 p l hpl k hk]`. Establish `hpv : (matHom _ σ J p).1 *ᵥ u = l.1 • u`.

Use function extensionality and compare the values at `i`. Use `congrFun (congrFun hpl i) 0` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, hu, adVec, firstColumn, col0]`. Establish `hpinv : (matHom _ σ J p⁻¹).1 *ᵥ u = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u`. Establish `e1 : (matHom _ σ J p⁻¹).1 *ᵥ ((matHom _ σ J p).1 *ᵥ u) = u`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]`. Rewrite `e1` using `[hpv, Matrix.mulVec_smul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, Units.inv_mul, one_smul]`. Use `_ = _ := by rw [e1]`.

Establish `hg : (matHom _ σ J (p * k)⁻¹).1 *ᵥ u = (matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)`. Rewrite using `[mul_inv_rev, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hpinv]`. Rewrite using `[hg]`. Establish `hk'` using `mem_levelAll.1 (inv_mem hk)`. Establish `hfv : ∀ v, normFin F L v (fun i => compFin F E v (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) = absEv F E v (unitFin F E v l⁻¹) * normFin F L v (fun i => compFin F E v (u i))`.

Introduce `v`. Establish `e : (fun i => compFin F E v (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) = (matHom _ σ J (proj σ J v k⁻¹)).1 *ᵥ ((unitFin F E v l⁻¹ : Fv F v ⊗[F] E) • fun i => compFin F E v (u i))`. Use function extensionality and compare the values at `i`. Rewrite using `[RingHom.map_mulVec, matHom_proj]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using `[GlobalTheory.Doubling.unitFin]`. Rewrite using `[e, normFin_stab σ J L v _ (hk'.1 v), normFin_unit_smul]`. Establish `hiw : ∀ w, normInf a w (fun i => compInf F E w (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) = absEw F E w (unitInf F E w l⁻¹) * normInf a w (fun i => compInf F E w (u i))`. Introduce `w`.

Establish `e : (fun i => compInf F E w (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) = (matHom _ σ J (projArch σ J w k⁻¹)).1 *ᵥ ((unitInf F E w l⁻¹ : w.Completion ⊗[F] E) • fun i => compInf F E w (u i))`. Use function extensionality and compare the values at `i`. Rewrite using `[RingHom.map_mulVec, matHom_projArch]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Simplify using `[GlobalTheory.Doubling.unitInf]`. Rewrite using `[e, normInf_stab σ J hCM a w _ (hk'.2 w), normInf_unit_smul]`. Unfold `ht`. Simplify using `only [hfv, hiw, NNReal.coe_mul]`. Establish `hA1 : (Function.mulSupport fun v => ((absEv F E v (unitFin F E v l⁻¹) : ℝ≥0) : ℝ)).Finite` using `(GlobalTheory.Doubling.finite_mulSupport_absEv l⁻¹).subset (fun v hv => by`.

Simplify using `only [Function.mem_mulSupport, ne_eq, NNReal.coe_eq_one] at hv ⊢`. Conclude with `hv)`. Rewrite using `[finprod_mul_distrib hA1 hfinR, Finset.prod_mul_distrib]`. Establish `hl : (absE F E l : ℝ) * ((∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) * ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ)) = 1`. Establish `h1 : (absE F E l : ℝ) * (absE F E l⁻¹ : ℝ) = 1`.

Rewrite using `[← NNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, NNReal.coe_one]`. Establish `h2` using `NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv l⁻¹)`. Establish `e2 : (absE F E l⁻¹ : ℝ) = (∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) * ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ)`. Rewrite using `[GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]`. Use `congr 1`.

Rewrite using `[← e2]`. Conclude with `h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ht_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
      0 < GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ∧
      ∀ g : GAd σ J, h g * GlobalTheory.EisMidHt.ht L a ((matHom _ σ J g⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) =
        GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hCM, -, hJ, -, hW, hA, hI⟩ := hS
  have hx0 : firstColumn X ≠ 0 := by
    intro e
    have h1 := congrFun (congrFun hW.xy 0) 0
    have h2 : (Formalism.UG.cT (σ : E →+* E) X * J * Y) 0 0 = 0 := by
      simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Finset.sum_eq_zero fun i _ => by rw [show X i 0 = 0 from congrFun e i, map_zero, zero_mul], zero_mul]
    rw [h2] at h1
    simp at h1
  obtain ⟨hfin, hpos⟩ := normFin_first_column_finite_pos σ J X Y L a hCM hJ hW hA
  set u := adVec F (firstColumn X) with hu
  have hfinR : (Function.mulSupport fun v => (normFin F L v (fun i => compFin F E v (u i)) : ℝ)).Finite :=
    hfin.subset (fun v hv => fun e => hv (by simp [e]))
  refine ⟨mul_pos ?_ (Finset.prod_pos fun w _ => normInf_adVec_pos σ hCM a w _ hx0), fun g => ?_⟩
  · rw [finprod_eq_prod _ hfinR]
    exact Finset.prod_pos fun v _ => by exact_mod_cast hpos v
  · obtain ⟨p, l, hpl, k, hk, rfl⟩ := hI.1 g
    rw [hI.2 p l hpl k hk]
    have hpv : (matHom _ σ J p).1 *ᵥ u = l.1 • u := by
      funext i
      have := congrFun (congrFun hpl i) 0
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hu, adVec, firstColumn, col0] using this
    have hpinv : (matHom _ σ J p⁻¹).1 *ᵥ u = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u := by
      have e1 : (matHom _ σ J p⁻¹).1 *ᵥ ((matHom _ σ J p).1 *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
          Matrix.one_mulVec]
      rw [hpv, Matrix.mulVec_smul] at e1
      calc _ = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • (l.1 • (matHom _ σ J p⁻¹).1 *ᵥ u) := by
            rw [smul_smul, Units.inv_mul, one_smul]
        _ = _ := by rw [e1]
    have hg : (matHom _ σ J (p * k)⁻¹).1 *ᵥ u = (matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u) := by
      rw [mul_inv_rev, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hpinv]
    rw [hg]
    have hk' := mem_levelAll.1 (inv_mem hk)
    have hfv : ∀ v, normFin F L v (fun i => compFin F E v (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
        absEv F E v (unitFin F E v l⁻¹) * normFin F L v (fun i => compFin F E v (u i)) := by
      intro v
      have e : (fun i => compFin F E v (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
          (matHom _ σ J (proj σ J v k⁻¹)).1 *ᵥ ((unitFin F E v l⁻¹ : Fv F v ⊗[F] E) • fun i => compFin F E v (u i)) := by
        funext i
        rw [RingHom.map_mulVec, matHom_proj]
        congr 1
        funext j
        simp [GlobalTheory.Doubling.unitFin]
      rw [e, normFin_stab σ J L v _ (hk'.1 v), normFin_unit_smul]
    have hiw : ∀ w, normInf a w (fun i => compInf F E w (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
        absEw F E w (unitInf F E w l⁻¹) * normInf a w (fun i => compInf F E w (u i)) := by
      intro w
      have e : (fun i => compInf F E w (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
          (matHom _ σ J (projArch σ J w k⁻¹)).1 *ᵥ ((unitInf F E w l⁻¹ : w.Completion ⊗[F] E) • fun i => compInf F E w (u i)) := by
        funext i
        rw [RingHom.map_mulVec, matHom_projArch]
        congr 1
        funext j
        simp [GlobalTheory.Doubling.unitInf]
      rw [e, normInf_stab σ J hCM a w _ (hk'.2 w), normInf_unit_smul]
    unfold ht
    simp only [hfv, hiw, NNReal.coe_mul]
    have hA1 : (Function.mulSupport fun v => ((absEv F E v (unitFin F E v l⁻¹) : ℝ≥0) : ℝ)).Finite :=
      (GlobalTheory.Doubling.finite_mulSupport_absEv l⁻¹).subset (fun v hv => by
        simp only [Function.mem_mulSupport, ne_eq, NNReal.coe_eq_one] at hv ⊢; exact hv)
    rw [finprod_mul_distrib hA1 hfinR, Finset.prod_mul_distrib]
    have hl : (absE F E l : ℝ) * ((∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) *
        ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ)) = 1 := by
      have h1 : (absE F E l : ℝ) * (absE F E l⁻¹ : ℝ) = 1 := by
        rw [← NNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, NNReal.coe_one]
      have h2 := NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv l⁻¹)
      have e2 : (absE F E l⁻¹ : ℝ) = (∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) *
          ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ) := by
        rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
        congr 1
      rw [← e2]
      exact h1
    calc _ = ((absE F E l : ℝ) * ((∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) *
          ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ))) *
          ((∏ᶠ v, (normFin F L v (fun i => compFin F E v (u i)) : ℝ)) *
            ∏ w, normInf a w (fun i => compInf F E w (u i))) := by ring
      _ = _ := by rw [hl, one_mul]
end GlobalTheory.EisMidHt

end

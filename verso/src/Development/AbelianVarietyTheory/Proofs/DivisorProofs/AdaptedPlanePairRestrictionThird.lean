import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicGLMulVecHaarEqModulusDetStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblSiegelX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Unfold `actB zs`. Rewrite using `[Matrix.vecMulVec_mul, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]`. Use `congr 1`. Use `congrArg (· *ᵥ v) hpt using 1` and compare the differences between its conclusion and the goal. Use `congr 1`.

Simplify using `only [Matrix.mulVec_mulVec]`. Use `congr 1`.
-/
theorem actB_zs {n n₁ d : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)} (H : Plane E n n₁)
    (p : UG (cA σ) J) (t : GL (Fin d) (AE F E))
    (hpt : (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin d) = diagCols (Fin d) * t.1) (v : Fin d → AE F E) :
    actB (cA σ) p (zs H v) = zs H ((t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ v) := by
  unfold actB zs
  rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
  congr 1
  convert congrArg (· *ᵥ v) hpt using 1
  · congr 1
  · simp only [Matrix.mulVec_mulVec]
    congr 1

/- English proof (translation)
Introduce `hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne dd dd₁ hdd hdd₁ omd omd₁ homd homd₁ ed hmap hheis hinv hadm hnz p t hpt a ha`. Take `⟨μ, hμ, l₁, hl₁, hl₁inv, Φ₀, hΦ₀, hLΦ₀⟩` from `GlobalTheory.T.adapted_plane_pair_vacuum hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne dd dd₁ hdd hdd₁ ed hmap hheis hinv hadm hnz`. Take `⟨hint, hLadm⟩` from `GlobalTheory.T.adapted_plane_pair_restriction_alt hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne dd dd₁ hdd hdd₁ ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁inv μ hμ`. Establish `hLinv` using `GlobalTheory.T.adapted_plane_pair_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne dd dd₁ hdd hdd₁ ed hmap hheis hinv hadm hnz l₁ hl₁inv μ hμ hint`. Use `set L := avgL dd B.ψ (zs H) (l₁ ∘ₗ ed) μ with hL`.

Establish `hS` using `homd.2.2 L hLadm hLinv p t hpt Φ₀ hΦ₀`. Establish `hstd` using `hP.base.std`. Establish `hpres : ∀ w, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), dd.rho B.ψ w Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d)` using `fun w Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd (dd.e w) Φ hΦ`. Take `⟨m, hm⟩ : ∃ m : ℝ, m = (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ)` from `⟨_, rfl⟩`. Take `⟨m', hm'⟩ : ∃ m' : ℝ, m' = (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t⁻¹)) : ℝ)` from `⟨_, rfl⟩`.

Establish `hmm : m * m' = 1`. Rewrite using `[hm, hm', ← NNReal.coe_mul, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one, NNReal.coe_one]`. Establish `hm0 : 0 < m`. Break down `(show (0:ℝ) ≤ m from hm ▸ NNReal.coe_nonneg _).lt_or_eq with h | h` into its components or cases. Conclude with `h`.

Rewrite `hmm` using `[← h, zero_mul]`. Conclude with `absurd hmm zero_ne_one`. Establish `hS₁` using `homd₁.2.2 l₁ hl₁ hl₁inv p t hpt`. Simplify using `only [adeleClass] at hS₁`. Rewrite `hS₁` using `[← hm]`.

Use `set c₁ : ℂ := (χX (Matrix.GeneralLinearGroup.det t) : ℂ) * (((m ^ ((Fintype.card (Fin n₁) : ℝ) / 2) : ℝ)) : ℂ) with hc₁`. Establish `hpt' : ∀ u : Fin d → AE F E, actB (cA σ) p (zs H (((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _) *ᵥ u)) = zs H u`. Introduce `u`. Rewrite using `[actB_zs H p t hpt, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hfun : avgFun dd B.ψ (zs H) (l₁ ∘ₗ ed) (omd p Φ₀) = fun u => (a * c₁) * avgFun dd B.ψ (zs H) (l₁ ∘ₗ ed) Φ₀ (((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _) *ᵥ u)`.

Use function extensionality and compare the values at `u`. Establish `hΨ` using `hpres (zs H (((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _) *ᵥ u)) Φ₀ hΦ₀`. Simplify using `only [avgFun, LinearMap.comp_apply]`. Rewrite using `[← hpt' u, ← homd.2.1.impl p _ Φ₀ hΦ₀, ha _ hΨ, map_smul, hS₁ _ (hmap _ hΨ), smul_eq_mul, hc₁]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcalc : L (omd p Φ₀) = a * c₁ * (m : ℂ) * L Φ₀`. Rewrite using `[hL, avgL_apply _ _ _ _ _ _ (hint _ (homd.2.1.pres p Φ₀ hΦ₀)), avgL_apply _ _ _ _ _ _ (hint _ hΦ₀), hfun, integral_const_mul, GlobalTheory.T.integral_adelicGL_mulVec_haar_eq_modulus_det F E d t⁻¹ μ hμ]`. Establish `: m'⁻¹ = m` using `(eq_inv_of_mul_eq_one_left hmm).symm`. Rewrite using `[← hm', this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hS` using `[hcalc]`. Establish `hcard : ((Fintype.card (Fin n) : ℝ) / 2) = ((Fintype.card (Fin n₁) : ℝ) / 2) + 1`. Simplify using `only [Fintype.card_fin, hH.rank]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hpow : (m ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) = m ^ ((Fintype.card (Fin n₁) : ℝ) / 2) * m`. Rewrite using `[hcard, Real.rpow_add hm0, Real.rpow_one]`. Simplify using `only [adeleClass] at hS`. Rewrite `hS` using `[← hm, hpow]`. Establish `hχ : (χX (Matrix.GeneralLinearGroup.det t) : ℂ) ≠ 0` using `Circle.coe_ne_zero _`.

Establish `hp0 : ((m ^ ((Fintype.card (Fin n₁) : ℝ) / 2) : ℝ) : ℂ) ≠ 0`. Conclude with `(Real.rpow_pos_of_pos hm0 _).ne'` after adjusting the coercions. Establish `hm0' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm0.ne'`. Rewrite `hS` using `[hc₁]`. Move the coercions through the operations in `at hS`.

Establish `key : (a - 1) * ((χX (Matrix.GeneralLinearGroup.det t) : ℂ) * ((m ^ ((Fintype.card (Fin n₁) : ℝ) / 2) : ℝ) : ℂ) * m * L Φ₀) = 0`. Take the linear combination `hS`. Establish `hne : (χX (Matrix.GeneralLinearGroup.det t) : ℂ) * ((m ^ ((Fintype.card (Fin n₁) : ℝ) / 2) : ℝ) : ℂ) * m * L Φ₀ ≠ 0`. Use `mul_ne_zero (mul_ne_zero (mul_ne_zero hχ hp0) hm0') ?_` and prove the remaining obligations. Rewrite using `[hL, avgL_apply _ _ _ _ _ _ (hint _ hΦ₀)]`.

Conclude with `hLΦ₀`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)`.
-/
theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (cA σ) (-1) (incM F X₁.J) (dbl (incM F W.J))) (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X₁.J) (incM F W.J) M₁.co dd₁ →
      ∀ (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)) (omd₁ : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ)),
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X₁.J) (dbl (incM F W.J)) dd₁ χX (diagCols (Fin d)) omd₁ →
      ∀ ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)) →
        (∀ (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (incM F H.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ z : Fin d ⊕ Fin d → AE F E, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l ∘ₗ ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ≠ 0) →
      ∀ (p : UG (cA σ) (dbl (incM F W.J))) (t : GL (Fin d) (AE F E)),
        (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin d) = diagCols (Fin d) * t.1 →
      ∀ a : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (omd p Φ) = a • omd₁ p (ed Φ)) → a = 1 := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne dd dd₁ hdd hdd₁
    omd omd₁ homd homd₁ ed hmap hheis hinv hadm hnz p t hpt a ha
  obtain ⟨μ, hμ, l₁, hl₁, hl₁inv, Φ₀, hΦ₀, hLΦ₀⟩ := GlobalTheory.T.adapted_plane_pair_vacuum hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁
    r₁ s₁ hH hP₁ e he hne dd dd₁ hdd hdd₁ ed hmap hheis hinv hadm hnz
  obtain ⟨hint, hLadm⟩ := GlobalTheory.T.adapted_plane_pair_restriction_alt hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁
    r₁ s₁ hH hP₁ e he hne dd dd₁ hdd hdd₁ ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁inv μ hμ
  have hLinv := GlobalTheory.T.adapted_plane_pair_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁
    r₁ s₁ hH hP₁ e he hne dd dd₁ hdd hdd₁ ed hmap hheis hinv hadm hnz l₁ hl₁inv μ hμ hint
  set L := avgL dd B.ψ (zs H) (l₁ ∘ₗ ed) μ with hL
  have hS := homd.2.2 L hLadm hLinv p t hpt Φ₀ hΦ₀
  have hstd := hP.base.std
  have hpres : ∀ w, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), dd.rho B.ψ w Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
    fun w Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd (dd.e w) Φ hΦ
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) := ⟨_, rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m' : ℝ, m' = (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t⁻¹)) : ℝ) := ⟨_, rfl⟩
  have hmm : m * m' = 1 := by
    rw [hm, hm', ← NNReal.coe_mul, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one, NNReal.coe_one]
  have hm0 : 0 < m := by
    rcases (show (0:ℝ) ≤ m from hm ▸ NNReal.coe_nonneg _).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hmm; exact absurd hmm zero_ne_one
  have hS₁ := homd₁.2.2 l₁ hl₁ hl₁inv p t hpt
  simp only [adeleClass] at hS₁
  rw [← hm] at hS₁
  set c₁ : ℂ := (χX (Matrix.GeneralLinearGroup.det t) : ℂ) * (((m ^ ((Fintype.card (Fin n₁) : ℝ) / 2) : ℝ)) : ℂ) with hc₁
  have hpt' : ∀ u : Fin d → AE F E, actB (cA σ) p (zs H (((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _) *ᵥ u)) = zs H u := by
    intro u
    rw [actB_zs H p t hpt, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hfun : avgFun dd B.ψ (zs H) (l₁ ∘ₗ ed) (omd p Φ₀) =
      fun u => (a * c₁) * avgFun dd B.ψ (zs H) (l₁ ∘ₗ ed) Φ₀ (((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _) *ᵥ u) := by
    funext u
    have hΨ := hpres (zs H (((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _) *ᵥ u)) Φ₀ hΦ₀
    simp only [avgFun, LinearMap.comp_apply]
    rw [← hpt' u, ← homd.2.1.impl p _ Φ₀ hΦ₀, ha _ hΨ, map_smul, hS₁ _ (hmap _ hΨ), smul_eq_mul, hc₁]
    ring
  have hcalc : L (omd p Φ₀) = a * c₁ * (m : ℂ) * L Φ₀ := by
    rw [hL, avgL_apply _ _ _ _ _ _ (hint _ (homd.2.1.pres p Φ₀ hΦ₀)), avgL_apply _ _ _ _ _ _ (hint _ hΦ₀), hfun,
      integral_const_mul, GlobalTheory.T.integral_adelicGL_mulVec_haar_eq_modulus_det F E d t⁻¹ μ hμ]
    have : m'⁻¹ = m := (eq_inv_of_mul_eq_one_left hmm).symm
    rw [← hm', this]
    ring
  rw [hcalc] at hS
  have hcard : ((Fintype.card (Fin n) : ℝ) / 2) = ((Fintype.card (Fin n₁) : ℝ) / 2) + 1 := by
    simp only [Fintype.card_fin, hH.rank]; push_cast; ring
  have hpow : (m ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) = m ^ ((Fintype.card (Fin n₁) : ℝ) / 2) * m := by
    rw [hcard, Real.rpow_add hm0, Real.rpow_one]
  simp only [adeleClass] at hS
  rw [← hm, hpow] at hS
  have hχ : (χX (Matrix.GeneralLinearGroup.det t) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hp0 : ((m ^ ((Fintype.card (Fin n₁) : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hm0 _).ne'
  have hm0' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  rw [hc₁] at hS
  push_cast at hS
  have key : (a - 1) * ((χX (Matrix.GeneralLinearGroup.det t) : ℂ) * ((m ^ ((Fintype.card (Fin n₁) : ℝ) / 2) : ℝ) : ℂ) * m * L Φ₀) = 0 := by
    linear_combination hS
  have hne : (χX (Matrix.GeneralLinearGroup.det t) : ℂ) * ((m ^ ((Fintype.card (Fin n₁) : ℝ) / 2) : ℝ) : ℂ) * m * L Φ₀ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hχ hp0) hm0') ?_
    rw [hL, avgL_apply _ _ _ _ _ _ (hint _ hΦ₀)]; exact hLΦ₀
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)

end GlobalTheory.DblSiegelX

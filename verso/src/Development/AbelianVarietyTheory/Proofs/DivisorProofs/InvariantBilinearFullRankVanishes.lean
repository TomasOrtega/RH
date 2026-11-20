import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHaarMatrixSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantFormZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankPartialIntegrationProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureAdditiveAutomorphismScaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankExtensionIntegralExistsStatement
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory

noncomputable section
namespace GlobalTheory.FibreVanish
open GlobalTheory.SplitFlip Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev jn {ρ e d : ℕ} (Y₁ : Matrix (Fin ρ) (Fin d) k) (Y₂ : Matrix (Fin e) (Fin d) k) : Matrix (Fin (ρ + e)) (Fin d) k :=
  (fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id

/- English proof (translation)
Use extensionality with `i j`. Take `⟨i, rfl⟩` from `finSumFinEquiv.surjective i`. Apply the tactic sequence `rcases i with i | i <;> simp [jn, Matrix.mul_apply]`.
-/
theorem jn_mul {ρ e d : ℕ} (Y₁ : Matrix (Fin ρ) (Fin d) k) (Y₂ : Matrix (Fin e) (Fin d) k) (M : Matrix (Fin d) (Fin d) k) :
    jn Y₁ Y₂ * M = jn (Y₁ * M) (Y₂ * M) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i <;> simp [jn, Matrix.mul_apply]

/- English proof (translation)
Use `⟨?_, fun Y hY => hΘ.2 _ ?_⟩` and prove the remaining obligations. Use `show _ ∈ GlobalTheory.SplitWeil.SB _`. Simplify using `using comp_mul_mem_SB (1 : GL (Fin n) k) h hΘ.1`. Rewrite using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by simpa using h.isUnit.map Matrix.detMonoidHom)]` and apply the resulting hypothesis.
-/
theorem comp_mul_mem_fullRk {n d : ℕ} (h : GL (Fin d) k) {Θ : Matrix (Fin n) (Fin d) k → ℂ} (hΘ : Θ ∈ fullRk k n d) :
    (fun Y => Θ (Y * h.1)) ∈ fullRk k n d := by
  refine ⟨?_, fun Y hY => hΘ.2 _ ?_⟩
  · show _ ∈ GlobalTheory.SplitWeil.SB _
    simpa using comp_mul_mem_SB (1 : GL (Fin n) k) h hΘ.1
  · rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by simpa using h.isUnit.map Matrix.detMonoidHom)]

/- English proof (translation)
Use `⟨?_, fun Y hY => ?_⟩` and prove the remaining obligations. Use `(SB (Matrix (Fin n) (Fin d) k)).smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) (comp_mul_mem_SB (invT g)⁻¹ (1 : GL (Fin d) k) hΘ.1)` as an intermediate fact. Simplify using `only [invT_inv_val, Units.val_one, Matrix.mul_one] at this`. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `Y`.

Simplify using `[lact, mul_assoc]`. Simplify using `only [lact]`. Rewrite using `[hΘ.2 _ ?_, mul_zero]`. Rewrite using `[Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by simpa using (g.isUnit.map Matrix.detMonoidHom))]` and apply the resulting hypothesis.
-/
theorem lact_mem_fullRk {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) {Θ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΘ : Θ ∈ fullRk k n d) : lact ν g Θ ∈ fullRk k n d := by
  refine ⟨?_, fun Y hY => ?_⟩
  · have := (SB (Matrix (Fin n) (Fin d) k)).smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2))
      (comp_mul_mem_SB (invT g)⁻¹ (1 : GL (Fin d) k) hΘ.1)
    simp only [invT_inv_val, Units.val_one, Matrix.mul_one] at this
    convert this using 1
    funext Y
    simp [lact, mul_assoc]
  · simp only [lact]
    rw [hΘ.2 _ ?_, mul_zero]
    rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by simpa using (g.isUnit.map Matrix.detMonoidHom))]

/- English proof (translation)
The claim follows from `GlobalTheory.T.full_rank_partial_integration_projection`.
-/
theorem fibreA : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ρ e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure],
    ∃ P : fullRk k (ρ + e) d →ₗ[ℂ] fullRk k ρ d, ∀ (Θ : fullRk k (ρ + e) d) (Y₁ : Matrix (Fin ρ) (Fin d) k),
      (P Θ).1 Y₁ = ∫ Y₂, Θ.1 ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) ∂μ := GlobalTheory.T.full_rank_partial_integration_projection

/- English proof (translation)
The claim follows from `GlobalTheory.T.haar_measure_additive_automorphism_scale`.
-/
theorem scaleB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure]
    (L : Matrix (Fin e) (Fin d) k ≃+ Matrix (Fin e) (Fin d) k), Continuous L → Continuous L.symm →
    ∃ c : ℝ, 0 < c ∧ ∀ f : Matrix (Fin e) (Fin d) k → ℂ, ∫ x, f (L x) ∂μ = (c : ℂ) * ∫ x, f x ∂μ := GlobalTheory.T.haar_measure_additive_automorphism_scale

/- English proof (translation)
The claim follows from `GlobalTheory.T.full_rank_extension_integral_exists`.
-/
theorem ontoC : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ρ e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure], ρ + e ≤ d →
    ∀ θ ∈ fullRk k ρ d, ∃ Θ ∈ fullRk k (ρ + e) d, ∀ Y₁ : Matrix (Fin ρ) (Fin d) k,
      ∫ Y₂, Θ ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) ∂μ = θ Y₁ := GlobalTheory.T.full_rank_extension_integral_exists

def dilN (ρ e : ℕ) (t : kˣ) : GL (Fin (ρ + e)) k :=
  Units.map (Matrix.reindexAlgEquiv k k finSumFinEquiv).toMonoidHom (GlobalTheory.RankChart.dilGL t)

/- English proof (translation)
Establish `h1 : (dilN ρ e t).valᵀ = ((GlobalTheory.RankChart.dilGL t : GL (Fin ρ ⊕ Fin e) k).valᵀ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`. Simplify using `[dilN, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.transpose_submatrix]`. Rewrite using `[h1, jn, ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, GlobalTheory.RankChart.dilGL_transpose_mul]`. Simplify using `[GlobalTheory.RankChart.dil, jn]`.
-/
theorem dilN_transpose_mul {ρ e d : ℕ} (t : kˣ) (Y₁ : Matrix (Fin ρ) (Fin d) k) (Y₂ : Matrix (Fin e) (Fin d) k) :
    (dilN ρ e t).valᵀ * jn Y₁ Y₂ = jn Y₁ ((t : k) • Y₂) := by
  have h1 : (dilN ρ e t).valᵀ = ((GlobalTheory.RankChart.dilGL t : GL (Fin ρ ⊕ Fin e) k).valᵀ).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm := by
    simp [dilN, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.transpose_submatrix]
  rw [h1, jn, ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, GlobalTheory.RankChart.dilGL_transpose_mul]
  simp [GlobalTheory.RankChart.dil, jn]

/- English proof (translation)
Use `GlobalTheory.RankChart.gdet_dilGL (R := Fin ρ) (T := Fin e) t` as an intermediate fact. Use `ext`. Simplify using `only [gdet, Matrix.GeneralLinearGroup.val_det_apply] at this ⊢`. Rewrite using `[dilN]`. Simplify using `[Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self]`.

Simplify using `using congrArg Units.val this`.
-/
theorem gdet_dilN (ρ e : ℕ) (t : kˣ) : gdet (dilN ρ e t) = t ^ e := by
  have := GlobalTheory.RankChart.gdet_dilGL (R := Fin ρ) (T := Fin e) t
  ext
  simp only [gdet, Matrix.GeneralLinearGroup.val_det_apply] at this ⊢
  rw [dilN]
  simp [Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self]
  simpa using congrArg Units.val this

/- English proof (translation)
Use `letI : MeasurableSpace (Matrix (Fin e) (Fin d) k) := borel _`. Use `haveI : BorelSpace (Matrix (Fin e) (Fin d) k) := ⟨rfl⟩`. Take `⟨μ, hμ⟩` from `@GlobalTheory.haar_exists_matrix_local_field k _ _ _ _ e d`. Take `⟨P, hP⟩` from `fibreA k ρ e d μ`. Establish `hPh : ∀ h : GL (Fin d) k, ∃ c : ℝ, 0 < c ∧ ∀ Θ Θ' : fullRk k (ρ + e) d, Θ'.1 = (fun Y => Θ.1 (Y * h.1)) → (P Θ').1 = fun Y₁ => (c : ℂ) * (P Θ).1 (Y₁ * h.1)`.

Introduce `h`. Set `L : Matrix (Fin e) (Fin d) k ≃+ Matrix (Fin e) (Fin d) k` to `{ toFun := fun Y => Y * h.1, invFun := fun Y => Y * (h⁻¹).1, left_inv := fun Y => by simp [Matrix.mul_assoc], right_inv := fun Y => by simp [Matrix.mul_assoc], map_add' := fun Y Z => Matrix.add_mul _ _ _ }`. Take `⟨c, hc, hcf⟩` from `scaleB k e d μ L (continuous_id.matrix_mul continuous_const) (continuous_id.matrix_mul continuous_const)`. Use `⟨c, hc, fun Θ Θ' hΘ' => funext fun Y₁ => ?_⟩` and prove the remaining obligations. Rewrite using `[hP, hP, hΘ']`.

Use `show ∫ Y₂, Θ.1 (jn Y₁ Y₂ * h.1) ∂μ = _`. Simplify using `only [jn_mul]`. Conclude with `hcf (fun Y₂ => Θ.1 (jn (Y₁ * h.1) Y₂))`. Set `D : fullRk k (ρ + e) d →ₗ[ℂ] fullRk k (ρ + e) d →ₗ⋆[ℂ] ℂ` to `Bf.compl₂ P`. Establish `hD : ∀ Ψ₁ Θ, D Ψ₁ Θ = Bf Ψ₁ (P Θ)` using `fun _ _ => rfl`.

Establish `hν : ν ≠ 1`. Introduce and unpack `rfl`. Conclude with `hr 1 one_pos 1 (by simp)`. Establish `key` using `GlobalTheory.T.full_rank_coinvariant_form_zero hKP k (ρ + e) d ν hd hs hu hν D (fun g Ψ₁ Ψ₁' Ψ₂ hg => by rw [hD, hD]; exact h1 g Ψ₁ Ψ₁' (P Ψ₂) hg) (fun h => by`. Take `⟨m, hm, hmf⟩` from `h2 h`.

Take `⟨c, hc, hcf⟩` from `hPh h`. Use `⟨m / c, div_pos hm hc, fun Ψ₁ Ψ₁' Ψ₂ Ψ₂' e1 e2 => ?_⟩` and prove the remaining obligations. Establish `hχ : (fun Y => (P Ψ₂).1 (Y * h.1)) ∈ fullRk k ρ d` using `comp_mul_mem_fullRk h (P Ψ₂).2`. Establish `hP2 : P Ψ₂' = (c : ℂ) • (⟨_, hχ⟩ : fullRk k ρ d)` using `Subtype.ext (by rw [hcf Ψ₂ Ψ₂' e2]; rfl)`. Establish `hc0 : (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`.

Rewrite using `[hD, hD, hP2, map_smulₛₗ, ← hmf Ψ₁ Ψ₁' (P Ψ₂) ⟨_, hχ⟩ e1 rfl, Complex.conj_ofReal, smul_eq_mul]`. Use `push_cast`. Use the proof step `field_simp)`. Set `Lϖ : Matrix (Fin e) (Fin d) k ≃+ Matrix (Fin e) (Fin d) k` to `{ toFun := fun Y => (ϖ : k) • Y, invFun := fun Y => ((ϖ⁻¹ : kˣ) : k) • Y, left_inv := fun Y => by simp [smul_smul], right_inv := fun Y => by simp [smul_smul], map_add' := fun Y Z => smul_add _ _ _ }`. Take `⟨c, hc, hcf⟩` from `scaleB k e d μ Lϖ (by show Continuous fun Y : Matrix (Fin e) (Fin d) k => (ϖ : k) • Y; exact continuous_const_smul _) (by show Continuous fun Y : Matrix (Fin e) (Fin d) k => ((ϖ⁻¹ : kˣ) : k) • Y; exact continuous_const_smul _)`.

Take `⟨r, hr0, hra⟩` from `GlobalTheory.RankChart.exists_apow_eq (ϖ ^ e) d`. Use `set a : ℂ := (ν ϖ : ℂ) ^ e * ((r * c : ℝ) : ℂ) with ha`. Establish `hdil : ∀ Θ : fullRk k (ρ + e) d, P ⟨lact ν (dilN ρ e ϖ) Θ.1, lact_mem_fullRk _ _ Θ.2⟩ = a • P Θ`. Introduce `Θ`. Use `Subtype.ext (funext fun Y₁ => ?_)` and prove the remaining obligations.

Rewrite using `[hP]`. Use `show ∫ Y₂, lact ν (dilN ρ e ϖ) Θ.1 (jn Y₁ Y₂) ∂μ = a * (P Θ).1 Y₁`. Simplify using `only [lact, dilN_transpose_mul, gdet_dilN, hra]`. Rewrite using `[integral_const_mul, hP]`. Use `hcf (fun Y₂ => Θ.1 (jn Y₁ Y₂))` as an intermediate fact.

Simplify using `only [Lϖ] at this`. Use `erw [this]`. Simplify using `[ha]`. Expand and normalize the polynomial expressions, which then agree. Establish `hzero : ∀ Ψ₁ Θ, D Ψ₁ Θ = 0`.

Introduce `Ψ₁ Θ`. Establish `h3` using `key (dilN ρ e ϖ) Ψ₁ Θ ⟨_, lact_mem_fullRk _ _ Θ.2⟩ rfl`. Rewrite `h3` using `[hD, hD, hdil, map_smulₛₗ, smul_eq_mul]`. Establish `hne : starRingEnd ℂ a ≠ 1`. Introduce `h4`.

Establish `h5 : a = 1` using `by simpa using congrArg (starRingEnd ℂ) h4`. Establish `hrc : (0 : ℝ) < r * c` using `mul_pos hr0 hc`. Apply `hr e he (r * c)⁻¹` to reduce the goal to its premises. Rewrite `h5` using `[ha]`. Move the coercions through the operations in `at h5 ⊢`.

Conclude with `eq_inv_of_mul_eq_one_left h5`. Establish `: (starRingEnd ℂ a - 1) * Bf Ψ₁ (P Θ) = 0` using `by rw [sub_mul, h3]; ring`. Rewrite using `[hD]`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)`. Introduce `Ψ₁ Ψ₂`.

Take `⟨Θ, hΘ, hΘf⟩` from `ontoC k ρ e d μ hd.le Ψ₂.1 Ψ₂.2`. Establish `: P ⟨Θ, hΘ⟩ = Ψ₂` using `Subtype.ext (funext fun Y₁ => by rw [hP]; exact hΘf Y₁)`. Rewrite using `[← this, ← hD]`. Conclude with `hzero Ψ₁ _`.
-/
theorem fibre_bilinear_form_vanishes_rank (hKP : GlobalTheory.ThK.KP) (ρ e d : ℕ) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (hd : ρ + e < d) (he : 0 < e)
    (hs : GlobalTheory.SmGL.IsSmoothChar ν) (hu : GlobalTheory.SmGL.IsUnitaryChar ν)
    (hr : ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ))
    (Bf : fullRk k (ρ + e) d →ₗ[ℂ] fullRk k ρ d →ₗ⋆[ℂ] ℂ)
    (h1 : ∀ (g : GL (Fin (ρ + e)) k) (Ψ₁ Ψ₁' : fullRk k (ρ + e) d) (Ψ₂ : fullRk k ρ d),
      Ψ₁'.1 = lact ν g Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂)
    (h2 : ∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ (Ψ₁ Ψ₁' : fullRk k (ρ + e) d) (Ψ₂ Ψ₂' : fullRk k ρ d),
      Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) :
    ∀ Ψ₁ Ψ₂, Bf Ψ₁ Ψ₂ = 0 := by
  classical
  letI : MeasurableSpace (Matrix (Fin e) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin e) (Fin d) k) := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := @GlobalTheory.haar_exists_matrix_local_field k _ _ _ _ e d
  obtain ⟨P, hP⟩ := fibreA k ρ e d μ
  have hPh : ∀ h : GL (Fin d) k, ∃ c : ℝ, 0 < c ∧ ∀ Θ Θ' : fullRk k (ρ + e) d,
      Θ'.1 = (fun Y => Θ.1 (Y * h.1)) → (P Θ').1 = fun Y₁ => (c : ℂ) * (P Θ).1 (Y₁ * h.1) := by
    intro h
    let L : Matrix (Fin e) (Fin d) k ≃+ Matrix (Fin e) (Fin d) k :=
      { toFun := fun Y => Y * h.1, invFun := fun Y => Y * (h⁻¹).1,
        left_inv := fun Y => by simp [Matrix.mul_assoc], right_inv := fun Y => by simp [Matrix.mul_assoc],
        map_add' := fun Y Z => Matrix.add_mul _ _ _ }
    obtain ⟨c, hc, hcf⟩ := scaleB k e d μ L (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const)
    refine ⟨c, hc, fun Θ Θ' hΘ' => funext fun Y₁ => ?_⟩
    rw [hP, hP, hΘ']
    show ∫ Y₂, Θ.1 (jn Y₁ Y₂ * h.1) ∂μ = _
    simp only [jn_mul]
    exact hcf (fun Y₂ => Θ.1 (jn (Y₁ * h.1) Y₂))
  let D : fullRk k (ρ + e) d →ₗ[ℂ] fullRk k (ρ + e) d →ₗ⋆[ℂ] ℂ := Bf.compl₂ P
  have hD : ∀ Ψ₁ Θ, D Ψ₁ Θ = Bf Ψ₁ (P Θ) := fun _ _ => rfl
  have hν : ν ≠ 1 := by
    rintro rfl
    exact hr 1 one_pos 1 (by simp)
  have key := GlobalTheory.T.full_rank_coinvariant_form_zero hKP k (ρ + e) d ν hd hs hu hν D
    (fun g Ψ₁ Ψ₁' Ψ₂ hg => by rw [hD, hD]; exact h1 g Ψ₁ Ψ₁' (P Ψ₂) hg)
    (fun h => by
      obtain ⟨m, hm, hmf⟩ := h2 h
      obtain ⟨c, hc, hcf⟩ := hPh h
      refine ⟨m / c, div_pos hm hc, fun Ψ₁ Ψ₁' Ψ₂ Ψ₂' e1 e2 => ?_⟩
      have hχ : (fun Y => (P Ψ₂).1 (Y * h.1)) ∈ fullRk k ρ d := comp_mul_mem_fullRk h (P Ψ₂).2
      have hP2 : P Ψ₂' = (c : ℂ) • (⟨_, hχ⟩ : fullRk k ρ d) := Subtype.ext (by rw [hcf Ψ₂ Ψ₂' e2]; rfl)
      have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      rw [hD, hD, hP2, map_smulₛₗ, ← hmf Ψ₁ Ψ₁' (P Ψ₂) ⟨_, hχ⟩ e1 rfl, Complex.conj_ofReal, smul_eq_mul]
      push_cast
      field_simp)

  let Lϖ : Matrix (Fin e) (Fin d) k ≃+ Matrix (Fin e) (Fin d) k :=
    { toFun := fun Y => (ϖ : k) • Y, invFun := fun Y => ((ϖ⁻¹ : kˣ) : k) • Y,
      left_inv := fun Y => by simp [smul_smul], right_inv := fun Y => by simp [smul_smul],
      map_add' := fun Y Z => smul_add _ _ _ }
  obtain ⟨c, hc, hcf⟩ := scaleB k e d μ Lϖ
    (by show Continuous fun Y : Matrix (Fin e) (Fin d) k => (ϖ : k) • Y; exact continuous_const_smul _)
    (by show Continuous fun Y : Matrix (Fin e) (Fin d) k => ((ϖ⁻¹ : kˣ) : k) • Y; exact continuous_const_smul _)
  obtain ⟨r, hr0, hra⟩ := GlobalTheory.RankChart.exists_apow_eq (ϖ ^ e) d
  set a : ℂ := (ν ϖ : ℂ) ^ e * ((r * c : ℝ) : ℂ) with ha
  have hdil : ∀ Θ : fullRk k (ρ + e) d,
      P ⟨lact ν (dilN ρ e ϖ) Θ.1, lact_mem_fullRk _ _ Θ.2⟩ = a • P Θ := by
    intro Θ
    refine Subtype.ext (funext fun Y₁ => ?_)
    rw [hP]
    show ∫ Y₂, lact ν (dilN ρ e ϖ) Θ.1 (jn Y₁ Y₂) ∂μ = a * (P Θ).1 Y₁
    simp only [lact, dilN_transpose_mul, gdet_dilN, hra]
    rw [integral_const_mul, hP]
    have := hcf (fun Y₂ => Θ.1 (jn Y₁ Y₂))
    simp only [Lϖ] at this
    erw [this]
    simp [ha]
    ring
  have hzero : ∀ Ψ₁ Θ, D Ψ₁ Θ = 0 := by
    intro Ψ₁ Θ
    have h3 := key (dilN ρ e ϖ) Ψ₁ Θ ⟨_, lact_mem_fullRk _ _ Θ.2⟩ rfl
    rw [hD, hD, hdil, map_smulₛₗ, smul_eq_mul] at h3
    have hne : starRingEnd ℂ a ≠ 1 := by
      intro h4
      have h5 : a = 1 := by simpa using congrArg (starRingEnd ℂ) h4
      have hrc : (0 : ℝ) < r * c := mul_pos hr0 hc
      apply hr e he (r * c)⁻¹
      rw [ha] at h5
      push_cast at h5 ⊢
      exact eq_inv_of_mul_eq_one_left h5
    have : (starRingEnd ℂ a - 1) * Bf Ψ₁ (P Θ) = 0 := by rw [sub_mul, h3]; ring
    rw [hD]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  intro Ψ₁ Ψ₂
  obtain ⟨Θ, hΘ, hΘf⟩ := ontoC k ρ e d μ hd.le Ψ₂.1 Ψ₂.2
  have : P ⟨Θ, hΘ⟩ = Ψ₂ := Subtype.ext (funext fun Y₁ => by rw [hP]; exact hΘf Y₁)
  rw [← this, ← hD]
  exact hzero Ψ₁ _

/- English proof (translation)
Introduce `hKP k _ _ _ _ n ρ d ν ϖ hnd hρn hs hu hr Bf h1 h2`. Take `⟨e, rfl⟩` from `Nat.exists_eq_add_of_le hρn.le`. Conclude with `fibre_bilinear_form_vanishes_rank hKP ρ e d ν ϖ hnd (by omega) hs hu hr Bf h1 h2`.
-/
theorem form_eq_zero : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n ρ d : ℕ) (ν : kˣ →* ℂˣ) (ϖ : kˣ), n < d → ρ < n → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Bf : fullRk k n d →ₗ[ℂ] fullRk k ρ d →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' : fullRk k n d) (Ψ₂ : fullRk k ρ d), Ψ₁'.1 = lact ν g Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ (Ψ₁ Ψ₁' : fullRk k n d) (Ψ₂ Ψ₂' : fullRk k ρ d),
        Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      ∀ Ψ₁ Ψ₂, Bf Ψ₁ Ψ₂ = 0 := by
  intro hKP k _ _ _ _ n ρ d ν ϖ hnd hρn hs hu hr Bf h1 h2
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hρn.le
  exact fibre_bilinear_form_vanishes_rank hKP ρ e d ν ϖ hnd (by omega) hs hu hr Bf h1 h2
end GlobalTheory.FibreVanish

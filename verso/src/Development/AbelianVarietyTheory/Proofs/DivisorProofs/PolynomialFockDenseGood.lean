import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTriplePolynomialFockStableMulTraceLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussiansStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroGaussianVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleEqTopOfGaussianMemDerivStableStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open scoped Classical

noncomputable section

namespace GlobalTheory.PolDense

open GlobalTheory.GaussFockJ GlobalTheory.ThK.EvAt0.PolD

/- English proof (translation)
Establish `hcm` using `hB.cm`. Establish `hψ` using `hB.std`. Take `⟨ε, hε⟩` from `hG`. Set `rel : Matrix (Fin n) (Fin d) (AE F E) → InfinitePlace F → Matrix (Fin n) (Fin d) ℂ` to `fun u w => (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)`. Use `choose R hRat hRmap using fun u => exists_mat_at hcm B.emb (rel u)`.

Establish `hRadd : ∀ u v, R (u + v) = R u + R v`. Introduce `u v`. Use `eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_add, hRat u c hc, hRat v c hc, add_zero]) fun w => ?_` and prove the remaining obligations. Rewrite using `[hRmap, Matrix.map_add _ (map_add _), hRmap, hRmap]`. Simplify using `only [rel, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]`.

Establish `hRsmul : ∀ (c : AF F) u, R (c • u) = c • R u`. Introduce `c u`. Use `eq_of_map_piInf hcm B.emb (hRat _) (fun c' hc' => by rw [smul_comm, hRat u c' hc', smul_zero]) fun w => ?_` and prove the remaining obligations. Rewrite using `[hRmap, map_smul_piInf, hRmap]`. Simplify using `only [rel, map_smul_piInf, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]`.

Establish `hRR : ∀ u, At (evI F) u → R (R u) = -u`. Introduce `u hu`. Use `eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_neg, hu c hc, neg_zero]) fun w => ?_` and prove the remaining obligations. Rewrite using `[hRmap, Matrix.map_neg _ (map_neg _)]`. Simplify using `only [rel, hRmap]`.

Establish `hV` using `(hX.cartan w).1`. Establish `hW'` using `(hW.cartan w).1`. Establish `hWt : (W.θ w)ᵀ * (W.θ w)ᵀ = 1` using `by rw [← Matrix.transpose_mul, hW', Matrix.transpose_one]`. Establish `he : (((ε w : ℤ) : ℂ) * Complex.I) * (((ε w : ℤ) : ℂ) * Complex.I) = -1`. Establish `h1 : ((ε w : ℤ) : ℂ) * ((ε w : ℤ) : ℂ) = 1`.

Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`. Take the linear combination `(Complex.I * Complex.I) * h1 + Complex.I_mul_I`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, smul_smul, he, neg_one_smul]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hWt, Matrix.mul_one]`. Set `J : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))` to `fun w => Psi M (R (Phi M w))`.

Establish `hJPhi : ∀ w, Phi M (J w) = R (Phi M w)` using `fun w => Phi_Psi M (hRat _)`. Establish `hPsi_smul : ∀ (t : ℝ) v, At (evI F) v → Psi M (realAd F t • v) = t • Psi M v`. Introduce `t v hv`. Rewrite using `[← Phi_Psi M hv, ← Phi_smul, Psi_Phi, Psi_Phi]`. Set `J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))` to `{ toFun := J map_add' := fun w w' => by show Psi M (R (Phi M (w + w'))) = Psi M (R (Phi M w)) + Psi M (R (Phi M w'))`.

Rewrite using `[Phi_add, hRadd, Psi_add]`. Use the proof step `map_smul' := fun t w => by show Psi M (R (Phi M (t • w))) = t • Psi M (R (Phi M w))`. Rewrite using `[Phi_smul, hRsmul, hPsi_smul t _ (hRat _)] }`. Use `⟨J₀, fun w => ?_, fun w x => ?_⟩` and prove the remaining obligations. Use `show Psi M (R (Phi M (Psi M (R (Phi M w))))) = -w`.

Rewrite using `[Phi_Psi M (hRat _), hRR _ (at_Phi M w), Psi_neg, Psi_Phi]`. Establish `h` using `hε (Phi M w) (R (Phi M w)) (at_Phi M w) (hRat _) (hRmap _) _ _ (actsD_Phi hψ M w f₀) (by rw [← hJPhi]; exact actsD_Phi hψ M (J w) f₀)`. Rewrite using `[dHeis_eq_dOp, dHeis_eq_dOp]`. Use `show dOp (J w).1 (J w).2 f₀ x = _`. Rewrite using `[h]`.

Both sides reduce to the same expression.
-/
theorem exists_complex_structure_pair {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) {r s r' s' : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (f₀ : SInf F (Fin n × Fin d))
    (hG : M.IsGauss B.ψ B.emb f₀) :
    ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ ∀ w x, GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (J₀ w) ⇑f₀ x =
        Complex.I * GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) w ⇑f₀ x := by
  have hcm := hB.cm
  have hψ := hB.std
  obtain ⟨ε, hε⟩ := hG
  let rel : Matrix (Fin n) (Fin d) (AE F E) → InfinitePlace F → Matrix (Fin n) (Fin d) ℂ :=
    fun u w => (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)
  choose R hRat hRmap using fun u => exists_mat_at hcm B.emb (rel u)
  have hRadd : ∀ u v, R (u + v) = R u + R v := by
    intro u v
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_add, hRat u c hc, hRat v c hc, add_zero])
      fun w => ?_
    rw [hRmap, Matrix.map_add _ (map_add _), hRmap, hRmap]
    simp only [rel, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]
  have hRsmul : ∀ (c : AF F) u, R (c • u) = c • R u := by
    intro c u
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c' hc' => by rw [smul_comm, hRat u c' hc', smul_zero])
      fun w => ?_
    rw [hRmap, map_smul_piInf, hRmap]
    simp only [rel, map_smul_piInf, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  have hRR : ∀ u, At (evI F) u → R (R u) = -u := by
    intro u hu
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_neg, hu c hc, neg_zero]) fun w => ?_
    rw [hRmap, Matrix.map_neg _ (map_neg _)]
    simp only [rel, hRmap]
    have hV := (hX.cartan w).1
    have hW' := (hW.cartan w).1
    have hWt : (W.θ w)ᵀ * (W.θ w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hW', Matrix.transpose_one]
    have he : (((ε w : ℤ) : ℂ) * Complex.I) * (((ε w : ℤ) : ℂ) * Complex.I) = -1 := by
      have h1 : ((ε w : ℤ) : ℂ) * ((ε w : ℤ) : ℂ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
      linear_combination (Complex.I * Complex.I) * h1 + Complex.I_mul_I
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, he, neg_one_smul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hWt, Matrix.mul_one]
  let J : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    fun w => Psi M (R (Phi M w))
  have hJPhi : ∀ w, Phi M (J w) = R (Phi M w) := fun w => Phi_Psi M (hRat _)
  have hPsi_smul : ∀ (t : ℝ) v, At (evI F) v → Psi M (realAd F t • v) = t • Psi M v := by
    intro t v hv
    rw [← Phi_Psi M hv, ← Phi_smul, Psi_Phi, Psi_Phi]
  let J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    { toFun := J
      map_add' := fun w w' => by
        show Psi M (R (Phi M (w + w'))) = Psi M (R (Phi M w)) + Psi M (R (Phi M w'))
        rw [Phi_add, hRadd, Psi_add]
      map_smul' := fun t w => by
        show Psi M (R (Phi M (t • w))) = t • Psi M (R (Phi M w))
        rw [Phi_smul, hRsmul, hPsi_smul t _ (hRat _)] }
  refine ⟨J₀, fun w => ?_, fun w x => ?_⟩
  · show Psi M (R (Phi M (Psi M (R (Phi M w))))) = -w
    rw [Phi_Psi M (hRat _), hRR _ (at_Phi M w), Psi_neg, Psi_Phi]
  · have h := hε (Phi M w) (R (Phi M w)) (at_Phi M w) (hRat _) (hRmap _) _ _ (actsD_Phi hψ M w f₀)
      (by rw [← hJPhi]; exact actsD_Phi hψ M (J w) f₀)
    rw [dHeis_eq_dOp, dHeis_eq_dOp]
    show dOp (J w).1 (J w).2 f₀ x = _
    rw [h]
    rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW`. Take `⟨f₀, hne, hG⟩` from `GlobalTheory.T.exists_nonzero_gaussian_vector F E σ B n d r s r' s' X W M hB hX hW GlobalTheory.T.archHeisenbergDerivatives_exist GlobalTheory.T.archActionReadings_compatible`. Take `⟨J₀, hJJ, hJ⟩` from `exists_complex_structure_pair B X W M hB hX hW f₀ hG`. Take `⟨Q, -, -, hneg, hsol, -⟩` from `GlobalTheory.T.fockVacua_smooth_family_complexGaussians (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (GlobalTheory.GaussLine.pairInf_nondeg F (Fin n × Fin d)) (fun _ => J₀) (fun _ => contDiff_const) (fun _ => hJJ) (fun _ => ⟨f₀, hne, hJ⟩)`. Take `⟨ε, hε, hev⟩` from `hneg 0`.

Establish `hQ` using `hev.self_of_nhds`. Establish `hf` using `hsol 0 f₀ hJ`. Establish `h0 : f₀ 0 ≠ 0`. Introduce `h`. Apply `hne` to reduce the goal to its premises.

Use extensionality with `x`. Rewrite using `[hf x, h, zero_mul]`. Both sides reduce to the same expression. Establish `hmem : f₀ ∈ M.Pol B.ψ B.emb`. Rewrite using `[Model.Pol, Submodule.mem_sInf]`.

Conclude with `fun N hN => hN.1 f₀ hG`. Set `Qc : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ` to `LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ (-Q 0))`. Establish `hQc : ∀ x y, Qc x y = -Q 0 x y` using `fun x y => rfl`. Establish `hsurj : Function.Surjective (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)).flip`. Establish `hinj : Function.Injective (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)).flip`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `q hq`. Conclude with `GlobalTheory.GaussLine.pairInf_nondeg F _ q fun x => by`. Simplify using `using LinearMap.congr_fun hq x`. Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj`.

Use `GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable _ (M.Pol B.ψ B.emb) ((f₀ 0)⁻¹ • f₀) Qc ε hε (fun x => ?_) (fun x => ?_) (Submodule.smul_mem _ _ hmem) ?_ ?_` and prove the remaining obligations. Rewrite using `[hQc]`. Use `hQ x` as an intermediate fact. Simplify using `only [LinearMap.neg_apply, Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[SchwartzMap.smul_apply, hf x, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h0, one_mul, hQc, neg_neg]`. Introduce `v f f₁ hfN h₁`. Establish `e : dOp v 0 f = f₁`. Use `SchwartzMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[h₁ x, ← dHeis_eq_dOp (v, (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)) f x]`.

Simplify using `[GlobalTheory.GaussLine.dHeis]`. Rewrite `hfN`, the goal using `[Model.Pol, Submodule.mem_sInf]`. Introduce `N hN`. Conclude with `e ▸ hN.2 _ (at_Phi M (v, 0)) f (hfN N hN) _ (actsD_Phi hB.std M (v, 0) f)`. Introduce `ℓ f f₁ hfN h₁`.

Take `⟨q, hq⟩` from `hsurj ℓ.toLinearMap`. Take `⟨f₂, hf₂, h₂⟩` from `GlobalTheory.PolMul.model_mul M B.ψ hB.std B.emb q f hfN`. Establish `e : f₂ = f₁`. Use `SchwartzMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[h₂ x, h₁ x]`.

Use `LinearMap.congr_fun hq x` as an intermediate fact. Simplify using `only [LinearMap.flip_apply, ContinuousLinearMap.coe_coe] at this`. Rewrite using `[this]`. Conclude with `e ▸ hf₂`.
-/
theorem pol_dense_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    Dense ((M.Pol B.ψ B.emb : Submodule ℂ (SInf F (Fin n × Fin d))) : Set (SInf F (Fin n × Fin d))) := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW
  obtain ⟨f₀, hne, hG⟩ := GlobalTheory.T.exists_nonzero_gaussian_vector F E σ B n d r s r' s' X W M hB hX hW GlobalTheory.T.archHeisenbergDerivatives_exist GlobalTheory.T.archActionReadings_compatible
  obtain ⟨J₀, hJJ, hJ⟩ := exists_complex_structure_pair B X W M hB hX hW f₀ hG
  obtain ⟨Q, -, -, hneg, hsol, -⟩ := GlobalTheory.T.fockVacua_smooth_family_complexGaussians (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d))
    (GlobalTheory.GaussLine.pairInf_nondeg F (Fin n × Fin d)) (fun _ => J₀) (fun _ => contDiff_const) (fun _ => hJJ)
    (fun _ => ⟨f₀, hne, hJ⟩)
  obtain ⟨ε, hε, hev⟩ := hneg 0
  have hQ := hev.self_of_nhds
  have hf := hsol 0 f₀ hJ
  have h0 : f₀ 0 ≠ 0 := by
    intro h
    apply hne
    ext x
    rw [hf x, h, zero_mul]
    rfl
  have hmem : f₀ ∈ M.Pol B.ψ B.emb := by
    rw [Model.Pol, Submodule.mem_sInf]
    exact fun N hN => hN.1 f₀ hG

  let Qc : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
        (-Q 0))
  have hQc : ∀ x y, Qc x y = -Q 0 x y := fun x y => rfl

  have hsurj : Function.Surjective (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)).flip := by
    have hinj : Function.Injective (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)).flip := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro q hq
      exact GlobalTheory.GaussLine.pairInf_nondeg F _ q fun x => by
        simpa using LinearMap.congr_fun hq x
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  refine GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable _ (M.Pol B.ψ B.emb) ((f₀ 0)⁻¹ • f₀) Qc ε hε (fun x => ?_) (fun x => ?_)
    (Submodule.smul_mem _ _ hmem) ?_ ?_
  · rw [hQc]
    have := hQ x
    simp only [LinearMap.neg_apply, Complex.neg_re]
    linarith
  · rw [SchwartzMap.smul_apply, hf x, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h0, one_mul, hQc, neg_neg]
  · intro v f f₁ hfN h₁
    have e : dOp v 0 f = f₁ := by
      refine SchwartzMap.ext fun x => ?_
      rw [h₁ x, ← dHeis_eq_dOp (v, (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)) f x]
      simp [GlobalTheory.GaussLine.dHeis]
    rw [Model.Pol, Submodule.mem_sInf] at hfN ⊢
    intro N hN
    exact e ▸ hN.2 _ (at_Phi M (v, 0)) f (hfN N hN) _ (actsD_Phi hB.std M (v, 0) f)
  · intro ℓ f f₁ hfN h₁
    obtain ⟨q, hq⟩ := hsurj ℓ.toLinearMap
    obtain ⟨f₂, hf₂, h₂⟩ := GlobalTheory.PolMul.model_mul M B.ψ hB.std B.emb q f hfN
    have e : f₂ = f₁ := by
      refine SchwartzMap.ext fun x => ?_
      rw [h₂ x, h₁ x]
      have := LinearMap.congr_fun hq x
      simp only [LinearMap.flip_apply, ContinuousLinearMap.coe_coe] at this
      rw [this]
    exact e ▸ hf₂

end GlobalTheory.PolDense

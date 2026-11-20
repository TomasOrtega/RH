import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalCoordsCMStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCMStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaNonzeroF

/- English proof (translation)
Establish `hinv : J⁻¹ * J = 1` using `Matrix.nonsing_inv_mul J hdet`. Establish `hmap : (J⁻¹).map σ * J.map σ = 1`. Use `congrArg (fun M => M.map σ) hinv` as an intermediate fact. Simplify `this` using `[Matrix.map_mul, Matrix.map_one]`. Establish `hT : (J.map σ)ᵀ = J`.

Use extensionality with `i j`. Simplify using `[Matrix.transpose_apply, Matrix.map_apply, hJ]`. Establish `h2 : J * ((J⁻¹).map σ)ᵀ = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hX : ((J⁻¹).map σ)ᵀ = J⁻¹` using `(Matrix.inv_eq_right_inv h2).symm`.

Introduce `i j`. Use `congrFun (congrFun hX i) j` as an intermediate fact. Simplify `this` using `[Matrix.transpose_apply, Matrix.map_apply]`.
-/
theorem herm_inv_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) :
    ∀ i j, σ (J⁻¹ j i) = J⁻¹ i j := by
  have hinv : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  have hmap : (J⁻¹).map σ * J.map σ = 1 := by
    have := congrArg (fun M => M.map σ) hinv
    simpa [Matrix.map_mul, Matrix.map_one] using this
  have hT : (J.map σ)ᵀ = J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have h2 : J * ((J⁻¹).map σ)ᵀ = 1 := by
    calc J * ((J⁻¹).map σ)ᵀ = (J.map σ)ᵀ * ((J⁻¹).map σ)ᵀ := by rw [hT]
      _ = 1 := by rw [← Matrix.transpose_mul, hmap, Matrix.transpose_one]
  have hX : ((J⁻¹).map σ)ᵀ = J⁻¹ := (Matrix.inv_eq_right_inv h2).symm
  intro i j
  have := congrFun (congrFun hX i) j
  simpa [Matrix.transpose_apply, Matrix.map_apply] using this

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ`. Establish `hstd` using `GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hσ : ∀ x, σ (σ x) = x` using `fun x => by`. Apply `((B.emb w).1 : E →+* ℂ).injective` to reduce the goal to its premises.

Rewrite using `[hB.cm.2.2.2, hB.cm.2.2.2, star_star]`. Establish `h2 : Module.finrank F E = 2` using `hB.cm.2.2.1`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)`. Set `JA : Matrix (Fin nT) (Fin nT) E` to `JTᵀ`. Set `JB : Matrix (Fin nS) (Fin nS) E` to `-(ξ₀ • JS⁻¹)`.

Apply the tactic sequence `have hSinv := herm_inv_entry σ JS hS.1 (Ne.isUnit hS.2)`. Establish `hA : ∀ i j, σ (JA j i) = JA i j` using `fun i j => hT.1 j i`. Establish `hBs : ∀ i j, σ (JB j i) = -JB i j` using `fun i j => by`. Simplify using `only [JB, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσξ, hSinv]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hA' : JA.det ≠ 0` using `by simp only [JA, Matrix.det_transpose]; exact hT.2`. Establish `hB' : JB.det ≠ 0`. Simplify using `only [JB, Matrix.det_neg, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : E) ≠ 0)) (mul_ne_zero (pow_ne_zero _ hξ0) (Matrix.isUnit_nonsing_inv_det JS (Ne.isUnit hS.2)).ne_zero)`. Take `⟨co, hco⟩` from `GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hA hBs hA' hB'`.

Set `co' : Darboux (symp (cA σ) (-1 : AF F ⊗[F] E) (incM F JA) (incM F JB)) (Fin nT × Fin nS)` to `co`. Establish `hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F, co'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))` using `hco`. Establish `hJA : JA = JTᵀ` using `rfl`. Establish `hJB : (-1 : AF F ⊗[F] E) • incM F JB = incM F (ξ₀ • JS⁻¹)`. Use extensionality with `i j`.

Simplify using `[JB, incM]`. Set `τ` to `Fintype.equivFin (Fin nT × Fin nS)`. Establish `he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co' τ w) (GlobalTheory.TransportF.numCoordF co' τ w')` using `fun w w' => by`. Rewrite using `[GlobalTheory.TransportF.symplOF_eq_symp hJA hJB, co'.form]`. Simplify using `only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]`.

Establish `hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F, GlobalTheory.TransportF.numCoordF co' τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)` using `fun x => by`. Take `⟨y, z, h⟩` from `hrat x`. Conclude with `⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩`. Take `⟨Φ, hΦ, hne⟩` from `GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin nT × Fin nS)`. Use `⟨GlobalTheory.WeilSchrodinger.thetaTr F co' B.ψ Φ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.TransportF.thetaTr_eqF co' τ]`. Conclude with `GlobalTheory.T.isThetaFunction_thetaTransform_rational_coords_CM F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hstd _ (GlobalTheory.TransportF.numCoordF co' τ) he hr _ (GlobalTheory.TransportF.comp_mem_schA τ hΦ)`. Introduce `h`. Establish `h0` using `congrFun h 0`. Apply `hne` to reduce the goal to its premises.

Establish `hs : GlobalTheory.WeilM.schr B.ψ (0 : (Fin nT × Fin nS → AF F) × (Fin nT × Fin nS → AF F)) Φ = Φ`. Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.WeilM.schr]`. Simplify `h0` using `[GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hs]`.
-/
theorem exists_isThetaFunOF_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∃ f₀ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ
  have hstd := GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  let JA : Matrix (Fin nT) (Fin nT) E := JTᵀ
  let JB : Matrix (Fin nS) (Fin nS) E := -(ξ₀ • JS⁻¹)
  have hSinv := herm_inv_entry σ JS hS.1 (Ne.isUnit hS.2)
  have hA : ∀ i j, σ (JA j i) = JA i j := fun i j => hT.1 j i
  have hBs : ∀ i j, σ (JB j i) = -JB i j := fun i j => by
    simp only [JB, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσξ, hSinv]
    ring
  have hA' : JA.det ≠ 0 := by simp only [JA, Matrix.det_transpose]; exact hT.2
  have hB' : JB.det ≠ 0 := by
    simp only [JB, Matrix.det_neg, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : E) ≠ 0))
      (mul_ne_zero (pow_ne_zero _ hξ0) (Matrix.isUnit_nonsing_inv_det JS (Ne.isUnit hS.2)).ne_zero)
  obtain ⟨co, hco⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hA hBs hA' hB'
  let co' : Darboux (symp (cA σ) (-1 : AF F ⊗[F] E) (incM F JA) (incM F JB)) (Fin nT × Fin nS) := co
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
      co'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := hco
  have hJA : JA = JTᵀ := rfl
  have hJB : (-1 : AF F ⊗[F] E) • incM F JB = incM F (ξ₀ • JS⁻¹) := by
    ext i j
    simp [JB, incM]
  let τ := Fintype.equivFin (Fin nT × Fin nS)
  have he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co' τ w) (GlobalTheory.TransportF.numCoordF co' τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp hJA hJB, co'.form]
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F,
      GlobalTheory.TransportF.numCoordF co' τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  obtain ⟨Φ, hΦ, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin nT × Fin nS)
  refine ⟨GlobalTheory.WeilSchrodinger.thetaTr F co' B.ψ Φ, ?_, ?_⟩
  · rw [GlobalTheory.TransportF.thetaTr_eqF co' τ]
    exact GlobalTheory.T.isThetaFunction_thetaTransform_rational_coords_CM F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hstd _ (GlobalTheory.TransportF.numCoordF co' τ) he hr _
      (GlobalTheory.TransportF.comp_mem_schA τ hΦ)
  · intro h
    have h0 := congrFun h 0
    apply hne
    have hs : GlobalTheory.WeilM.schr B.ψ (0 : (Fin nT × Fin nS → AF F) × (Fin nT × Fin nS → AF F)) Φ = Φ := by
      funext x
      simp [GlobalTheory.WeilM.schr]
    simpa [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hs] using h0

end GlobalTheory.ThetaNonzeroF

end

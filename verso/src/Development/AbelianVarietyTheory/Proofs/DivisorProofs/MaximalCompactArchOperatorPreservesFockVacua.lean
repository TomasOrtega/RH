import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KInfVac

open GlobalTheory.RealLift GlobalTheory.KInfPol

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk A hA f₀ hf₀`. Establish `hB` using `hP.base`. Establish `hw` using `hP.weil`. Rewrite `hf₀`, the goal using `[← GlobalTheory.ThK.EvAt0.PolEv.isGauss_iff hB.std]`. Take `⟨D, hD⟩` from `GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std`.

Establish `hL` using `actsLaws F (Fin n × Fin d)`. Establish `hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine B.ψ u) φ (D u φ)` using `fun u hu φ => (hD u hu φ).1`. Establish `hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ)` using `fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M B.ψ u) (hSD u hu φ)`. Establish `hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ))` using `fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M B.ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))`. Establish `hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1`.

Rewrite using `[← Matrix.transpose_mul]`. Express the relevant statement in the definitionally equal form `(mat (k * k⁻¹))ᵀ = 1`. Rewrite using `[mul_inv_cancel]`. Conclude with `Matrix.transpose_one`. Establish `hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u` using `fun u => by`.

Rewrite using `[Matrix.mul_assoc, hkk, Matrix.mul_one]`. Take `⟨ε, hε⟩` from `hf₀`. Use `⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩` and prove the remaining obligations. Establish `hv` using `at_mul_right hu (mat k⁻¹)ᵀ`. Establish `hv'` using `at_mul_right hu' (mat k⁻¹)ᵀ`.

Establish `h1` using `hint _ hv f₀`. Establish `h2` using `hint _ hv' f₀`. Rewrite `h1`, `h2` using `[hcan]`. Establish `e1` using `(hL _ _ _).2.2.1 _ hg h1`. Establish `e2` using `(hL _ _ _).2.2.1 _ hg' h2`.

Establish `key` using `hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)`. Rewrite using `[e1, e2, key, map_smul]`. Establish `hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1`. Rewrite using `[← Matrix.map_mul]`. Express the relevant statement in the definitionally equal form `(mat (k⁻¹ * k)).map _ = 1`.

Rewrite using `[inv_mul_cancel]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1` using `mul_eq_one_comm.1 hm`. Establish `hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]`. Use `congr 1`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]`.
-/
theorem gaussD_of_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ g : SInf F (Fin n × Fin d), GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb g → GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb (A g) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk A hA f₀ hf₀
  have hB := hP.base
  have hw := hP.weil
  rw [← GlobalTheory.ThK.EvAt0.PolEv.isGauss_iff hB.std] at hf₀ ⊢
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine B.ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M B.ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M B.ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  obtain ⟨ε, hε⟩ := hf₀
  refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
  have hv := at_mul_right hu (mat k⁻¹)ᵀ
  have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
  have h1 := hint _ hv f₀
  have h2 := hint _ hv' f₀
  rw [hcan] at h1 h2
  have e1 := (hL _ _ _).2.2.1 _ hg h1
  have e2 := (hL _ _ _).2.2.1 _ hg' h2
  have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
  · rw [e1, e2, key, map_smul]
  · have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
      rw [← Matrix.map_mul]
      change (mat (k⁻¹ * k)).map _ = 1
      rw [inv_mul_cancel]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
    have hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
      calc _ = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w *
            ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
        _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) *
            (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
    rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]

end GlobalTheory.KInfVac

end

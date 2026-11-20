import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatMem

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G

variable {F : Type} [Field F] [NumberField F]

private def eQ : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun := Sum.elim ![0, 2, 3] fun _ => 1
  invFun := ![.inl 0, .inr (), .inl 1, .inl 2]
  left_inv := by
    rintro (i | ⟨⟩)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/- English proof (translation)
Set `M : Matrix (Fin 4) (Fin 3 ⊕ Unit) F` to `(1 : Matrix (Fin 4) (Fin 4) F).submatrix id eQ`. Set `N : Matrix (Fin 3 ⊕ Unit) (Fin 4) F` to `(1 : Matrix (Fin 4) (Fin 4) F).submatrix eQ id`. Establish `hNM : N * M = 1`. Establish `h` using `Matrix.submatrix_mul (1 : Matrix (Fin 4) (Fin 4) F) (1 : Matrix (Fin 4) (Fin 4) F) eQ id eQ Function.bijective_id`. Rewrite `h` using `[Matrix.mul_one, Matrix.submatrix_one_equiv]`.

Conclude with `h.symm`. Establish `hMN : M * N = 1`. Establish `h` using `Matrix.submatrix_mul (1 : Matrix (Fin 4) (Fin 4) F) (1 : Matrix (Fin 4) (Fin 4) F) id eQ id eQ.bijective`. Rewrite `h` using `[Matrix.mul_one, Matrix.submatrix_id_id]`. Conclude with `h.symm`.

Establish `h` using `GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hφ`. Establish `hx : ∀ x : Fin 3 ⊕ Unit → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun i => x (eQ.symm i)`. Introduce `x`. Use function extensionality and compare the values at `i`. Establish `hM : ∀ j k, M j k = if j = eQ k then (1 : F) else 0` using `fun j k => by`.

Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin 4) (Fin 4) F) j (eQ k) = _`. Conclude with `Matrix.one_apply`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, hM]`. Rewrite using `[Finset.sum_eq_single (eQ.symm i)]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Establish `: i ≠ eQ b` using `fun h => hb (by simp [h])`. Simplify using `[this]`. Simplify using the standard rewrite rules. Simplify `h` using `only [hx]`.
-/
private theorem reindex_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4)) :
    (fun z : Fin 3 ⊕ Unit → A F => φ fun i => z (eQ.symm i)) ∈ schwartzBruhatPi F (Fin 3 ⊕ Unit) := by
  let M : Matrix (Fin 4) (Fin 3 ⊕ Unit) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix id eQ
  let N : Matrix (Fin 3 ⊕ Unit) (Fin 4) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix eQ id
  have hNM : N * M = 1 := by
    have h := Matrix.submatrix_mul (1 : Matrix (Fin 4) (Fin 4) F) (1 : Matrix (Fin 4) (Fin 4) F)
      eQ id eQ Function.bijective_id
    rw [Matrix.mul_one, Matrix.submatrix_one_equiv] at h
    exact h.symm
  have hMN : M * N = 1 := by
    have h := Matrix.submatrix_mul (1 : Matrix (Fin 4) (Fin 4) F) (1 : Matrix (Fin 4) (Fin 4) F)
      id eQ id eQ.bijective
    rw [Matrix.mul_one, Matrix.submatrix_id_id] at h
    exact h.symm
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hφ
  have hx : ∀ x : Fin 3 ⊕ Unit → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun i => x (eQ.symm i) := by
    intro x
    funext i
    have hM : ∀ j k, M j k = if j = eQ k then (1 : F) else 0 := fun j k => by
      change (1 : Matrix (Fin 4) (Fin 4) F) j (eQ k) = _
      exact Matrix.one_apply
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hM]
    rw [Finset.sum_eq_single (eQ.symm i)]
    · simp
    · intro b _ hb
      have : i ≠ eQ b := fun h => hb (by simp [h])
      simp [this]
    · simp
  simpa only [hx] using h

/- English proof (translation)
Establish `h` using `GroundTheory.Heights₂.Theta.integrable_partialFourierPi_slice (reindex_mem φ.2) (fun i : Fin 3 => v (eQ (.inl i)))`. Establish `hmp` using `measurePreserving_funUnique (adeleMeasure F) Unit`. Use `(hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 ?_` and prove the remaining obligations. Use `h.congr (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Establish `: (fun i => (Sum.elim (fun i : Fin 3 => v (eQ (.inl i))) y : Fin 3 ⊕ Unit → A F) (eQ.symm i)) = Function.update v 1 (MeasurableEquiv.funUnique Unit (A F) y)`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [eQ]`. Simplify using `only [Function.comp]`. Rewrite using `[this]`.
-/
private theorem integrable_slice (φ : S4 F) (v : V4 F) :
    Integrable (fun s : A F => φ.1 (Function.update v 1 s)) (adeleMeasure F) := by
  have h := GroundTheory.Heights₂.Theta.integrable_partialFourierPi_slice (reindex_mem φ.2)
    (fun i : Fin 3 => v (eQ (.inl i)))
  have hmp := measurePreserving_funUnique (adeleMeasure F) Unit
  refine (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 ?_
  refine h.congr (Eventually.of_forall fun y => ?_)
  have : (fun i => (Sum.elim (fun i : Fin 3 => v (eQ (.inl i))) y : Fin 3 ⊕ Unit → A F) (eQ.symm i)) =
      Function.update v 1 (MeasurableEquiv.funUnique Unit (A F) y) := by
    funext i
    fin_cases i <;> simp [eQ]
  simp only [Function.comp]
  rw [this]

/- English proof (translation)
Establish `hs` using `integrable_slice φ v`. Establish `hc : Continuous fun s : A F => ψ (-(s * v 1))` using `continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp (continuous_id.mul continuous_const).neg)`. Conclude with `hs.mono (hs.1.mul hc.aestronglyMeasurable) (Eventually.of_forall fun s => by rw [norm_mul, ψ, Circle.norm_coe, mul_one])`.
-/
private theorem integrable_term (φ : S4 F) (v : V4 F) :
    Integrable (fun s : A F => φ.1 (Function.update v 1 s) * ψ (-(s * v 1))) (adeleMeasure F) := by
  have hs := integrable_slice φ v
  have hc : Continuous fun s : A F => ψ (-(s * v 1)) :=
    continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp
      (continuous_id.mul continuous_const).neg)
  exact hs.mono (hs.1.mul hc.aestronglyMeasurable)
    (Eventually.of_forall fun s => by rw [norm_mul, ψ, Circle.norm_coe, mul_one])

end UpperTheory.ConvolutionTheory.R2.G

/- English proof (translation)
Introduce `F _ _`. Establish `hadd : ∀ φ χ : S4 F, hat (φ + χ).1 = hat φ.1 + hat χ.1`. Introduce `φ χ`. Use function extensionality and compare the values at `v`. Simplify using `only [hat, Submodule.coe_add, Pi.add_apply, add_mul]`.

Conclude with `integral_add (integrable_term φ v) (integrable_term χ v)`. Establish `hsmul : ∀ (c : ℂ) (φ : S4 F), hat (c • φ).1 = c • hat φ.1`. Introduce `c φ`. Use function extensionality and compare the values at `v`. Simplify using `only [hat, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]`.

Conclude with `integral_const_mul c _`. Use `⟨{ toFun := fun φ => ⟨hat φ.1, (UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1⟩ map_add' := fun φ χ => Subtype.ext (hadd φ χ) map_smul' := fun c φ => Subtype.ext (hsmul c φ) }, fun φ => rfl⟩` and prove the remaining obligations.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.hatLin :
    ∀ (F : Type) [Field F] [NumberField F], ∃ H : S4 F →ₗ[ℂ] S4 F, ∀ φ, (H φ).1 = hat φ.1 := by
  intro F _ _
  have hadd : ∀ φ χ : S4 F, hat (φ + χ).1 = hat φ.1 + hat χ.1 := by
    intro φ χ
    funext v
    simp only [hat, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrable_term φ v) (integrable_term χ v)
  have hsmul : ∀ (c : ℂ) (φ : S4 F), hat (c • φ).1 = c • hat φ.1 := by
    intro c φ
    funext v
    simp only [hat, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  refine ⟨{ toFun := fun φ => ⟨hat φ.1, (UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1⟩
            map_add' := fun φ χ => Subtype.ext (hadd φ χ)
            map_smul' := fun c φ => Subtype.ext (hsmul c φ) }, fun φ => rfl⟩

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneTransferStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXUW

/- English proof (translation)
Introduce `hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he h c hc hz`. Establish `hS` using `IsUWeilPair.isUSplitting hP.weil`. Establish `hS₁` using `IsUWeilPair.isUSplitting hP₁.weil`. Establish `hone : incM F (1 : Matrix (Fin d) (Fin d) E) = 1` using `by simp [incM]`. Establish `hinvG : ∀ a : UA σ W.J, om₁ (1, a) * om₁ (1, a⁻¹) = 1` using `fun a => by`.

Apply the tactic sequence `rw [← map_mul, ← map_one om₁]; congr 1; ext <;> simp`. Establish `hmulX : ∀ a b : UA σ W.J, om (1, a * b) = om (1, a) * om (1, b)` using `fun a b => by`. Apply the tactic sequence `rw [← map_mul]; congr 1; ext <;> simp`. Establish `hmulX₁ : ∀ a b : UA σ W.J, om₁ (1, a * b) = om₁ (1, a) * om₁ (1, b)` using `fun a b => by`. Apply the tactic sequence `rw [← map_mul]; congr 1; ext <;> simp`.

Establish `key : ∀ h' : UA σ W.J, ∃ c' : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), om₁ (1, h'⁻¹) (e (om (1, h') Ψ)) = c' • e Ψ`. Introduce `h'`. Use `set e' : Fn F n d →ₗ[ℂ] Fn F n₁ d := om₁ (1, h'⁻¹) ∘ₗ e ∘ₗ om (1, h') with he'`. Establish `e'_apply : ∀ Ψ, e' Ψ = om₁ (1, h'⁻¹) (e (om (1, h') Ψ))` using `fun Ψ => rfl`. Establish `hmaps : ∀ Ψ ∈ schA F (Fin n × Fin d), e' Ψ ∈ schA F (Fin n₁ × Fin d)` using `fun Ψ hΨ => hS₁.pres _ _ (he.maps _ (hS.pres _ _ hΨ))`.

Establish `hheis : ∀ z, ∀ Ψ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Ψ) = M₁.co.rho B.ψ z (e' Ψ)`. Introduce `z Ψ hΨ`. Rewrite using `[e'_apply, e'_apply, hS.impl _ _ _ hΨ]`. Establish `h1 : actAB (cA σ) ((1 : UA σ X.J), h') (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) = incM F H.ι * (z * (mat h')ᵀ) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ`. Simplify using `only [actAB, hone, Matrix.transpose_one, Matrix.mul_one]`.

Simplify using `[mat, Matrix.mul_assoc]`. Rewrite using `[h1, he.Heisenberg₂ _ _ (hS.pres _ _ hΨ), hS₁.impl _ _ _ (he.maps _ (hS.pres _ _ hΨ))]`. Use `congr 2`. Simplify using `only [actAB]`. Establish `h2 : mat h'⁻¹ * mat h' = 1` using `by show mat (h'⁻¹ * h') = 1`.

Rewrite using `[inv_mul_cancel]`. Both sides reduce to the same expression. Use `show ((1 : Matrix (Fin n₁) (Fin n₁) (AE F E))) * (z * (mat h')ᵀ) * (mat h'⁻¹)ᵀ = z`. Rewrite using `[Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h2, Matrix.transpose_one, Matrix.mul_one]`. Establish `hinvI : ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Ψ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ u Ψ) = e' Ψ`.

Introduce and unpack `u ⟨z, rfl⟩ Ψ hΨ`. Rewrite using `[e'_apply, e'_apply, hS.impl _ _ _ hΨ]`. Establish `h1 : actAB (cA σ) ((1 : UA σ X.J), h') (Matrix.vecMulVec (incV F H.x) z) = Matrix.vecMulVec (incV F H.x) (mat h' *ᵥ z)`. Simplify using `only [actAB]`. Use `show (1 : Matrix (Fin n) (Fin n) (AE F E)) * Matrix.vecMulVec (incV F H.x) z * (mat h')ᵀ = _`.

Rewrite using `[Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]`. Rewrite using `[h1, he.inv _ ⟨_, rfl⟩ _ (hS.pres _ _ hΨ)]`. Establish `hadm : ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d), l ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d)`. Introduce `l hl`. Establish `a1` using `hS₁.adm (1, h'⁻¹) l hl`.

Establish `a2` using `GlobalTheory.T.hermitian_adapted_plane_constant hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he _ a1`. Conclude with `hS.adm (1, h') _ a2`. Conclude with `GlobalTheory.T.hermitian_adapted_plane_seesaw hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he e' hmaps hheis hinvI hadm`. Use `choose κ hκ using key`. Take `⟨Φ₀, hΦ₀, hne⟩` from `hz`.

Establish `uniqS : ∀ a b : ℂ, a • e Φ₀ = b • e Φ₀ → a = b` using `fun a b hab => smul_left_injective ℂ hne hab`. Establish `hcκ : c = κ h` using `uniqS _ _ ((hc Φ₀ hΦ₀).symm.trans (hκ h Φ₀ hΦ₀))`. Establish `hκ1 : κ 1 = 1`. Use `uniqS _ _ ?_` and prove the remaining obligations. Rewrite using `[← hκ 1 Φ₀ hΦ₀, one_smul, inv_one, show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply, show om₁ (1, 1) = 1 from map_one om₁, Module.End.one_apply]`.

Establish `hκmul : ∀ a b, κ (a * b) = κ a * κ b`. Introduce `a b`. Use `uniqS _ _ ?_` and prove the remaining obligations. Rewrite using `[← hκ (a * b) Φ₀ hΦ₀, mul_inv_rev, hmulX, hmulX₁, Module.End.mul_apply, Module.End.mul_apply, hκ a _ (hS.pres _ _ hΦ₀), map_smul, hκ b _ hΦ₀, smul_smul, mul_comm]`. Establish `hκinv : ∀ a, κ a * κ a⁻¹ = 1` using `fun a => by rw [← hκmul, mul_inv_cancel, hκ1]`.

Set `cχ : UA σ W.J →* ℂˣ` to `{ toFun := fun a => ⟨κ a, κ a⁻¹, hκinv a, by simpa using hκinv a⁻¹⟩ map_one' := Units.ext hκ1 map_mul' := fun a b => Units.ext (hκmul a b) }`. Establish `hχ : ∀ a, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, a) Φ) = (cχ a : ℂ) • om₁ (1, a) (e Φ)`. Introduce `a Φ hΦ`. Establish `k` using `congrArg (om₁ (1, a)) (hκ a Φ hΦ)`. Rewrite `k` using `[← Module.End.mul_apply, hinvG, Module.End.one_apply, map_smul]`.

Conclude with `k`. Establish `h1` using `GlobalTheory.T.hermitian_adapted_plane_transfer hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he ⟨Φ₀, hΦ₀, hne⟩ cχ hχ`. Establish `h2 : (cχ h : ℂ) = 1` using `by rw [h1]; rfl`. Rewrite using `[hcκ]`. Conclude with `h2`.
-/
theorem twist_scalar_eq_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (h : UA σ W.J) (c : ℂ), (∀ Φ ∈ schA F (Fin n × Fin d), om₁ (1, h⁻¹) (e (om (1, h) Φ)) = c • e Φ) →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) → c = 1 := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he h c hc hz
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hS₁ := IsUWeilPair.isUSplitting hP₁.weil
  have hone : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by simp [incM]
  have hinvG : ∀ a : UA σ W.J, om₁ (1, a) * om₁ (1, a⁻¹) = 1 := fun a => by
    rw [← map_mul, ← map_one om₁]; congr 1; ext <;> simp
  have hmulX : ∀ a b : UA σ W.J, om (1, a * b) = om (1, a) * om (1, b) := fun a b => by
    rw [← map_mul]; congr 1; ext <;> simp
  have hmulX₁ : ∀ a b : UA σ W.J, om₁ (1, a * b) = om₁ (1, a) * om₁ (1, b) := fun a b => by
    rw [← map_mul]; congr 1; ext <;> simp

  have key : ∀ h' : UA σ W.J, ∃ c' : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d),
      om₁ (1, h'⁻¹) (e (om (1, h') Ψ)) = c' • e Ψ := by
    intro h'
    set e' : Fn F n d →ₗ[ℂ] Fn F n₁ d := om₁ (1, h'⁻¹) ∘ₗ e ∘ₗ om (1, h') with he'
    have e'_apply : ∀ Ψ, e' Ψ = om₁ (1, h'⁻¹) (e (om (1, h') Ψ)) := fun Ψ => rfl
    have hmaps : ∀ Ψ ∈ schA F (Fin n × Fin d), e' Ψ ∈ schA F (Fin n₁ × Fin d) := fun Ψ hΨ =>
      hS₁.pres _ _ (he.maps _ (hS.pres _ _ hΨ))
    have hheis : ∀ z, ∀ Ψ ∈ schA F (Fin n × Fin d),
        e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Ψ) = M₁.co.rho B.ψ z (e' Ψ) := by
      intro z Ψ hΨ
      rw [e'_apply, e'_apply, hS.impl _ _ _ hΨ]
      have h1 : actAB (cA σ) ((1 : UA σ X.J), h') (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
          incM F H.ι * (z * (mat h')ᵀ) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ := by
        simp only [actAB, hone, Matrix.transpose_one, Matrix.mul_one]
        simp [mat, Matrix.mul_assoc]
      rw [h1, he.Heisenberg₂ _ _ (hS.pres _ _ hΨ), hS₁.impl _ _ _ (he.maps _ (hS.pres _ _ hΨ))]
      congr 2
      simp only [actAB]
      have h2 : mat h'⁻¹ * mat h' = 1 := by
        show mat (h'⁻¹ * h') = 1
        rw [inv_mul_cancel]; rfl
      show ((1 : Matrix (Fin n₁) (Fin n₁) (AE F E))) * (z * (mat h')ᵀ) * (mat h'⁻¹)ᵀ = z
      rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h2, Matrix.transpose_one, Matrix.mul_one]
    have hinvI : ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Ψ ∈ schA F (Fin n × Fin d),
        e' (M.co.rho B.ψ u Ψ) = e' Ψ := by
      rintro u ⟨z, rfl⟩ Ψ hΨ
      rw [e'_apply, e'_apply, hS.impl _ _ _ hΨ]
      have h1 : actAB (cA σ) ((1 : UA σ X.J), h') (Matrix.vecMulVec (incV F H.x) z) =
          Matrix.vecMulVec (incV F H.x) (mat h' *ᵥ z) := by
        simp only [actAB]
        show (1 : Matrix (Fin n) (Fin n) (AE F E)) * Matrix.vecMulVec (incV F H.x) z * (mat h')ᵀ = _
        rw [Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
      rw [h1, he.inv _ ⟨_, rfl⟩ _ (hS.pres _ _ hΨ)]
    have hadm : ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d), l ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d) := by
      intro l hl
      have a1 := hS₁.adm (1, h'⁻¹) l hl
      have a2 := GlobalTheory.T.hermitian_adapted_plane_constant hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he _ a1
      exact hS.adm (1, h') _ a2
    exact GlobalTheory.T.hermitian_adapted_plane_seesaw hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he e' hmaps hheis
      hinvI hadm
  choose κ hκ using key
  obtain ⟨Φ₀, hΦ₀, hne⟩ := hz
  have uniqS : ∀ a b : ℂ, a • e Φ₀ = b • e Φ₀ → a = b := fun a b hab => smul_left_injective ℂ hne hab
  have hcκ : c = κ h := uniqS _ _ ((hc Φ₀ hΦ₀).symm.trans (hκ h Φ₀ hΦ₀))
  have hκ1 : κ 1 = 1 := by
    refine uniqS _ _ ?_
    rw [← hκ 1 Φ₀ hΦ₀, one_smul, inv_one, show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one,
      Module.End.one_apply, show om₁ (1, 1) = 1 from map_one om₁, Module.End.one_apply]
  have hκmul : ∀ a b, κ (a * b) = κ a * κ b := by
    intro a b
    refine uniqS _ _ ?_
    rw [← hκ (a * b) Φ₀ hΦ₀, mul_inv_rev, hmulX, hmulX₁, Module.End.mul_apply, Module.End.mul_apply,
      hκ a _ (hS.pres _ _ hΦ₀), map_smul, hκ b _ hΦ₀, smul_smul, mul_comm]
  have hκinv : ∀ a, κ a * κ a⁻¹ = 1 := fun a => by rw [← hκmul, mul_inv_cancel, hκ1]
  let cχ : UA σ W.J →* ℂˣ :=
    { toFun := fun a => ⟨κ a, κ a⁻¹, hκinv a, by simpa using hκinv a⁻¹⟩
      map_one' := Units.ext hκ1
      map_mul' := fun a b => Units.ext (hκmul a b) }
  have hχ : ∀ a, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, a) Φ) = (cχ a : ℂ) • om₁ (1, a) (e Φ) := by
    intro a Φ hΦ
    have k := congrArg (om₁ (1, a)) (hκ a Φ hΦ)
    rw [← Module.End.mul_apply, hinvG, Module.End.one_apply, map_smul] at k
    exact k
  have h1 := GlobalTheory.T.hermitian_adapted_plane_transfer hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he ⟨Φ₀, hΦ₀, hne⟩ cχ hχ
  have h2 : (cχ h : ℂ) = 1 := by rw [h1]; rfl
  rw [hcκ]
  exact h2

end GlobalTheory.MixXUW

end

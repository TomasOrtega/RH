import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionPairRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionPairFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbsStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXTorusValue

/- English proof (translation)
Introduce `l hl hinv p t hp φ hφ`. Establish `hl' : l ∘ₗ om g⁻¹ ∈ C.adm κ` using `hs.adm g⁻¹ l hl`. Establish `hgg : ((g⁻¹ : UG c JB) : GL β E).1 * (g : GL β E).1 = 1`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]`. Both sides reduce to the same expression.

Establish `hgg' : (g : GL β E).1 * ((g⁻¹ : UG c JB) : GL β E).1 = 1`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]`. Both sides reduce to the same expression. Establish `hSS : (S : Matrix ν ν E) * ((S⁻¹ : GL ν E) : Matrix ν ν E) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel]`.

Both sides reduce to the same expression. Establish `hgi : ((g⁻¹ : UG c JB) : GL β E).1 * Cy = Cy' * ((S⁻¹ : GL ν E) : Matrix ν ν E)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hg]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Cy' * ((S⁻¹ : GL ν E) : Matrix ν ν E) := by rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]`. Establish `hinv' : ∀ z : Matrix α ν E, ∀ φ ∈ C.sp κ, (l ∘ₗ om g⁻¹) (d.rho ψ (z * Cyᵀ) φ) = (l ∘ₗ om g⁻¹) φ`. Introduce `z φ hφ`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hs.impl g⁻¹ _ φ hφ]`.

Establish `e1 : actB c g⁻¹ (z * Cyᵀ) = (z * ((S⁻¹ : GL ν E) : Matrix ν ν E)ᵀ) * Cy'ᵀ`. Unfold `actB`. Rewrite using `[Matrix.mul_assoc, ← Matrix.transpose_mul, hgi, Matrix.transpose_mul, Matrix.mul_assoc]`. Rewrite using `[e1]`. Conclude with `hinv _ _ (hs.pres _ φ hφ)`.

Establish `hp' : (((g * p * g⁻¹ : UG c JB) : GL β E) : Matrix β β E) * Cy = Cy * ((S * t * S⁻¹ : GL ν E) : Matrix ν ν E)`. Simplify using `only [Subgroup.coe_mul, Units.val_mul]`. Rewrite using `[Matrix.mul_assoc, hgi, ← Matrix.mul_assoc, Matrix.mul_assoc (g : GL β E).1, hp, ← Matrix.mul_assoc, hg]`. Simplify using `only [Matrix.mul_assoc]`. Establish `key` using `hS (l ∘ₗ om g⁻¹) hl' hinv' (g * p * g⁻¹) (S * t * S⁻¹) hp' (om g φ) (hs.pres g φ hφ)`.

Simplify using `only [LinearMap.comp_apply] at key`. Establish `e2 : om g⁻¹ (om (g * p * g⁻¹) (om g φ)) = om p φ`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Use `group`.

Establish `e3 : om g⁻¹ (om g φ) = φ`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Establish `e4 : Matrix.GeneralLinearGroup.det (S * t * S⁻¹) = Matrix.GeneralLinearGroup.det t`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det S), mul_assoc, mul_inv_cancel, mul_one]`. Rewrite `key` using `[e2, e3, e4]`.

Conclude with `key`.
-/
theorem siegelRule_of_conj {R E : Type} [CommRing R] [Invertible (2 : R)] [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ}
    {χ : Eˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy Cy' : Matrix β ν E}
    {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)} (hs : IsSplitting C ψ d (actB c) om)
    (hS : SiegelRule c C ψ ξ JA JB d χ Cy om) (g : UG c JB) (S : GL ν E)
    (hg : ((g : GL β E) : Matrix β β E) * Cy' = Cy * (S : Matrix ν ν E)) :
    SiegelRule c C ψ ξ JA JB d χ Cy' om := by
  intro l hl hinv p t hp φ hφ
  have hl' : l ∘ₗ om g⁻¹ ∈ C.adm κ := hs.adm g⁻¹ l hl
  have hgg : ((g⁻¹ : UG c JB) : GL β E).1 * (g : GL β E).1 = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hgg' : (g : GL β E).1 * ((g⁻¹ : UG c JB) : GL β E).1 = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hSS : (S : Matrix ν ν E) * ((S⁻¹ : GL ν E) : Matrix ν ν E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]; rfl
  have hgi : ((g⁻¹ : UG c JB) : GL β E).1 * Cy = Cy' * ((S⁻¹ : GL ν E) : Matrix ν ν E) := by
    calc ((g⁻¹ : UG c JB) : GL β E).1 * Cy = ((g⁻¹ : UG c JB) : GL β E).1 * (Cy * ((S : Matrix ν ν E) *
          ((S⁻¹ : GL ν E) : Matrix ν ν E))) := by rw [hSS, Matrix.mul_one]
      _ = ((g⁻¹ : UG c JB) : GL β E).1 * ((g : GL β E).1 * Cy') * ((S⁻¹ : GL ν E) : Matrix ν ν E) := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = Cy' * ((S⁻¹ : GL ν E) : Matrix ν ν E) := by rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]
  have hinv' : ∀ z : Matrix α ν E, ∀ φ ∈ C.sp κ, (l ∘ₗ om g⁻¹) (d.rho ψ (z * Cyᵀ) φ) = (l ∘ₗ om g⁻¹) φ := by
    intro z φ hφ
    simp only [LinearMap.comp_apply]
    rw [hs.impl g⁻¹ _ φ hφ]
    have e1 : actB c g⁻¹ (z * Cyᵀ) = (z * ((S⁻¹ : GL ν E) : Matrix ν ν E)ᵀ) * Cy'ᵀ := by
      unfold actB
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hgi, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e1]
    exact hinv _ _ (hs.pres _ φ hφ)
  have hp' : (((g * p * g⁻¹ : UG c JB) : GL β E) : Matrix β β E) * Cy =
      Cy * ((S * t * S⁻¹ : GL ν E) : Matrix ν ν E) := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [Matrix.mul_assoc, hgi, ← Matrix.mul_assoc, Matrix.mul_assoc (g : GL β E).1, hp,
      ← Matrix.mul_assoc, hg]
    simp only [Matrix.mul_assoc]
  have key := hS (l ∘ₗ om g⁻¹) hl' hinv' (g * p * g⁻¹) (S * t * S⁻¹) hp' (om g φ) (hs.pres g φ hφ)
  simp only [LinearMap.comp_apply] at key
  have e2 : om g⁻¹ (om (g * p * g⁻¹) (om g φ)) = om p φ := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2; group
  have e3 : om g⁻¹ (om g φ) = φ := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e4 : Matrix.GeneralLinearGroup.det (S * t * S⁻¹) = Matrix.GeneralLinearGroup.det t := by
    rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det S), mul_assoc, mul_inv_cancel, mul_one]
  rw [e2, e3, e4] at key
  exact key

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he t m hm k hk hne`. Take `⟨-, ⟨d', hd', hsp, dd, omd, hdd, ⟨-, hsd, hsieg⟩, hbox⟩, -⟩` from `hP.weil`. Take `⟨Cy, md, T, g, S, hCy, hmd, hmdT, hdetT, hgS⟩` from `GlobalTheory.T.adapted_plane_restriction_pair_real F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ t m hm`. Take `⟨l, hl, hinv, hfac, φ₁, hφ₁, φ₂, hφ₂, hL⟩` from `GlobalTheory.T.adapted_plane_restriction_pair_finite F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne d' hd' dd hdd`. Establish `hS'` using `siegelRule_of_conj hsd.toIsSplitting hsieg g S hgS`.

Establish `key` using `hS' l hl (fun z φ hφ => by`. Take `⟨y₁, y₂, u, hz⟩` from `hCy z`. Rewrite using `[hz]`. Conclude with `hinv y₁ y₂ u φ hφ) md T hmdT (boxFun φ₁ φ₂)`. Use the proof step `(GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ hφ₁ φ₂ hφ₂)`.

Rewrite `key` using `[hbox m md hmd φ₁ hφ₁ φ₂ hφ₂, hdetT, GlobalTheory.T.modulus_of_norm_eq_abs]`. Establish `h1 : l (boxFun ((om.comp (MonoidHom.inl _ _)) m φ₁) φ₂) = k * l (boxFun φ₁ φ₂)` using `hfac φ₁ hφ₁ _ (hsp.pres m φ₁ hφ₁) φ₂ hφ₂ k (hk φ₁ hφ₁)`. Rewrite `key` using `[h1]`. Establish `h2` using `mul_right_cancel₀ hL key`. Rewrite using `[h2, Fintype.card_fin]`.
-/
theorem torus_value : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (t : (AE F E)ˣ) (m : UA σ X.J), IsLevi (W₁ := X₁) H t 1 m →
        ∀ k : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d), e (om (m, 1) Φ) = k • e Φ) → (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
        k = (χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he t m hm k hk hne
  obtain ⟨-, ⟨d', hd', hsp, dd, omd, hdd, ⟨-, hsd, hsieg⟩, hbox⟩, -⟩ := hP.weil
  obtain ⟨Cy, md, T, g, S, hCy, hmd, hmdT, hdetT, hgS⟩ :=
    GlobalTheory.T.adapted_plane_restriction_pair_real F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ t m hm
  obtain ⟨l, hl, hinv, hfac, φ₁, hφ₁, φ₂, hφ₂, hL⟩ :=
    GlobalTheory.T.adapted_plane_restriction_pair_finite F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne d' hd' dd hdd
  have hS' := siegelRule_of_conj hsd.toIsSplitting hsieg g S hgS
  have key := hS' l hl (fun z φ hφ => by
      obtain ⟨y₁, y₂, u, hz⟩ := hCy z
      rw [hz]; exact hinv y₁ y₂ u φ hφ) md T hmdT (boxFun φ₁ φ₂)
    (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ hφ₁ φ₂ hφ₂)
  rw [hbox m md hmd φ₁ hφ₁ φ₂ hφ₂, hdetT, GlobalTheory.T.modulus_of_norm_eq_abs] at key
  have h1 : l (boxFun ((om.comp (MonoidHom.inl _ _)) m φ₁) φ₂) = k * l (boxFun φ₁ φ₂) :=
    hfac φ₁ hφ₁ _ (hsp.pres m φ₁ hφ₁) φ₂ hφ₂ k (hk φ₁ hφ₁)
  rw [h1] at key
  have h2 := mul_right_cancel₀ hL key
  rw [h2, Fintype.card_fin]

end GlobalTheory.MixXTorusValue

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleEvaluationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairPlaneDescent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvLawBLeft

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun x _ => by ring`.
-/
theorem mul_vecMulVec' {R : Type} [CommRing R] {k l p : ℕ} (A : Matrix (Fin k) (Fin l) R) (y : Fin l → R) (w : Fin p → R) :
    A * Matrix.vecMulVec y w = Matrix.vecMulVec (A *ᵥ y) w := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' hev X om om' om₁ om₁' T T₁`. Establish `P'` using `GlobalTheory.ThK.Inhab.pairV' T`. Establish `P₁'` using `GlobalTheory.ThK.Inhab.pairV' T₁`. Take `⟨Mb, hMb⟩` from `GlobalTheory.ModelEx.model_exists F E σ B T.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ T₁.geo.hV' T.geo.hW`. Take `⟨omb, hwb⟩` from `GlobalTheory.WeilExGen.exists_isWeil hP F E σ B T.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ T₁.geo.hV' T.geo.hW Mb hMb X.α (X.α / X.β) P'.hX P'.hW T₁.chars.resα P'.resW`.

Establish `Pb : IsPair B Mb X.α (X.α / X.β) omb G₁.q (b - G₁.q) _ _` using `⟨T.base, T₁.geo.hV', T.geo.hW, hMb, P'.hX, P'.hW, T₁.chars.resα, P'.resW, hwb⟩`. Take `⟨⟨e₁, he₁⟩, law₁⟩` from `GlobalTheory.T.adapted_plane_first_variable hP F E σ B (b + 2) (a + (b + 2)) G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ P' b G₁.V' H 0 (b + 1) Mb omb _ _ cfg.hH Pb`. Take `⟨e₂, he₂⟩` from `((GlobalTheory.T.theta_evaluation_zero_cone hP).1 F E σ B b (a + (b + 2)) G₁.V' G.W Mb X.α (X.α / X.β) omb _ _ _ _ Pb (a + b) G₁.V' G₁.W H' a (a + b + 1) G₁.M' rfl cfg.hH' T₁.geo.hM').1`. Establish `mapsC : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), (e₂ ∘ₗ e₁) Φ ∈ schA F (Fin b × Fin (a + b))` using `fun Φ hΦ => he₂.maps _ (he₁.maps Φ hΦ)`. Establish `heisC : ∀ z, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M'.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ)`.

Introduce `z Φ hΦ`. Establish `h1` using `he₁.Heisenberg₂ (z * (incM F H'.ι)ᵀ) Φ hΦ`. Establish `h2` using `he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)`. Rewrite `h1` using `[incM_one, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc]`. Rewrite `h2` using `[incM_one, Matrix.one_mul]`.

Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[h1, h2]`. Establish `invC : ∀ u ∈ isoB H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ`. Introduce `u hu Φ hΦ`. Simplify using `only [LinearMap.comp_apply]`.

Break down `hu with hu | ⟨y, rfl⟩` into its components or cases. Rewrite using `[he₁.inv u hu Φ hΦ]`. Establish `h1` using `he₁.Heisenberg₂ (Matrix.vecMulVec y (incV F H'.x)) Φ hΦ`. Rewrite `h1` using `[incM_one, Matrix.transpose_one, Matrix.mul_one, mul_vecMulVec']`. Rewrite using `[h1, he₂.inv _ ⟨y, rfl⟩ _ (he₁.maps Φ hΦ)]`.

Establish `locC : ∃ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b))) (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ), (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) ∧ ∀ f φ, (∀ …`. Take `⟨ei₁, ev₁, -, hv₁, hp₁⟩` from `he₁.loc`. Take `⟨ei₂, ev₂, -, hv₂, hp₂⟩` from `he₂.loc`. Use `⟨ei₂.comp ei₁, fun v => ev₂ v ∘ₗ ev₁ v, fun v => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply]`.

Rewrite using `[(hv₁ v).1, (hv₂ v).1]`. Rewrite using `[Submodule.map_comp, (hv₁ v).2, (hv₂ v).2]`. Introduce `f φ hφ hcof`. Establish `hφ₁ : ∀ v, ev₁ v (φ v) ∈ SB _` using `fun v => (hv₁ v).2 ▸ Submodule.mem_map_of_mem (hφ v)`. Establish `hcof₁ : ∀ᶠ v in cofinite, ev₁ v (φ v) = Mb.vac v` using `hcof.mono fun v hv => by rw [hv, (hv₁ v).1]`.

Simplify using `only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]`. Rewrite using `[hp₁ f φ hφ hcof, hp₂ _ _ hφ₁ hcof₁]`. Take `⟨c, hc⟩` from `GlobalTheory.T.config_b_triple_evaluation_compatible hP F E σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ e' hev (e₂ ∘ₗ e₁) mapsC heisC invC locC`. Take `⟨Φ₀, hΦ₀, hne⟩` from `GlobalTheory.ThK.EvTwoNeB.comp_ne_zero hP F E σ B (b + 2) (a + (b + 2)) b (a + b) G.V' G.W G₁.V' G₁.W G.M' X.α (X.α / X.β) om' _ _ _ _ P' H H' 0 (b + 1) a (a + b + 1) Mb omb _ _ G₁.M' cfg.hH cfg.hH' Pb T₁.geo.hM' e₁ e₂ he₁ he₂`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Apply `hne` to reduce the goal to its premises. Use `hc Φ₀ hΦ₀` as an intermediate fact. Rewrite `this` using `[zero_smul, LinearMap.comp_apply]`. Conclude with `this`.

Establish `hLW : IsLevi (W₁` using `G₁.W) H' 1 (1 : UA σ G₁.W.J) (1 : UA σ G.W.J) := by`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (1 : Matrix _ _ _) *ᵥ _ = _`. Simplify using the standard rewrite rules. Use `show (1 : Matrix _ _ _) *ᵥ _ = _`.

Simplify using the standard rewrite rules. Use `show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)`. Simplify using the standard rewrite rules. Establish `hLX : IsLevi (W₁` using `G₁.V') H 1 (1 : UA σ G₁.V'.J) (1 : UA σ G.V'.J) := by`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show (1 : Matrix _ _ _) *ᵥ _ = _`. Simplify using the standard rewrite rules. Use `show (1 : Matrix _ _ _) *ᵥ _ = _`. Simplify using the standard rewrite rules. Use `show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)`.

Simplify using the standard rewrite rules. Establish `hpres : ∀ x, ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), om' x Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))` using `fun x Ψ hΨ => (T.weil'.isUSplitting).pres _ _ hΨ`. Use `⟨fun u hu Ψ hΨ => ?_, fun t g₀ g hL Ψ hΨ => ?_⟩` and prove the remaining obligations. Establish `h1` using `law₁ e₁ he₁ 1 1 1 1 hLX u hu Ψ hΨ`. Establish `hone : omb (1, 1) = 1` using `map_one omb`.

Rewrite `h1` using `[mul_one, hone, Module.End.one_apply]`. Simplify using `only [map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one, one_smul] at h1`. Establish `key : (e₂ ∘ₗ e₁) (om' (u, 1) Ψ) = (e₂ ∘ₗ e₁) Ψ`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[h1]`.

Rewrite `key` using `[hc _ (hpres _ _ hΨ), hc _ hΨ]`. Conclude with `smul_right_injective _ hc0 key`. Establish `h1` using `law₁ e₁ he₁ 1 t g₀ g hL 1 (Subgroup.one_mem _) Ψ hΨ`. Establish `h2` using `GlobalTheory.T.adapted_plane_second_variable hP F E σ B b (a + (b + 2)) G₁.V' G.W Mb X.α (X.α / X.β) omb _ _ _ _ Pb (a + b) G₁.W H' a (a + b + 1) G₁.M' om₁' _ _ cfg.hH' P₁' e₂ he₂ g₀ 1 1 1 hLW 1 (Subgroup.one_mem _) (e₁ Ψ) (he₁.maps Ψ hΨ)`. Simplify using `only [one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at h1 h2`.

Establish `key : (e₂ ∘ₗ e₁) (om' (g, 1) Ψ) = fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t • om₁' (g₀, 1) ((e₂ ∘ₗ e₁) Ψ)`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[h1, map_smul, h2]`. Both sides reduce to the same expression. Rewrite `key` using `[hc _ (hpres _ _ hΨ), hc _ hΨ, map_smul, smul_comm _ c]`.

Conclude with `smul_right_injective _ hc0 key`.
-/
theorem globalLaw : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    (∀ u ∈ unip σ G.V' H, ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e' (om' (u, 1) Ψ) = e' Ψ) ∧
    ∀ t g₀ g, IsLevi H t g₀ g → ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      e' (om' (g, 1) Ψ) = fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t • om₁' (g₀, 1) (e' Ψ) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' hev X om om' om₁ om₁' T T₁
  have P' := GlobalTheory.ThK.Inhab.pairV' T
  have P₁' := GlobalTheory.ThK.Inhab.pairV' T₁
  obtain ⟨Mb, hMb⟩ := GlobalTheory.ModelEx.model_exists F E σ B T.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ T₁.geo.hV' T.geo.hW
  obtain ⟨omb, hwb⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B T.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ T₁.geo.hV' T.geo.hW Mb hMb
    X.α (X.α / X.β) P'.hX P'.hW T₁.chars.resα P'.resW
  have Pb : IsPair B Mb X.α (X.α / X.β) omb G₁.q (b - G₁.q) _ _ :=
    ⟨T.base, T₁.geo.hV', T.geo.hW, hMb, P'.hX, P'.hW, T₁.chars.resα, P'.resW, hwb⟩
  obtain ⟨⟨e₁, he₁⟩, law₁⟩ := GlobalTheory.T.adapted_plane_first_variable hP F E σ B (b + 2) (a + (b + 2)) G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ P'
    b G₁.V' H 0 (b + 1) Mb omb _ _ cfg.hH Pb
  obtain ⟨e₂, he₂⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hP).1 F E σ B b (a + (b + 2)) G₁.V' G.W Mb X.α (X.α / X.β) omb _ _ _ _ Pb
    (a + b) G₁.V' G₁.W H' a (a + b + 1) G₁.M' rfl cfg.hH' T₁.geo.hM').1
  have mapsC : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), (e₂ ∘ₗ e₁) Φ ∈ schA F (Fin b × Fin (a + b)) :=
    fun Φ hΦ => he₂.maps _ (he₁.maps Φ hΦ)
  have heisC : ∀ z, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M'.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ) := by
    intro z Φ hΦ
    have h1 := he₁.Heisenberg₂ (z * (incM F H'.ι)ᵀ) Φ hΦ
    have h2 := he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)
    rw [incM_one, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc] at h1
    rw [incM_one, Matrix.one_mul] at h2
    simp only [LinearMap.comp_apply]
    rw [h1, h2]
  have invC : ∀ u ∈ isoB H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ := by
    intro u hu Φ hΦ
    simp only [LinearMap.comp_apply]
    rcases hu with hu | ⟨y, rfl⟩
    · rw [he₁.inv u hu Φ hΦ]
    · have h1 := he₁.Heisenberg₂ (Matrix.vecMulVec y (incV F H'.x)) Φ hΦ
      rw [incM_one, Matrix.transpose_one, Matrix.mul_one, mul_vecMulVec'] at h1
      rw [h1, he₂.inv _ ⟨y, rfl⟩ _ (he₁.maps Φ hΦ)]
  have locC : ∃ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
      (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
        (e₂ ∘ₗ e₁) (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
    obtain ⟨ei₁, ev₁, -, hv₁, hp₁⟩ := he₁.loc
    obtain ⟨ei₂, ev₂, -, hv₂, hp₂⟩ := he₂.loc
    refine ⟨ei₂.comp ei₁, fun v => ev₂ v ∘ₗ ev₁ v, fun v => ⟨?_, ?_⟩, ?_⟩
    · simp only [LinearMap.comp_apply]
      rw [(hv₁ v).1, (hv₂ v).1]
    · rw [Submodule.map_comp, (hv₁ v).2, (hv₂ v).2]
    · intro f φ hφ hcof
      have hφ₁ : ∀ v, ev₁ v (φ v) ∈ SB _ := fun v => (hv₁ v).2 ▸ Submodule.mem_map_of_mem (hφ v)
      have hcof₁ : ∀ᶠ v in cofinite, ev₁ v (φ v) = Mb.vac v := hcof.mono fun v hv => by rw [hv, (hv₁ v).1]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      rw [hp₁ f φ hφ hcof, hp₂ _ _ hφ₁ hcof₁]
  obtain ⟨c, hc⟩ := GlobalTheory.T.config_b_triple_evaluation_compatible hP F E σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ e' hev (e₂ ∘ₗ e₁)
    mapsC heisC invC locC
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.ThK.EvTwoNeB.comp_ne_zero hP F E σ B (b + 2) (a + (b + 2)) b (a + b) G.V' G.W G₁.V' G₁.W G.M'
    X.α (X.α / X.β) om' _ _ _ _ P' H H' 0 (b + 1) a (a + b + 1) Mb omb _ _ G₁.M' cfg.hH cfg.hH' Pb T₁.geo.hM' e₁ e₂ he₁ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    rw [zero_smul, LinearMap.comp_apply] at this
    exact this
  have hLW : IsLevi (W₁ := G₁.W) H' 1 (1 : UA σ G₁.W.J) (1 : UA σ G.W.J) := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp
  have hLX : IsLevi (W₁ := G₁.V') H 1 (1 : UA σ G₁.V'.J) (1 : UA σ G.V'.J) := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), om' x Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) :=
    fun x Ψ hΨ => (T.weil'.isUSplitting).pres _ _ hΨ
  refine ⟨fun u hu Ψ hΨ => ?_, fun t g₀ g hL Ψ hΨ => ?_⟩
  · have h1 := law₁ e₁ he₁ 1 1 1 1 hLX u hu Ψ hΨ
    have hone : omb (1, 1) = 1 := map_one omb
    rw [mul_one, hone, Module.End.one_apply] at h1
    simp only [map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one, one_smul] at h1
    have key : (e₂ ∘ₗ e₁) (om' (u, 1) Ψ) = (e₂ ∘ₗ e₁) Ψ := by
      simp only [LinearMap.comp_apply]
      rw [h1]
    rw [hc _ (hpres _ _ hΨ), hc _ hΨ] at key
    exact smul_right_injective _ hc0 key
  · have h1 := law₁ e₁ he₁ 1 t g₀ g hL 1 (Subgroup.one_mem _) Ψ hΨ
    have h2 := GlobalTheory.T.adapted_plane_second_variable hP F E σ B b (a + (b + 2)) G₁.V' G.W Mb X.α (X.α / X.β) omb _ _ _ _ Pb (a + b) G₁.W H'
      a (a + b + 1) G₁.M' om₁' _ _ cfg.hH' P₁' e₂ he₂ g₀ 1 1 1 hLW 1 (Subgroup.one_mem _) (e₁ Ψ) (he₁.maps Ψ hΨ)
    simp only [one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at h1 h2
    have key : (e₂ ∘ₗ e₁) (om' (g, 1) Ψ) = fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t • om₁' (g₀, 1) ((e₂ ∘ₗ e₁) Ψ) := by
      simp only [LinearMap.comp_apply]
      rw [h1, map_smul, h2]
      rfl
    rw [hc _ (hpres _ _ hΨ), hc _ hΨ, map_smul, smul_comm _ c] at key
    exact smul_right_injective _ hc0 key

end GlobalTheory.ThK.EvLawBLeft

namespace GlobalTheory.ThK.EvLawBLeft

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f M.vac (fun v => (hM.vac v).1) hM.std⟩` and prove the remaining obligations. Establish `hz0 : ∀ v i, evFin F v (z i) = 0`. Introduce `v i`. Use `set u : AF F := (0, 1) with hu`. Establish `h1` using `congrFun (hz u GlobalTheory.ArchLocality.evI_fin) i`.

Establish `h2 : evFin F v u = 1` using `map_one (evFin F v)`. Establish `h3` using `congrArg (evFin F v) h1`. Simplify using `only [Pi.zero_apply, map_zero] at h3`. Express the relevant statement in the definitionally equal form `evFin F v (u * z i) = 0 at h3`. Rewrite `h3` using `[map_mul, h2, one_mul]`.

Conclude with `h3`. Simplify using `only [Pi.add_apply, map_add, hz0, add_zero]`.
-/
theorem rest_vac {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ)
    (f : SInf F (Fin n × Fin d)) :
    Rest (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (fun x => ∏ᶠ v, M.vac v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f M.vac (fun v => (hM.vac v).1) hM.std⟩
  have hz0 : ∀ v i, evFin F v (z i) = 0 := by
    intro v i
    set u : AF F := (0, 1) with hu
    have h1 := congrFun (hz u GlobalTheory.ArchLocality.evI_fin) i
    have h2 : evFin F v u = 1 := map_one (evFin F v)
    have h3 := congrArg (evFin F v) h1
    simp only [Pi.zero_apply, map_zero] at h3
    change evFin F v (u * z i) = 0 at h3
    rw [map_mul, h2, one_mul] at h3
    exact h3
  simp only [Pi.add_apply, map_add, hz0, add_zero]

/- English proof (translation)
Use `DFunLike.ext _ _ fun x => ?_` and prove the remaining obligations. Establish `key` using `GlobalTheory.ThK.PureTensIndep.sum_local_eq_zero M.vac (fun v => (hM.vac v).2.1) hM.std ∅ ![A - C] ![M.vac] (fun i v _ => by fin_cases i; rfl) ?_ x (fun _ _ => 0)`. Simplify `key` using `[sub_eq_zero]`. Simplify using `only [Fin.sum_univ_one, Matrix.cons_val_zero]`. Use function extensionality and compare the values at `y`.

Establish `e` using `congrFun h y`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure] at e`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, SchwartzMap.sub_apply]`. Rewrite using `[sub_mul, e, sub_self]`.
-/
theorem eq_of_pure_vac {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    (hM : M.IsGood ψ) {A C : SInf F (Fin n × Fin d)} (h : pure A M.vac = pure C M.vac) : A = C := by
  refine DFunLike.ext _ _ fun x => ?_
  have key := GlobalTheory.ThK.PureTensIndep.sum_local_eq_zero M.vac (fun v => (hM.vac v).2.1) hM.std ∅ ![A - C] ![M.vac]
    (fun i v _ => by fin_cases i; rfl) ?_ x (fun _ _ => 0)
  · simpa [sub_eq_zero] using key
  · simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    funext y
    have e := congrFun h y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure] at e
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, SchwartzMap.sub_apply]
    rw [sub_mul, e, sub_self]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' hev ei' ev' hloc X om om' om₁ om₁' T T₁`. Take `⟨hU, hL⟩` from `globalLaw hP F E σ B a b G G₁ H H' cfg e' hev X om om' om₁ om₁' T T₁`. Establish `hM'` using `T.geo.hM'`. Establish `hM₁'` using `T₁.geo.hM'`. Establish `hex` using `GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ (b + 2) (a + (b + 2)) G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' T.base.cm T.base.std T.weil'`.

Establish `hex₁` using `GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ b (a + b) G₁.V' G₁.W G₁.M' B.ψ X.α (X.α / X.β) om₁' T₁.base.cm T₁.base.std T₁.weil'`. Take `⟨-, hvac, hpure⟩` from `hloc`. Establish `hE : ∀ f, e' (pure f G.M'.vac) = pure (ei' f) G₁.M'.vac`. Introduce `f`. Rewrite using `[hpure f G.M'.vac (fun v => (hM'.vac v).1) (Eventually.of_forall fun _ => rfl)]`.

Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `(hvac v).1`. Establish `hA : ∀ g ∈ UAt σ G.V' (evI F), ∀ f, om' (g, 1) (pure f G.M'.vac) = pure (locOpInf (om' (g, 1)) f) G.M'.vac` using `fun g hg f => acts_locOpInf (hex g hg f) _ (rest_vac hM' f)`. Establish `hA₁ : ∀ g₀ ∈ UAt σ G₁.V' (evI F), ∀ f, om₁' (g₀, 1) (pure f G₁.M'.vac) = pure (locOpInf (om₁' (g₀, 1)) f) G₁.M'.vac` using `fun g hg f => acts_locOpInf (hex₁ g hg f) _ (rest_vac hM₁' f)`.

Establish `hS : ∀ f, pure f G.M'.vac ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))` using `fun f => (rest_vac hM' f).2`. Use `⟨fun u hu huI f => ?_, fun t g₀ g hLv hg hg₀ f => ?_⟩` and prove the remaining obligations. Apply `eq_of_pure_vac hM₁'` to reduce the goal to its premises. Rewrite using `[← hE, ← hE, ← hA u huI f, hU u hu _ (hS f)]`. Apply `eq_of_pure_vac hM₁'` to reduce the goal to its premises.

Rewrite using `[← hE, ← hA g hg f, hL t g₀ g hLv _ (hS f), hE, hA₁ g₀ hg₀]`. Use function extensionality and compare the values at `y`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem infLaw : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      (∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evI F) → ∀ f, ei' (locOpInf (om' (u, 1)) f) = ei' f) ∧
      ∀ t g₀ g, IsLevi H t g₀ g → g ∈ UAt σ G.V' (evI F) → g₀ ∈ UAt σ G₁.V' (evI F) → ∀ f,
        ei' (locOpInf (om' (g, 1)) f) = fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t • locOpInf (om₁' (g₀, 1)) (ei' f) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' hev ei' ev' hloc X om om' om₁ om₁' T T₁
  obtain ⟨hU, hL⟩ := globalLaw hP F E σ B a b G G₁ H H' cfg e' hev X om om' om₁ om₁' T T₁
  have hM' := T.geo.hM'
  have hM₁' := T₁.geo.hM'
  have hex := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ (b + 2) (a + (b + 2)) G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' T.base.cm T.base.std
    T.weil'
  have hex₁ := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ b (a + b) G₁.V' G₁.W G₁.M' B.ψ X.α (X.α / X.β) om₁' T₁.base.cm T₁.base.std
    T₁.weil'
  obtain ⟨-, hvac, hpure⟩ := hloc
  have hE : ∀ f, e' (pure f G.M'.vac) = pure (ei' f) G₁.M'.vac := by
    intro f
    rw [hpure f G.M'.vac (fun v => (hM'.vac v).1) (Eventually.of_forall fun _ => rfl)]
    congr 1
    funext v
    exact (hvac v).1
  have hA : ∀ g ∈ UAt σ G.V' (evI F), ∀ f,
      om' (g, 1) (pure f G.M'.vac) = pure (locOpInf (om' (g, 1)) f) G.M'.vac :=
    fun g hg f => acts_locOpInf (hex g hg f) _ (rest_vac hM' f)
  have hA₁ : ∀ g₀ ∈ UAt σ G₁.V' (evI F), ∀ f,
      om₁' (g₀, 1) (pure f G₁.M'.vac) = pure (locOpInf (om₁' (g₀, 1)) f) G₁.M'.vac :=
    fun g hg f => acts_locOpInf (hex₁ g hg f) _ (rest_vac hM₁' f)
  have hS : ∀ f, pure f G.M'.vac ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := fun f => (rest_vac hM' f).2
  refine ⟨fun u hu huI f => ?_, fun t g₀ g hLv hg hg₀ f => ?_⟩
  · apply eq_of_pure_vac hM₁'
    rw [← hE, ← hE, ← hA u huI f, hU u hu _ (hS f)]
  · apply eq_of_pure_vac hM₁'
    rw [← hE, ← hA g hg f, hL t g₀ g hLv _ (hS f), hE, hA₁ g₀ hg₀]
    funext y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.ThK.EvLawBLeft

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicSubScalarMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentRadicalEqLeviMulUnipotentStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.CuspCompLin

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n J hJ r X Y hW K S φ₁ φ₂ a₁ a₂ z h1 h2 H1 H2`. Take `⟨hc1, c₁, hC1, hs1⟩` from `H1`. Take `⟨hc2, c₂, hC2, hs2⟩` from `H2`. Establish `hcoc : ∀ T : Finset (Fin r), GlobalTheory.Cusp.Cocompact (ratPts σ J) (GlobalTheory.StdPar.unip σ J X T)` using `GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hcm n J hJ r X Y hW`. Establish `hdec : ∀ T T' : Finset (Fin r), T ⊆ T' → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T' → ∃ m ∈ ratPts σ J, m ∈ GlobalTheory.StdPar.levi σ J X Y T ∧ ∃ ν ∈ GlobalTheory.StdPar.unip σ J X T, γ = m * ν` using `GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent F E σ hcm n J hJ r X Y hW`.

Establish `hint : ∀ (T : Finset (Fin r)) (f : GAd σ J → ℂ), Continuous f → (∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T → ∀ g, f (γ * g) = f g) → ∀ (μ : Measure (GlobalTheory.StdPar.unip σ J X T)) (𝓕 : Set (GlobalTheory.StdPar.unip σ J X T)), μ.IsHaarMeasure → IsFundamentalDomain …`. Introduce `T f hf hfi μ 𝓕 hμ h𝓕 g`. Take `⟨C, hC, hcov⟩` from `hcoc T`. Conclude with `GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ _ C hC hcov μ hμ 𝓕 h𝓕 _ (by fun_prop) fun γ hγ u => by`. Simplify using `only [Subgroup.coe_mul, mul_assoc]`.

Conclude with `hfi _ (Subgroup.mem_subgroupOf.1 hγ) γ.2 _`. Establish `hcusp : ∀ (T : Finset (Fin r)) (a : GAd σ J → ℂ), S ⊆ T → GlobalTheory.StdPar.IsAutOn σ J X Y S K a → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T → ∀ g, a (γ * g) = a g`. Introduce `T a hT ha γ hγ hγT g`. Take `⟨m, hm, hmL, ν, hν, rfl⟩` from `hdec S T hT γ hγ hγT`. Rewrite using `[mul_assoc, ha.leftM m hm hmL, ha.leftN ν hν]`.

Establish `hrat : ∀ a : GAd σ J → ℂ, GlobalTheory.StdPar.IsAutOn σ J X Y ∅ K a → ∀ γ ∈ ratPts σ J, ∀ g, a (γ * g) = a g` using `fun a ha γ hγ g => ha.leftM γ hγ (by simp) g`. Use `⟨⟨GlobalTheory.T.automorphic_sub_scalar_mul F E σ n J r X Y S K a₁ a₂ z hc1.1 hc2.1, fun T hT μ 𝓕 hμ h𝓕 hone g => ?_⟩, fun g => c₁ g - z * c₂ g, fun μ 𝓕 hμ h𝓕 hone g => ?_, fun ψ hψ μ 𝓕 hμ h𝓕 g g' => ?_⟩` and prove the remaining obligations. Establish `e1` using `hc1.2 T hT μ 𝓕 hμ h𝓕 hone g`. Establish `e2` using `hc2.2 T hT μ 𝓕 hμ h𝓕 hone g`. Establish `i1` using `hint T a₁ hc1.1.cont (hcusp T a₁ hT.1 hc1.1) μ 𝓕 hμ h𝓕 g`.

Establish `i2` using `hint T a₂ hc2.1.cont (hcusp T a₂ hT.1 hc2.1) μ 𝓕 hμ h𝓕 g`. Simplify using `only [Pi.zero_apply] at e1 e2 ⊢`. Rewrite using `[integral_sub i1 (i2.const_mul z), integral_const_mul, ← e1, ← e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1` using `hC1 μ 𝓕 hμ h𝓕 hone g`.

Establish `e2` using `hC2 μ 𝓕 hμ h𝓕 hone g`. Establish `i1` using `hint S φ₁ h1.cont (fun γ hγ _ => hrat φ₁ h1 γ hγ) μ 𝓕 hμ h𝓕 g`. Establish `i2` using `hint S φ₂ h2.cont (fun γ hγ _ => hrat φ₂ h2 γ hγ) μ 𝓕 hμ h𝓕 g`. Rewrite using `[integral_sub i1 (i2.const_mul z), integral_const_mul, ← e1, ← e2]`. Take `⟨i1, j1, e1⟩` from `hs1 ψ hψ μ 𝓕 hμ h𝓕 g g'`.

Take `⟨i2, j2, e2⟩` from `hs2 ψ hψ μ 𝓕 hμ h𝓕 g g'`. Establish `k1` using `i1.sub (i2.const_mul z)`. Establish `k2` using `j1.sub (j2.const_mul z)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `k1.congr (Filter.Eventually.of_forall fun m => by simp only [Pi.sub_apply]; ring)`.

Conclude with `k2.congr (Filter.Eventually.of_forall fun m => by simp only [Pi.sub_apply]; ring)`. Establish `l : ∫ m in 𝓕, (c₁ ((m : GAd σ J) * g) - z * c₂ ((m : GAd σ J) * g)) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ = (∫ m in 𝓕, c₁ ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ) - z * ∫ m in 𝓕, c₂ ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂ …`. Rewrite using `[← integral_const_mul, ← integral_sub i1 (i2.const_mul z)]`. Use `congr 1`. Use function extensionality and compare the values at `m`.

Expand and normalize the polynomial expressions, which then agree. Establish `r : ∫ m in 𝓕, (a₁ ((m : GAd σ J) * g) - z * a₂ ((m : GAd σ J) * g)) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ = (∫ m in 𝓕, a₁ ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ) - z * ∫ m in 𝓕, a₂ ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂ …`. Rewrite using `[← integral_const_mul, ← integral_sub j1 (j2.const_mul z)]`. Use `congr 1`. Use function extensionality and compare the values at `m`.

Expand and normalize the polynomial expressions, which then agree. Use `show ∫ m in 𝓕, (c₁ ((m : GAd σ J) * g) - z * c₂ ((m : GAd σ J) * g)) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ = ∫ m in 𝓕, (a₁ ((m : GAd σ J) * g) - z * a₂ ((m : GAd σ J) * g)) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ`. Rewrite using `[l, r, e1, e2]`.
-/
theorem isCuspComp_sub : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (K : Subgroup (GAd σ J)) (S : Finset (Fin r)) (φ₁ φ₂ a₁ a₂ : GAd σ J → ℂ) (z : ℂ),
        GlobalTheory.StdPar.IsAutOn σ J X Y ∅ K φ₁ → GlobalTheory.StdPar.IsAutOn σ J X Y ∅ K φ₂ →
        GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ₁ a₁ → GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ₂ a₂ →
        GlobalTheory.StdPar.IsCuspComp σ J X Y S K (fun g => φ₁ g - z * φ₂ g) (fun g => a₁ g - z * a₂ g) := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW K S φ₁ φ₂ a₁ a₂ z h1 h2 H1 H2
  obtain ⟨hc1, c₁, hC1, hs1⟩ := H1
  obtain ⟨hc2, c₂, hC2, hs2⟩ := H2
  have hcoc : ∀ T : Finset (Fin r), GlobalTheory.Cusp.Cocompact (ratPts σ J) (GlobalTheory.StdPar.unip σ J X T) :=
    GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hcm n J hJ r X Y hW
  have hdec : ∀ T T' : Finset (Fin r), T ⊆ T' → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T' →
      ∃ m ∈ ratPts σ J, m ∈ GlobalTheory.StdPar.levi σ J X Y T ∧ ∃ ν ∈ GlobalTheory.StdPar.unip σ J X T, γ = m * ν :=
    GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent F E σ hcm n J hJ r X Y hW
  have hint : ∀ (T : Finset (Fin r)) (f : GAd σ J → ℂ), Continuous f →
      (∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T → ∀ g, f (γ * g) = f g) →
      ∀ (μ : Measure (GlobalTheory.StdPar.unip σ J X T)) (𝓕 : Set (GlobalTheory.StdPar.unip σ J X T)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.unip σ J X T)) 𝓕 μ → ∀ g,
      IntegrableOn (fun u : GlobalTheory.StdPar.unip σ J X T => f ((u : GAd σ J) * g)) 𝓕 μ := by
    intro T f hf hfi μ 𝓕 hμ h𝓕 g
    obtain ⟨C, hC, hcov⟩ := hcoc T
    exact GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ _ C hC hcov μ hμ 𝓕 h𝓕 _ (by fun_prop) fun γ hγ u => by
      simp only [Subgroup.coe_mul, mul_assoc]
      exact hfi _ (Subgroup.mem_subgroupOf.1 hγ) γ.2 _
  have hcusp : ∀ (T : Finset (Fin r)) (a : GAd σ J → ℂ), S ⊆ T → GlobalTheory.StdPar.IsAutOn σ J X Y S K a →
      ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T → ∀ g, a (γ * g) = a g := by
    intro T a hT ha γ hγ hγT g
    obtain ⟨m, hm, hmL, ν, hν, rfl⟩ := hdec S T hT γ hγ hγT
    rw [mul_assoc, ha.leftM m hm hmL, ha.leftN ν hν]
  have hrat : ∀ a : GAd σ J → ℂ, GlobalTheory.StdPar.IsAutOn σ J X Y ∅ K a → ∀ γ ∈ ratPts σ J, ∀ g, a (γ * g) = a g :=
    fun a ha γ hγ g => ha.leftM γ hγ (by simp) g
  refine ⟨⟨GlobalTheory.T.automorphic_sub_scalar_mul F E σ n J r X Y S K a₁ a₂ z hc1.1 hc2.1, fun T hT μ 𝓕 hμ h𝓕 hone g => ?_⟩,
    fun g => c₁ g - z * c₂ g, fun μ 𝓕 hμ h𝓕 hone g => ?_, fun ψ hψ μ 𝓕 hμ h𝓕 g g' => ?_⟩
  · have e1 := hc1.2 T hT μ 𝓕 hμ h𝓕 hone g
    have e2 := hc2.2 T hT μ 𝓕 hμ h𝓕 hone g
    have i1 := hint T a₁ hc1.1.cont (hcusp T a₁ hT.1 hc1.1) μ 𝓕 hμ h𝓕 g
    have i2 := hint T a₂ hc2.1.cont (hcusp T a₂ hT.1 hc2.1) μ 𝓕 hμ h𝓕 g
    simp only [Pi.zero_apply] at e1 e2 ⊢
    rw [integral_sub i1 (i2.const_mul z), integral_const_mul, ← e1, ← e2]
    ring
  · have e1 := hC1 μ 𝓕 hμ h𝓕 hone g
    have e2 := hC2 μ 𝓕 hμ h𝓕 hone g
    have i1 := hint S φ₁ h1.cont (fun γ hγ _ => hrat φ₁ h1 γ hγ) μ 𝓕 hμ h𝓕 g
    have i2 := hint S φ₂ h2.cont (fun γ hγ _ => hrat φ₂ h2 γ hγ) μ 𝓕 hμ h𝓕 g
    rw [integral_sub i1 (i2.const_mul z), integral_const_mul, ← e1, ← e2]
  · obtain ⟨i1, j1, e1⟩ := hs1 ψ hψ μ 𝓕 hμ h𝓕 g g'
    obtain ⟨i2, j2, e2⟩ := hs2 ψ hψ μ 𝓕 hμ h𝓕 g g'
    have k1 := i1.sub (i2.const_mul z)
    have k2 := j1.sub (j2.const_mul z)
    refine ⟨?_, ?_, ?_⟩
    · exact k1.congr (Filter.Eventually.of_forall fun m => by simp only [Pi.sub_apply]; ring)
    · exact k2.congr (Filter.Eventually.of_forall fun m => by simp only [Pi.sub_apply]; ring)
    · have l : ∫ m in 𝓕, (c₁ ((m : GAd σ J) * g) - z * c₂ ((m : GAd σ J) * g)) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ =
          (∫ m in 𝓕, c₁ ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ) -
            z * ∫ m in 𝓕, c₂ ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ := by
        rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul z)]
        congr 1
        funext m
        ring
      have r : ∫ m in 𝓕, (a₁ ((m : GAd σ J) * g) - z * a₂ ((m : GAd σ J) * g)) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ =
          (∫ m in 𝓕, a₁ ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ) -
            z * ∫ m in 𝓕, a₂ ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ := by
        rw [← integral_const_mul, ← integral_sub j1 (j2.const_mul z)]
        congr 1
        funext m
        ring
      show ∫ m in 𝓕, (c₁ ((m : GAd σ J) * g) - z * c₂ ((m : GAd σ J) * g)) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ =
        ∫ m in 𝓕, (a₁ ((m : GAd σ J) * g) - z * a₂ ((m : GAd σ J) * g)) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ
      rw [l, r, e1, e2]

end GlobalTheory.CuspCompLin

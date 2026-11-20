import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateOpenSubgroupsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingOpenSubgroupsFiniteStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKEvAdm

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hev l hl g hg`. Take `⟨ei, ev, -, hvac, hpure⟩` from `hev.loc`. Take `⟨Bx, hBo, hBs, hBe, hinv⟩` from `GlobalTheory.T.exists_open_subgroups_integers F _ g hg`. Take `⟨R, hR⟩` from `GlobalTheory.T.scaling_open_subgroups_finite F _ Bx hBo hBs hBe g hg.2 hinv`. Set `φ : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → v.adicCompletion F) → ℂ` to `fun r v => Set.indicator {x : Fin n × Fin d → v.adicCompletion F | ∀ i, x i - evalV F v (r i) ∈ Bx v} 1`.

Establish `hφSB : ∀ r v, φ r v ∈ SB _` using `fun r => (GlobalTheory.T.translate_open_subgroups_finite F _ Bx hBo hBs hBe r).1`. Establish `hφvac : ∀ r, ∀ᶠ v in cofinite, φ r v = M.vac v` using `fun r => by filter_upwards [(GlobalTheory.T.translate_open_subgroups_finite F _ Bx hBo hBs hBe r).2, hM.std] with v h1 h2`. Conclude with `h1.trans h2.symm`. Set `ψ : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ∀ v : HeightOneSpectrum (𝓞 F), (Fin n₁ × Fin d₁ → v.adicCompletion F) → ℂ` to `fun r v => ev v (φ r v)`. Establish `hψSB : ∀ r v, ψ r v ∈ SB _` using `fun r v => by`.

Rewrite using `[← (hvac v).2]`. Conclude with `Submodule.mem_map_of_mem (hφSB r v)`. Establish `hψint : ∀ r, ∀ᶠ v in cofinite, ψ r v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1` using `fun r => by filter_upwards [hφvac r, hM₁.std] with v h1 h2 show ev v (φ r v) = _`. Rewrite using `[h1, (hvac v).1, h2]`. Set `g' : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) → ℂ` to `fun r y => ∏ᶠ v, ψ r v fun i => evalV F v (y i)`.

Establish `hg'SB : ∀ r, g' r ∈ SB _` using `fun r => GlobalTheory.T.restricted_product_mem_schwartz F _ (ψ r) (hψSB r) (hψint r)`. Establish `hT : ∀ r, ∃ T : SchwartzMap (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f (g' r)) = T f` using `fun r => hl (g' r) (hg'SB r)`. Use `choose T hT using hT`. Establish `key : ∀ f : SInf F (Fin n × Fin d), pureA F f g = ∑ r ∈ R, g r • pure f (φ r)`. Introduce `f`.

Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply]`. Use `conv_lhs => rw [hR]`. Simplify using `only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_left_comm]`. Both sides reduce to the same expression. Establish `key2 : ∀ (f : SInf F (Fin n₁ × Fin d₁)) r, pure f (ψ r) = pureA F f (g' r)` using `fun f r => rfl`. Use `⟨∑ r ∈ R, g r • (T r).comp ei, fun f => ?_⟩` and prove the remaining obligations. Establish `hL : l (e (pureA F (⇑f) g)) = ∑ r ∈ R, g r * T r (ei f)`.

Rewrite using `[key, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, hpure f (φ r) (hφSB r) (hφvac r), key2, hT, smul_eq_mul]`. Rewrite using `[LinearMap.comp_apply, hL, ContinuousLinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Both sides reduce to the same expression.
-/
theorem comp_mem_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hev l hl g hg
  classical
  obtain ⟨ei, ev, -, hvac, hpure⟩ := hev.loc
  obtain ⟨Bx, hBo, hBs, hBe, hinv⟩ := GlobalTheory.T.exists_open_subgroups_integers F _ g hg
  obtain ⟨R, hR⟩ := GlobalTheory.T.scaling_open_subgroups_finite F _ Bx hBo hBs hBe g hg.2 hinv
  let φ : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ∀ v : HeightOneSpectrum (𝓞 F),
      (Fin n × Fin d → v.adicCompletion F) → ℂ :=
    fun r v => Set.indicator {x : Fin n × Fin d → v.adicCompletion F | ∀ i, x i - evalV F v (r i) ∈ Bx v} 1
  have hφSB : ∀ r v, φ r v ∈ SB _ := fun r => (GlobalTheory.T.translate_open_subgroups_finite F _ Bx hBo hBs hBe r).1
  have hφvac : ∀ r, ∀ᶠ v in cofinite, φ r v = M.vac v := fun r => by
    filter_upwards [(GlobalTheory.T.translate_open_subgroups_finite F _ Bx hBo hBs hBe r).2, hM.std] with v h1 h2
    exact h1.trans h2.symm
  let ψ : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ∀ v : HeightOneSpectrum (𝓞 F),
      (Fin n₁ × Fin d₁ → v.adicCompletion F) → ℂ :=
    fun r v => ev v (φ r v)
  have hψSB : ∀ r v, ψ r v ∈ SB _ := fun r v => by
    rw [← (hvac v).2]; exact Submodule.mem_map_of_mem (hφSB r v)
  have hψint : ∀ r, ∀ᶠ v in cofinite,
      ψ r v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun r => by
    filter_upwards [hφvac r, hM₁.std] with v h1 h2
    show ev v (φ r v) = _
    rw [h1, (hvac v).1, h2]
  let g' : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    fun r y => ∏ᶠ v, ψ r v fun i => evalV F v (y i)
  have hg'SB : ∀ r, g' r ∈ SB _ := fun r => GlobalTheory.T.restricted_product_mem_schwartz F _ (ψ r) (hψSB r) (hψint r)
  have hT : ∀ r, ∃ T : SchwartzMap (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f (g' r)) = T f := fun r => hl (g' r) (hg'SB r)
  choose T hT using hT
  have key : ∀ f : SInf F (Fin n × Fin d), pureA F f g = ∑ r ∈ R, g r • pure f (φ r) := by
    intro f
    funext x
    rw [Finset.sum_apply]
    conv_lhs => rw [hR]
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_left_comm]
    rfl
  have key2 : ∀ (f : SInf F (Fin n₁ × Fin d₁)) r, pure f (ψ r) = pureA F f (g' r) := fun f r => rfl
  refine ⟨∑ r ∈ R, g r • (T r).comp ei, fun f => ?_⟩
  have hL : l (e (pureA F (⇑f) g)) = ∑ r ∈ R, g r * T r (ei f) := by
    rw [key, map_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, map_smul, hpure f (φ r) (hφSB r) (hφvac r), key2, hT, smul_eq_mul]
  rw [LinearMap.comp_apply, hL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rfl

end GlobalTheory.ThKEvAdm

end

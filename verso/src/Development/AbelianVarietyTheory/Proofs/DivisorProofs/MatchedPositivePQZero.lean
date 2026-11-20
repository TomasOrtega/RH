import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFunctionBoundedOnUnipotentStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.ThKEndACT

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH' c hprop Φ Φ' hSo hPM μ 𝓕 hμ hF h1 h`. Establish `hT` using `hM.triple`. Establish `hPol : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M'`. Take `⟨T, -, m, m', f, φ, f', φ', hf, hf', e1, e2, -⟩` from `hPM`. Use `⟨e1 ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_, e2 ▸ Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_⟩` and prove the remaining obligations.

Conclude with `⟨f i, (hf i).1, φ i, (hf i).2.1, Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hf i).2.2 v hT)), rfl⟩`. Conclude with `⟨f' j, (hf' j).1, φ' j, (hf' j).2.1, Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hf' j).2.2 v hT)), rfl⟩`. Take `⟨hS1, hS2⟩` from `GlobalTheory.T.split_existence hK F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH'`. Take `⟨⟨fa, fb⟩, hsp, -⟩` from `hS1 Φ hPol.1`. Take `⟨⟨fa', fb'⟩, hsp', -⟩` from `hS2 Φ' ⟨hPol.2, hSo⟩`.

Take `⟨ea, eb⟩` from `hprop Φ Φ' hSo hPM fa fb fa' fb' hsp hsp'`. Establish `e1` using `hsp.1 μ 𝓕 hμ hF h1 h`. Establish `e2` using `hsp'.1 μ 𝓕 hμ hF h1 h`. Take `⟨hc1, hi1⟩` from `GlobalTheory.T.continuous_left_invariant_theta hK F E σ B a a' G X om om' hT Φ hPol.1`. Take `⟨hc2, hi2⟩` from `GlobalTheory.T.continuous_left_invariant_dual hK F E σ B a a' G X om om' hT Φ' ⟨hPol.2, hSo⟩`.

Use `haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Establish `hfin : μ 𝓕 ≠ ⊤` using `by rw [h1]; exact ENNReal.one_ne_top`. Establish `hint : ∀ g : UA σ G.W.J → ℂ, Continuous g → (∀ γ ∈ ratU σ G.W.J, ∀ h, g (γ * h) = g h) → IntegrableOn (fun u : unip σ G.W H' => g (u.1 * h)) 𝓕 μ`.

Introduce `g hg hgi`. Take `⟨C, hC⟩` from `GlobalTheory.T.automorphic_function_bounded_on_unipotent F E σ B (a + a') d₁ G.W W₁ H' i₀ i₁ _ _ hT.base hT.geo.hW hH' g hg hgi h`. Conclude with `Measure.integrableOn_of_bounded (M := C) hfin (hg.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable (ae_of_all _ fun u => hC u.1 u.2)`. Establish `i1` using `hint _ hc1 hi1`. Establish `i2` using `(hint _ hc2 hi2).const_mul c`.

Use `show (0 : ℂ) = ∫ u in 𝓕, (G.M.I om Φ (u.1 * h) - c * G.M'.I om' Φ' (u.1 * h)) ∂μ`. Rewrite using `[integral_sub i1 i2, integral_const_mul, ← e1, ← e2, ea, eb]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → fa = c • fa' ∧ fb = c • fb') →
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
      IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0 := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH' c hprop Φ Φ' hSo hPM μ 𝓕 hμ hF h1 h
  have hT := hM.triple
  have hPol : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' := by
    obtain ⟨T, -, m, m', f, φ, f', φ', hf, hf', e1, e2, -⟩ := hPM
    refine ⟨e1 ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_,
      e2 ▸ Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_⟩
    · exact ⟨f i, (hf i).1, φ i, (hf i).2.1,
        Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hf i).2.2 v hT)), rfl⟩
    · exact ⟨f' j, (hf' j).1, φ' j, (hf' j).2.1,
        Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hf' j).2.2 v hT)), rfl⟩
  obtain ⟨hS1, hS2⟩ := GlobalTheory.T.split_existence hK F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH'
  obtain ⟨⟨fa, fb⟩, hsp, -⟩ := hS1 Φ hPol.1
  obtain ⟨⟨fa', fb'⟩, hsp', -⟩ := hS2 Φ' ⟨hPol.2, hSo⟩
  obtain ⟨ea, eb⟩ := hprop Φ Φ' hSo hPM fa fb fa' fb' hsp hsp'
  have e1 := hsp.1 μ 𝓕 hμ hF h1 h
  have e2 := hsp'.1 μ 𝓕 hμ hF h1 h
  obtain ⟨hc1, hi1⟩ := GlobalTheory.T.continuous_left_invariant_theta hK F E σ B a a' G X om om' hT Φ hPol.1
  obtain ⟨hc2, hi2⟩ := GlobalTheory.T.continuous_left_invariant_dual hK F E σ B a a' G X om om' hT Φ' ⟨hPol.2, hSo⟩
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hfin : μ 𝓕 ≠ ⊤ := by rw [h1]; exact ENNReal.one_ne_top
  have hint : ∀ g : UA σ G.W.J → ℂ, Continuous g → (∀ γ ∈ ratU σ G.W.J, ∀ h, g (γ * h) = g h) →
      IntegrableOn (fun u : unip σ G.W H' => g (u.1 * h)) 𝓕 μ := by
    intro g hg hgi
    obtain ⟨C, hC⟩ := GlobalTheory.T.automorphic_function_bounded_on_unipotent F E σ B (a + a') d₁ G.W W₁ H' i₀ i₁ _ _ hT.base hT.geo.hW hH' g hg hgi h
    exact Measure.integrableOn_of_bounded (M := C) hfin
      (hg.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable
      (ae_of_all _ fun u => hC u.1 u.2)
  have i1 := hint _ hc1 hi1
  have i2 := (hint _ hc2 hi2).const_mul c
  show (0 : ℂ) = ∫ u in 𝓕, (G.M.I om Φ (u.1 * h) - c * G.M'.I om' Φ' (u.1 * h)) ∂μ
  rw [integral_sub i1 i2, integral_const_mul, ← e1, ← e2, ea, eb]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.ThKEndACT

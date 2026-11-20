import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramDensityStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace PositivityTheory.Rg.Mass.LiteralAutomorphy

open PositivityTheory.Rg.Mass

/- English proof (translation)
Introduce `hMV hLM F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ`. Take `⟨C, hC⟩` from `hLM F E σ J d b li lam μ 𝓕 mi m hCM hJ hAn hli hlam hμ h𝓕 hmi hm`. Establish `hfin` using `Filter.eventually_cofinite.1 hC`. Use `⟨hfin.toFinset, fun S hS φ A hT => ?_⟩` and prove the remaining obligations. Take `⟨hφc, hφs, hφ0, hφU, hAS, hAL⟩` from `hT`.

Take `⟨hGc, hGs, hGl, hGi⟩` from `GlobalTheory.T.archimedean_binary_gram_density F E σ hCM J hJ d b li hli mi hmi φ hφc hφs hφ0 hφU`. Establish `hG0 : ∀ y : Ainf F, 0 ≤ ∫ X, φ X ∂(mi (hermScal (Ainf F) σ y))` using `fun y => integral_nonneg fun X => hφ0 X`. Establish `hP` using `fun v (hv : v ∉ S) => not_not.1 (fun h => hv (hS (hfin.mem_toFinset.2 h)))`. Establish `key` using `hMV F hCM.1 θ hθ li lam hli hlam S (fun s => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) (fun v s => (m v (hermScal (Fv F v) σ s) (A v)).toReal) C hGc hGs hG0 (fun v y => ENNReal.toReal_nonneg) (fun v hv => by`. Take `⟨h1, h2, h3⟩` from `hAS v hv`.

Take `⟨c1, c2, -⟩` from `GlobalTheory.T.local_binary_gram_integral F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v) (A v) h1 h2 h3`. Conclude with `⟨c1, c2⟩)`. Use the proof step `(fun v hv => by`. Take `⟨p1, p2, p3⟩` from `hP v hv`. Take `⟨l1, l2⟩` from `GlobalTheory.T.local_binary_gram_density F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v)`.

Simplify using `only [hAL v hv]`. Use `⟨l1, fun s hs => ?_, p2, p3, l2⟩` and prove the remaining obligations. Establish `hs0 : s ≠ 0` using `fun h => hs (h ▸ (v.adicCompletionIntegers F).zero_mem)`. Rewrite using `[p1 s hs hs0]`. Use the proof step `rfl)`.

Use `beta_reduce at key`. Establish `hlim : ENNReal.ofReal ((∫ y, (∫ X, φ X ∂(mi (hermScal (Ainf F) σ y))) ∂li) * ∏ v ∈ S, ∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v)) = vol b li lam S φ A`. Rewrite using `[ENNReal.ofReal_mul (integral_nonneg fun s => hG0 s), ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg fun s => ENNReal.toReal_nonneg), hGi]`. Unfold `vol`. Use `congr 1`.

Use `Finset.prod_congr rfl fun v hv => ?_` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hAS v hv`. Conclude with `(GlobalTheory.T.local_binary_gram_integral F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v) (A v) h1 h2 h3).2.2`. Rewrite `key` using `[hlim]`. Establish `hsq : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] 0) (𝓝[>] 0)`.

Use `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_` and prove the remaining obligations. Establish `h0 : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2))` using `(continuous_pow 2).tendsto 0`. Simplify using `using h0.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε) using Set.mem_Ioi.2 (pow_pos hε 2)`. Use `(key.comp hsq).congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)`. Simplify using `only [Function.comp_apply]`. Rewrite using `[← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]`. Use `tsum_congr fun β => ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.T.archimedean_binary_gram_integral F E σ hCM J hJ d b li hli mi hmi θ hθ ε hε (algebraMap F (Ainf F) β.1) φ hφc`.

Rewrite using `[← mul_assoc, h1, hGl, mul_assoc, ← ENNReal.ofReal_mul (hG0 _), map_pow]`.
-/
theorem srside : MeanVal → LocMass → RSide := by
  intro hMV hLM F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ
  obtain ⟨C, hC⟩ := hLM F E σ J d b li lam μ 𝓕 mi m hCM hJ hAn hli hlam hμ h𝓕 hmi hm
  have hfin := Filter.eventually_cofinite.1 hC
  refine ⟨hfin.toFinset, fun S hS φ A hT => ?_⟩
  obtain ⟨hφc, hφs, hφ0, hφU, hAS, hAL⟩ := hT
  obtain ⟨hGc, hGs, hGl, hGi⟩ := GlobalTheory.T.archimedean_binary_gram_density F E σ hCM J hJ d b li hli mi hmi φ hφc hφs hφ0 hφU
  have hG0 : ∀ y : Ainf F, 0 ≤ ∫ X, φ X ∂(mi (hermScal (Ainf F) σ y)) := fun y => integral_nonneg fun X => hφ0 X
  have hP := fun v (hv : v ∉ S) => not_not.1 (fun h => hv (hS (hfin.mem_toFinset.2 h)))
  have key := hMV F hCM.1 θ hθ li lam hli hlam S (fun s => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s)))
    (fun v s => (m v (hermScal (Fv F v) σ s) (A v)).toReal) C hGc hGs hG0 (fun v y => ENNReal.toReal_nonneg)
    (fun v hv => by
      obtain ⟨h1, h2, h3⟩ := hAS v hv
      obtain ⟨c1, c2, -⟩ := GlobalTheory.T.local_binary_gram_integral F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v) (A v) h1 h2 h3
      exact ⟨c1, c2⟩)
    (fun v hv => by
      obtain ⟨p1, p2, p3⟩ := hP v hv
      obtain ⟨l1, l2⟩ := GlobalTheory.T.local_binary_gram_density F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v)
      simp only [hAL v hv]
      refine ⟨l1, fun s hs => ?_, p2, p3, l2⟩
      have hs0 : s ≠ 0 := fun h => hs (h ▸ (v.adicCompletionIntegers F).zero_mem)
      rw [p1 s hs hs0]
      rfl)
  beta_reduce at key
  have hlim : ENNReal.ofReal ((∫ y, (∫ X, φ X ∂(mi (hermScal (Ainf F) σ y))) ∂li) *
      ∏ v ∈ S, ∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v)) = vol b li lam S φ A := by
    rw [ENNReal.ofReal_mul (integral_nonneg fun s => hG0 s),
      ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg fun s => ENNReal.toReal_nonneg), hGi]
    unfold vol
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨h1, h2, h3⟩ := hAS v hv
    exact (GlobalTheory.T.local_binary_gram_integral F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v) (A v) h1 h2 h3).2.2
  rw [hlim] at key
  have hsq : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) := (continuous_pow 2).tendsto 0
      simpa using h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε) using Set.mem_Ioi.2 (pow_pos hε 2)
  refine (key.comp hsq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  simp only [Function.comp_apply]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun β => ?_
  have h1 := GlobalTheory.T.archimedean_binary_gram_integral F E σ hCM J hJ d b li hli mi hmi θ hθ ε hε (algebraMap F (Ainf F) β.1) φ hφc
  rw [← mul_assoc, h1, hGl, mul_assoc, ← ENNReal.ofReal_mul (hG0 _), map_pow]

end PositivityTheory.Rg.Mass.LiteralAutomorphy

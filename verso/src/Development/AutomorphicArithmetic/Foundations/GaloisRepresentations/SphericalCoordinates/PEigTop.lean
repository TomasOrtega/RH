import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Introduce `hAd hDg hTy hRf hMk hBc hFd hFw hEv F _ _ O _ bar g ρ a n t₀ ε hSig D P₀ M₀ hP hM ga H hFix χ hMin hdeg hsep d co hco T hT k α hα`. Establish `hH : H.det ≠ 0` using `(hAd O bar g ρ D P₀ M₀ hP hM ga H hFix).1`. Take `⟨Sb, ty, ev, hD⟩` from `hDg F O bar g ρ a D P₀ hP ga H hFix.2 χ hMin hsep`. Establish `hcnt` using `hTy F O bar g ρ a n t₀ ε hSig H Sb ty ev hD`. Establish `hrts` using `hRf F O bar g ρ a n t₀ ε hSig D P₀ hP ga H hFix.2 Sb ty ev hD χ hMin hdeg`.

Establish `hmk` using `hMk F O bar g ρ a n t₀ ε hSig H Sb ty ev hD`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (evAt ty ev t₀).card = 1`. Establish `h` using `(hcnt t₀).1`. Simplify `h` using `[typeMult]`.

Take `⟨m, hm⟩` from `Multiset.card_eq_one.1 h1`. Conclude with `⟨m, (hmk m).2 hm⟩`. Introduce `mu hmu`. Establish `hE : evAt ty ev t₀ = {mu}` using `(hmk mu).1 hmu`. Establish `hev0 : ∀ i, ev i ≠ 0`.

Introduce `i h0`. Establish `hdet : H.det * Sb.det = Sb.det * ∏ j, ev j`. Establish `h` using `congrArg Matrix.det hD.2.2`. Simplify `h` using `[Matrix.det_mul, Matrix.det_diagonal]`. Rewrite `hdet` using `[Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero]`.

Conclude with `mul_ne_zero hH hD.1 hdet`. Establish `hr0 : rts χ t₀ = mu ::ₘ (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ)`. Rewrite using `[hrts t₀]`. Unfold `evFull`. Rewrite using `[hE, Multiset.singleton_add]`.

Establish `hnd : (rts χ t₀).Nodup` using `Polynomial.nodup_roots hsep.map`. Rewrite `hnd` using `[hr0, Multiset.nodup_cons]`. Establish `hne : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), (starRingEnd ℂ) r ≠ mu`. Introduce `r hr h`. Conclude with `hnd.1 (h ▸ Multiset.mem_map_of_mem _ hr)`.

Establish `hnz : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), (starRingEnd ℂ) r ≠ 0`. Introduce `r hr`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hr`. Conclude with `(_root_.map_ne_zero _).2 (hev0 i)`. Establish `herase : (rts χ t₀).erase mu = (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ)`.

Rewrite using `[hr0, Multiset.erase_cons_head]`. Take `⟨-, hdetT⟩` from `hBc F O bar g ρ a n t₀ ε hSig D P₀ M₀ hP hM H hH Sb ty ev hD mu hE d co hco T hT`. Establish `hT1 : LinearMap.det (1 - T) = ((evAt ty ev (ComplexEmbedding.conjugate t₀)).map fun r => 1 - 1 * (mu / (starRingEnd ℂ) r)).prod`. Establish `h` using `hdetT 1`. Rewrite `h` using `[one_smul]`. Then use the resulting hypothesis.

Establish `hfac : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), 1 - 1 * (mu / (starRingEnd ℂ) r) ≠ 0`. Introduce `r hr h`. Apply `hne r hr` to reduce the goal to its premises. Establish `hs` using `hnz r hr`. Clear denominators, using `at h` for the nonvanishing conditions.

Take the linear combination `h`. Establish `hFib` using `hFd F O bar g ρ a H Sb ty ev hD k α`. Establish `hF1 : LinearMap.det (1 - fibMap H (diagAct a ρ α)) = ∏ s, ∏ i, (1 - ty i (α s : F) * ev i)`. Establish `h` using `hFib 1`. Rewrite `h` using `[one_smul]`.

Simplify using `using h`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hr0]`. Conclude with `Multiset.mem_cons_self _ _`. Rewrite using `[hT1]`.

Use `Multiset.prod_ne_zero fun h => ?_` and prove the remaining obligations. Take `⟨r, hr, h0⟩` from `Multiset.mem_map.1 h`. Conclude with `hfac r hr h0`. Rewrite using `[hF1]`. Use `Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations.

Take `⟨x, hx⟩` from `hα s`. Establish `h` using `hEv F O bar g ρ a D P₀ hP ga H hFix.2 Sb ty ev hD i x`. Rewrite `h` using `[← hx]`. Then use the resulting hypothesis. Introduce `t`. Establish `hball : LinearMap.det (1 - t • T) / LinearMap.det (1 - T) = ballW t₀ t χ mu`.

Unfold `ballW`. Rewrite using `[herase, Multiset.map_map, hdetT t, hT1, ← Multiset.prod_map_div]`. Use `congr 1`. Use `Multiset.map_congr rfl fun r hr => ?_` and prove the remaining obligations. Establish `hs` using `hnz r hr`.

Establish `h1` using `hfac r hr`. Establish `h2 : (starRingEnd ℂ) r - mu ≠ 0` using `sub_ne_zero.2 (hne r hr)`. Simplify using `only [Function.comp_apply]`. Rewrite using `[div_eq_div_iff h1 h2]`. Clear the denominators using the available nonvanishing facts.

Unfold `locW`. Rewrite using `[hball, hFib t, hF1, map_prod, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `h` using `hFw F g n t₀ ε ty ev χ mu hSig.cx hSig.pos hSig.eps (fun τ => (hcnt τ).1) hrts hE (α s : F) t`.

Rewrite using `[← h, map_prod]`.
-/
theorem UpperTheory.Gal.W2.eigTop_of :
    UpperTheory.Gal.W2.AdExists → UpperTheory.Gal.W2.DiagExists → UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.RootsFull → UpperTheory.Gal.W2.MarkDiag → UpperTheory.Gal.W2.BallChar → UpperTheory.Gal.W2.FibDet → UpperTheory.Gal.W2.FibW → UpperTheory.Gal.W2.EvIntegral → UpperTheory.Gal.W2.EigTop := by
  intro hAd hDg hTy hRf hMk hBc hFd hFw hEv F _ _ O _ bar g ρ a n t₀ ε hSig D P₀ M₀ hP hM ga H hFix χ hMin hdeg hsep d co hco T hT k α hα
  have hH : H.det ≠ 0 := (hAd O bar g ρ D P₀ M₀ hP hM ga H hFix).1
  obtain ⟨Sb, ty, ev, hD⟩ := hDg F O bar g ρ a D P₀ hP ga H hFix.2 χ hMin hsep
  have hcnt := hTy F O bar g ρ a n t₀ ε hSig H Sb ty ev hD
  have hrts := hRf F O bar g ρ a n t₀ ε hSig D P₀ hP ga H hFix.2 Sb ty ev hD χ hMin hdeg
  have hmk := hMk F O bar g ρ a n t₀ ε hSig H Sb ty ev hD
  refine ⟨?_, ?_⟩
  · have h1 : (evAt ty ev t₀).card = 1 := by
      have h := (hcnt t₀).1
      simpa [typeMult] using h
    obtain ⟨m, hm⟩ := Multiset.card_eq_one.1 h1
    exact ⟨m, (hmk m).2 hm⟩
  intro mu hmu
  have hE : evAt ty ev t₀ = {mu} := (hmk mu).1 hmu
  have hev0 : ∀ i, ev i ≠ 0 := by
    intro i h0
    have hdet : H.det * Sb.det = Sb.det * ∏ j, ev j := by
      have h := congrArg Matrix.det hD.2.2
      simpa [Matrix.det_mul, Matrix.det_diagonal] using h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero] at hdet
    exact mul_ne_zero hH hD.1 hdet
  have hr0 : rts χ t₀ = mu ::ₘ (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ) := by
    rw [hrts t₀]
    unfold evFull
    rw [hE, Multiset.singleton_add]
  have hnd : (rts χ t₀).Nodup := Polynomial.nodup_roots hsep.map
  rw [hr0, Multiset.nodup_cons] at hnd
  have hne : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), (starRingEnd ℂ) r ≠ mu := by
    intro r hr h
    exact hnd.1 (h ▸ Multiset.mem_map_of_mem _ hr)
  have hnz : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), (starRingEnd ℂ) r ≠ 0 := by
    intro r hr
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hr
    exact (_root_.map_ne_zero _).2 (hev0 i)
  have herase : (rts χ t₀).erase mu = (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ) := by
    rw [hr0, Multiset.erase_cons_head]
  obtain ⟨-, hdetT⟩ := hBc F O bar g ρ a n t₀ ε hSig D P₀ M₀ hP hM H hH Sb ty ev hD mu hE d co hco T hT
  have hT1 : LinearMap.det (1 - T) =
      ((evAt ty ev (ComplexEmbedding.conjugate t₀)).map fun r => 1 - 1 * (mu / (starRingEnd ℂ) r)).prod := by
    have h := hdetT 1
    rwa [one_smul] at h
  have hfac : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), 1 - 1 * (mu / (starRingEnd ℂ) r) ≠ 0 := by
    intro r hr h
    apply hne r hr
    have hs := hnz r hr
    field_simp at h
    linear_combination h
  have hFib := hFd F O bar g ρ a H Sb ty ev hD k α
  have hF1 : LinearMap.det (1 - fibMap H (diagAct a ρ α)) = ∏ s, ∏ i, (1 - ty i (α s : F) * ev i) := by
    have h := hFib 1
    rw [one_smul] at h
    simpa using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr0]
    exact Multiset.mem_cons_self _ _
  · rw [hT1]
    refine Multiset.prod_ne_zero fun h => ?_
    obtain ⟨r, hr, h0⟩ := Multiset.mem_map.1 h
    exact hfac r hr h0
  · rw [hF1]
    refine Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_
    obtain ⟨x, hx⟩ := hα s
    have h := hEv F O bar g ρ a D P₀ hP ga H hFix.2 Sb ty ev hD i x
    rwa [← hx] at h
  · intro t
    have hball : LinearMap.det (1 - t • T) / LinearMap.det (1 - T) = ballW t₀ t χ mu := by
      unfold ballW
      rw [herase, Multiset.map_map, hdetT t, hT1, ← Multiset.prod_map_div]
      congr 1
      refine Multiset.map_congr rfl fun r hr => ?_
      have hs := hnz r hr
      have h1 := hfac r hr
      have h2 : (starRingEnd ℂ) r - mu ≠ 0 := sub_ne_zero.2 (hne r hr)
      simp only [Function.comp_apply]
      rw [div_eq_div_iff h1 h2]
      field_simp
    unfold locW
    rw [hball, hFib t, hF1, map_prod, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    have h := hFw F g n t₀ ε ty ev χ mu hSig.cx hSig.pos hSig.eps (fun τ => (hcnt τ).1) hrts hE (α s : F) t
    rw [← h, map_prod]

import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx

open NumberField IsDedekindDomain Filter

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V Λ t hV hAt v`. Take `⟨hInf, hUnr, hNe, -, -, -⟩` from `UpperTheory.ConvolutionTheory.T.places F E hp`. Take `⟨S₀, hS₀, hA⟩` from `hAt`. Take `⟨-, -, h0⟩` from `UpperTheory.ConvolutionTheory.Dp.parEx E n hn μ V hV`. Establish `hU` using `Filter.eventually_cofinite.1 hUnr`.

Establish `hfin` using `((hS₀.image (fun w => w.under (𝓞 F))).union hU).union (Set.finite_singleton v)`. Take `⟨q, hq, hqS⟩` from `(hInf.diff hfin).nonempty`. Establish `hsub : ∀ w, w.under (𝓞 F) ∉ hfin.toFinset → w ∉ S₀` using `fun w hw hw0 => hw (hfin.mem_toFinset.2 (Or.inl (Or.inl ⟨w, hw0, rfl⟩)))`. Use `⟨hfin.toFinset, q, (hNe q).some, hfin.mem_toFinset.2 (Or.inr rfl), fun h => hqS (hfin.mem_toFinset.1 h), hq, fun u hu => ?_, fun w hw => ?_, fun S' hS' => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hu (hfin.mem_toFinset.2 (Or.inl (Or.inr h)))`. Conclude with `(hA.2 w (hsub w hw)).2.1`. Establish `hS : ∀ w, w ∉ S' → w ∉ S₀` using `fun w hw => hsub w fun h => hw ((hS' w).2 (Or.inl h))`. Conclude with `⟨⟨hA.1, fun w hw => hA.2 w (hS w hw)⟩, fun τ => (hA.1 τ).1, fun w hw => ⟨(hA.2 w (hS w hw)).1, h0 w _ (hA.2 w (hS w hw))⟩⟩`.
-/
theorem UpperTheory.ConvolutionTheory.T.pickS :
    UpperTheory.ConvolutionTheory.T.PickS := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V Λ t hV hAt v
  obtain ⟨hInf, hUnr, hNe, -, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨S₀, hS₀, hA⟩ := hAt
  obtain ⟨-, -, h0⟩ := UpperTheory.ConvolutionTheory.Dp.parEx E n hn μ V hV
  have hU := Filter.eventually_cofinite.1 hUnr
  have hfin := ((hS₀.image (fun w => w.under (𝓞 F))).union hU).union (Set.finite_singleton v)
  obtain ⟨q, hq, hqS⟩ := (hInf.diff hfin).nonempty
  have hsub : ∀ w, w.under (𝓞 F) ∉ hfin.toFinset → w ∉ S₀ := fun w hw hw0 =>
    hw (hfin.mem_toFinset.2 (Or.inl (Or.inl ⟨w, hw0, rfl⟩)))
  refine ⟨hfin.toFinset, q, (hNe q).some, hfin.mem_toFinset.2 (Or.inr rfl),
    fun h => hqS (hfin.mem_toFinset.1 h), hq, fun u hu => ?_, fun w hw => ?_, fun S' hS' => ?_⟩
  · by_contra h
    exact hu (hfin.mem_toFinset.2 (Or.inl (Or.inr h)))
  · exact (hA.2 w (hsub w hw)).2.1
  · have hS : ∀ w, w ∉ S' → w ∉ S₀ := fun w hw => hsub w fun h => hw ((hS' w).2 (Or.inl h))
    exact ⟨⟨hA.1, fun w hw => hA.2 w (hS w hw)⟩, fun τ => (hA.1 τ).1,
      fun w hw => ⟨(hA.2 w (hS w hw)).1, h0 w _ (hA.2 w (hS w hw))⟩⟩

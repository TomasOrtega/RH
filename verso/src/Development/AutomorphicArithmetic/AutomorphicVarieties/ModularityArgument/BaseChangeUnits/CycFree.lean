import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ComplexBaseChangeOfLiterature
import Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CuspidalMultiplicityOne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.V.Z.Bc

/- English proof (translation)
Consider the cases of `π with`. Consider the case `cx P`. Consider the cases of `π' with`. Consider the case `cx P'`. Conclude with `Quotient.exact (UpperTheory.CBC.SmoothnessOfSatakeParameters.cx_smo hJ hn (CG.mk P) (CG.mk P') h)`.

Consider the case `re P'`. Conclude with `(UpperTheory.CBC.SmoothnessOfSatakeParameters.not_both F ‹IsTotallyReal F› ‹IsTotallyComplex F›).elim`. Consider the case `re P`. Consider the cases of `π' with`. Consider the case `cx P'`.

Conclude with `(UpperTheory.CBC.SmoothnessOfSatakeParameters.not_both F ‹IsTotallyReal F› ‹IsTotallyComplex F›).elim`. Consider the case `re P'`. Conclude with `UpperTheory.V.Af.strongMultOneReal F n hn P P' h`.
-/
private theorem smo0 (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (F : Type) [Field F] [NumberField F] (n : ℕ) (hn : 1 ≤ n) (π π' : Cusp F n)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.sat v B ∧ π'.sat v B) : π.Iso π' := by
  cases π with
  | cx P =>
    cases π' with
    | cx P' =>
      exact Quotient.exact (UpperTheory.CBC.SmoothnessOfSatakeParameters.cx_smo hJ hn (CG.mk P) (CG.mk P') h)
    | re P' =>
      exact (UpperTheory.CBC.SmoothnessOfSatakeParameters.not_both F ‹IsTotallyReal F› ‹IsTotallyComplex F›).elim
  | re P =>
    cases π' with
    | cx P' =>
      exact (UpperTheory.CBC.SmoothnessOfSatakeParameters.not_both F ‹IsTotallyReal F› ‹IsTotallyComplex F›).elim
    | re P' =>
      exact UpperTheory.V.Af.strongMultOneReal F n hn P P' h

/- English proof (translation)
Introduce `s hs`. Establish `key : ∃ P' : Cusp M n, P'.space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' P.space ∧ ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧ (∀ w, normV (g w) = normV w) …`. Consider the cases of `P with`. Consider the case `cx P`. Take `⟨P', hP'⟩` from `h8 M σ.toRingEquiv s hs n P`.

Conclude with `⟨.cx P', hP', h10 K M σ s hs n P P' hP'⟩`. Consider the case `re P`. Take `⟨P', hP'⟩` from `h9 M σ.toRingEquiv s hs n P`. Conclude with `⟨.re P', hP', h11 K M σ s hs n P P' hP'⟩`. Take `⟨P', hsp, g, hinj, hund, hnorm, hsat⟩` from `key`.

Use `⟨P', hsp, smo0 hJ M n hn P' P ?_⟩` and prove the remaining obligations. Use `filter_upwards [hsat, H g hinj hund hnorm] with w hB ⟨B, hB1, hB2⟩`. Conclude with `⟨B, hB _ hB2, hB1⟩`.
-/
private theorem conjIso0 (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (h8 : SConjSpaceC) (h9 : SConjSpaceR)
    (h10 : SConjSatC) (h11 : SConjSatR) {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {n : ℕ} (hn : 1 ≤ n) (P : Cusp M n) (σ : M ≃ₐ[K] M)
    (H : ∀ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g →
      (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) → (∀ w, normV (g w) = normV w) →
      ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∃ B, P.sat w B ∧ P.sat (g w) B) :
    P.ConjIso σ.toRingEquiv := by
  intro s hs
  have key : ∃ P' : Cusp M n,
      P'.space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' P.space ∧
      ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧
        (∀ w, normV (g w) = normV w) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ B, P.sat (g w) B → P'.sat w B := by
    cases P with
    | cx P =>
      obtain ⟨P', hP'⟩ := h8 M σ.toRingEquiv s hs n P
      exact ⟨.cx P', hP', h10 K M σ s hs n P P' hP'⟩
    | re P =>
      obtain ⟨P', hP'⟩ := h9 M σ.toRingEquiv s hs n P
      exact ⟨.re P', hP', h11 K M σ s hs n P P' hP'⟩
  obtain ⟨P', hsp, g, hinj, hund, hnorm, hsat⟩ := key
  refine ⟨P', hsp, smo0 hJ M n hn P' P ?_⟩
  filter_upwards [hsat, H g hinj hund hnorm] with w hB ⟨B, hB1, hB2⟩
  exact ⟨B, hB _ hB2, hB1⟩

/- English proof (translation)
Introduce `K M _ _ _ _ _ _ hp hK n hn`. Take `⟨L1, L2, L3⟩` from `L K M hp hK n hn`. Establish `hc` using `fun (P : Cusp M n) (σ : M ≃ₐ[K] M) => conjIso0 hJ SConjSpaceC_holds SConjSpaceR_holds SConjSatC_holds SConjSatR_holds hn P σ`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `sat inf h hr`.

Take `⟨π, rfl, rfl⟩` from `SCuspOf_holds K n sat inf h`. Break down `L1 π hr with ⟨η, hη, hi⟩ | ⟨P, hw, hinf⟩` into its components or cases. Use `Or.inl ⟨η, hη, ?_⟩ filter_upwards [STwSat_holds K n π η, SatakeParameterExistence.of_fin hF K n π] with v ⟨hu, ht⟩ ⟨B, hB⟩` and prove the remaining obligations. Conclude with `⟨hu, B, hB, SSatUniq_holds K n π v _ _ (SIsoSat_holds K n _ _ hi v _ (ht B hB)) hB⟩`. Conclude with `Or.inr ⟨P.sat, P.inf, SIsCusp_holds M n P, hw, hinf⟩`.

Introduce `sat' inf' h hr hinv`. Take `⟨P, rfl, rfl⟩` from `SCuspOf_holds M n sat' inf' h`. Use `(fun ⟨π, hw, hinf⟩ => ⟨π.sat, π.inf, SIsCusp_holds K n π, hw, hinf⟩) (L2 P hr fun σ => hc P σ fun g _ hund _ => ?_)` and prove the remaining obligations. Use `filter_upwards [hinv] with w hall`. Conclude with `hall (g w) (hund w)`.

Introduce `sat inf sat' inf' h h' hw sat₁ inf₁ h₁ hw₁`. Take `⟨π, rfl, rfl⟩` from `SCuspOf_holds K n sat inf h`. Take `⟨P, rfl, rfl⟩` from `SCuspOf_holds M n sat' inf' h'`. Take `⟨π₁, rfl, rfl⟩` from `SCuspOf_holds K n sat₁ inf₁ h₁`. Take `⟨η, hη, hi⟩` from `L3 π P (fun σ => hc P σ fun g hinj hund hnorm => by filter_upwards [hw, hinj.tendsto_cofinite.eventually hw] with w h1' h2'`.

Take `⟨f, hf⟩` from `SNormPow_holds K M w`. Take `⟨B, hB, hPB⟩` from `h1' f hf`. Take `⟨B', hB', hPB'⟩` from `h2' f (by rw [hnorm w, hund w]; exact hf)`. Rewrite `hB'` using `[hund w]`. Take `rfl` from `SSatUniq_holds K n π _ _ _ hB hB'`.

Conclude with `⟨_, hPB, hPB'⟩) hw π₁ hw₁`. Use `⟨η, hη, ?_⟩` and prove the remaining obligations. Use `filter_upwards [STwSat_holds K n π η, SatakeParameterExistence.of_fin hF K n π] with v ⟨hu, ht⟩ ⟨B, hB⟩`. Conclude with `⟨hu, B, hB, SIsoSat_holds K n _ _ hi v _ (ht B hB)⟩`.
-/
theorem cycC_of_fin_js (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (L : CBCr) : CycC := by
  intro K M _ _ _ _ _ _ hp hK n hn
  obtain ⟨L1, L2, L3⟩ := L K M hp hK n hn
  have hc := fun (P : Cusp M n) (σ : M ≃ₐ[K] M) => conjIso0 hJ SConjSpaceC_holds SConjSpaceR_holds
    SConjSatC_holds SConjSatR_holds hn P σ
  refine ⟨?_, ?_, ?_⟩
  · intro sat inf h hr
    obtain ⟨π, rfl, rfl⟩ := SCuspOf_holds K n sat inf h
    rcases L1 π hr with ⟨η, hη, hi⟩ | ⟨P, hw, hinf⟩
    · refine Or.inl ⟨η, hη, ?_⟩
      filter_upwards [STwSat_holds K n π η, SatakeParameterExistence.of_fin hF K n π] with v ⟨hu, ht⟩ ⟨B, hB⟩
      exact ⟨hu, B, hB, SSatUniq_holds K n π v _ _ (SIsoSat_holds K n _ _ hi v _ (ht B hB)) hB⟩
    · exact Or.inr ⟨P.sat, P.inf, SIsCusp_holds M n P, hw, hinf⟩
  · intro sat' inf' h hr hinv
    obtain ⟨P, rfl, rfl⟩ := SCuspOf_holds M n sat' inf' h
    refine (fun ⟨π, hw, hinf⟩ => ⟨π.sat, π.inf, SIsCusp_holds K n π, hw, hinf⟩) (L2 P hr fun σ => hc P σ fun g _ hund _ => ?_)
    filter_upwards [hinv] with w hall
    exact hall (g w) (hund w)
  · intro sat inf sat' inf' h h' hw sat₁ inf₁ h₁ hw₁
    obtain ⟨π, rfl, rfl⟩ := SCuspOf_holds K n sat inf h
    obtain ⟨P, rfl, rfl⟩ := SCuspOf_holds M n sat' inf' h'
    obtain ⟨π₁, rfl, rfl⟩ := SCuspOf_holds K n sat₁ inf₁ h₁
    obtain ⟨η, hη, hi⟩ := L3 π P (fun σ => hc P σ fun g hinj hund hnorm => by
      filter_upwards [hw, hinj.tendsto_cofinite.eventually hw] with w h1' h2'
      obtain ⟨f, hf⟩ := SNormPow_holds K M w
      obtain ⟨B, hB, hPB⟩ := h1' f hf
      obtain ⟨B', hB', hPB'⟩ := h2' f (by rw [hnorm w, hund w]; exact hf)
      rw [hund w] at hB'
      obtain rfl := SSatUniq_holds K n π _ _ _ hB hB'
      exact ⟨_, hPB, hPB'⟩) hw π₁ hw₁
    refine ⟨η, hη, ?_⟩
    filter_upwards [STwSat_holds K n π η, SatakeParameterExistence.of_fin hF K n π] with v ⟨hu, ht⟩ ⟨B, hB⟩
    exact ⟨hu, B, hB, SIsoSat_holds K n _ _ hi v _ (ht B hB)⟩

/- English proof (translation)
The claim follows from `cycC_of_fin_js CuspFormAutomorphicBounds.automorphicFormsFiniteGL PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity (cbcr_of_cbcc UpperTheory.ConvolutionTheory.cbcc)`.
-/
theorem cycC_holds : CycC :=
  cycC_of_fin_js CuspFormAutomorphicBounds.automorphicFormsFiniteGL PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity (cbcr_of_cbcc UpperTheory.ConvolutionTheory.cbcc)

end UpperTheory.V.Z.Bc

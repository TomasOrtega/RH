import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfFreePermuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSummanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMatrixMajorantOperatorNormLeDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperArithmeticGroupUnipotentUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotallySplitRationalPrimeOfSplitsCompletelyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsDirectSumComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsDefiniteUnitaryFlagDomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFiniteOfComponentsStatement

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn.Definite

/- English proof (translation)
Introduce `E _ _ _ hbal hsmall r U C _ _ M hdef hlev u c huc`. Take `⟨g, hsplit, hg, hunip⟩` from `hlev`. Take `⟨Γo, hst, hun, hmem⟩` from `GlobalTheory.T.exists_upperArithmeticGroup_unipotentUnitary E r U C M c g hunip`. Take `⟨x, hx, hnc, -⟩` from `hbal r (M.comp c)`. Establish `h1 : M.tr u c = 1` using `hsmall r (M.comp c) g (GlobalTheory.T.isTotallySplitRationalPrime_of_splitsCompletely E g hsplit) hg Γo hst hun x hx hnc (M.tr u c) (hmem u huc) (fun τ => GlobalTheory.T.unitaryMatrix_majorantOperatorNorm_le_definite E r (M.comp c).toData (by rw [M.comp_basePoint c]; exact hdef) …`.

Conclude with `M.tr_faithful u c huc (by rw [h1]; exact (M.comp c).Γ.one_mem)`.
-/
theorem free_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E → ∀ (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → LevelHyp M → ∀ (u : U) (c : C), u • c = c → u = 1 := by
  intro E _ _ _ hbal hsmall r U C _ _ M hdef hlev u c huc
  obtain ⟨g, hsplit, hg, hunip⟩ := hlev
  obtain ⟨Γo, hst, hun, hmem⟩ := GlobalTheory.T.exists_upperArithmeticGroup_unipotentUnitary E r U C M c g hunip
  obtain ⟨x, hx, hnc, -⟩ := hbal r (M.comp c)
  have h1 : M.tr u c = 1 :=
    hsmall r (M.comp c) g (GlobalTheory.T.isTotallySplitRationalPrime_of_splitsCompletely E g hsplit) hg Γo hst hun x hx hnc (M.tr u c) (hmem u huc)
      (fun τ => GlobalTheory.T.unitaryMatrix_majorantOperatorNorm_le_definite E r (M.comp c).toData (by rw [M.comp_basePoint c]; exact hdef) x hx _
        (hst _ (hmem u huc)).1 τ)
  exact M.tr_faithful u c huc (by rw [h1]; exact (M.comp c).Γ.one_mem)

/- English proof (translation)
Introduce `E _ _ _ r U C _ _ _ _ M hdef ka ρ hρ`. Use `haveI : Fintype C := Fintype.ofFinite C`. Establish `hfin : Module.Finite ℂ (M.cusp ka)` using `GlobalTheory.T.twoLevelCusp_finite_of_components E r U C M ka (fun c => GlobalTheory.T.finiteDimensional_cuspForms_definiteUnitaryFlagDomain E r (M.comp c).toData (by rw [M.comp_basePoint c]; exact hdef) _)`. Use `⟨hfin, fun H hH => ?_⟩` and prove the remaining obligations. Use `haveI : FiniteDimensional ℂ (M.cusp ka) := hfin`.

Establish `hfree : ∀ (h : H) (c : C), h • c = c → h = 1` using `free_of_definite E (GlobalTheory.T.existsBalancedFrameCMUnitary_proof E) (GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof E) r H C (sub M H) hdef hH`. Take `⟨A, hA, hAρ⟩` from `GlobalTheory.T.twoLevelCuspForms_directSum_components E r U C M ka ρ hρ`. Establish `hAρH : ∀ (h : H) (x : C), ∀ v ∈ A x, ρ h v ∈ A (h • x)` using `fun h x v hv => hAρ h x v hv`. Conclude with `⟨GlobalTheory.T.embedsInRegularRepresentationCopies_of_free_permuted_summands ℂ U (M.cusp ka) C ρ H hfree A hA hAρH, fun lam => GlobalTheory.T.card_mul_finrank_characterSpace_of_free_permuted_summands ℂ U (M.cusp ka) C ρ H hfree A hA hAρH H le_rfl lam⟩`.
-/
theorem share_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → Module.Finite ℂ (M.cusp ka) ∧ ∀ H : Subgroup U, LevelHyp (sub M H) → (∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H = finrank ℂ (M.cusp ka)) ∧ ∀ lam : H →* ℂˣ, Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank ℂ (M.cusp ka) := by
  intro E _ _ _ r U C _ _ _ _ M hdef ka ρ hρ
  classical
  haveI : Fintype C := Fintype.ofFinite C
  have hfin : Module.Finite ℂ (M.cusp ka) :=
    GlobalTheory.T.twoLevelCusp_finite_of_components E r U C M ka (fun c =>
      GlobalTheory.T.finiteDimensional_cuspForms_definiteUnitaryFlagDomain E r (M.comp c).toData (by rw [M.comp_basePoint c]; exact hdef) _)
  refine ⟨hfin, fun H hH => ?_⟩
  haveI : FiniteDimensional ℂ (M.cusp ka) := hfin
  have hfree : ∀ (h : H) (c : C), h • c = c → h = 1 :=
    free_of_definite E (GlobalTheory.T.existsBalancedFrameCMUnitary_proof E) (GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof E) r H C (sub M H) hdef hH
  obtain ⟨A, hA, hAρ⟩ := GlobalTheory.T.twoLevelCuspForms_directSum_components E r U C M ka ρ hρ
  have hAρH : ∀ (h : H) (x : C), ∀ v ∈ A x, ρ h v ∈ A (h • x) := fun h x v hv => hAρ h x v hv
  exact ⟨GlobalTheory.T.embedsInRegularRepresentationCopies_of_free_permuted_summands ℂ U (M.cusp ka) C ρ H hfree A hA hAρH,
    fun lam => GlobalTheory.T.card_mul_finrank_characterSpace_of_free_permuted_summands ℂ U (M.cusp ka) C ρ H hfree A hA hAρH H le_rfl lam⟩

end GlobalTheory.ShareOn.Definite

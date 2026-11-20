import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands

open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.DefiniteBC UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Simplify using `only [segSum]`. Rewrite using `[← GlobalTheory.NuShift.sumList_lpTw, List.map_map, List.map_map]`. Use `congr 1`. Use `List.map_congr_left fun Γ _ => ?_` and prove the remaining obligations. Use `show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _`.

Rewrite using `[hnu, WD.lpTw_add, add_comm, ← WD.lpTw_add, GlobalTheory.NuShift.lpChar_lpTw]`. Both sides reduce to the same expression.
-/
private theorem segSum_nu {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hnu : ∀ x (s : ℝ), rc (x.nu s) = (rc x).lpTw s)
    (l : List (Segment (w.adicCompletion E))) (c : ℝ) :
    segSum rc (l.map fun Γ => Γ.nu (c : ℂ)) = (segSum rc l).lpTw c := by
  simp only [segSum]
  rw [← GlobalTheory.NuShift.sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  rw [hnu, WD.lpTw_add, add_comm, ← WD.lpTw_add, GlobalTheory.NuShift.lpChar_lpTw]
  rfl

/- English proof (translation)
Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Take `⟨m, δ, Δ, s, hΔ, hδu, hs, hd0, hφ⟩` from `hTZ.exists_prod σ.smooth σ.irred hu hg`. Establish `hA` using `GlobalTheory.T.isLanglandsQuotient_of_irreducible_unitary_segment_product _ (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) a _ σ.ρ σ.irred m δ Δ s hΔ hδu hs hd0 hφ`. Establish `hB` using `GlobalTheory.T.langlandsQuotient_of_speh_type_product_isL _ hLM (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) (GlobalTheory.T.parabolicInduction_in_stages_product_of_products _) a _ σ.ρ m δ Δ s hΔ hδu hs hd0 hφ d n hd _ σ'.ρ σ'.irred hq`. Take `⟨a', ha', L⟩` from `hrc`.

Rewrite using `[L.langlands _ _ (GlobalTheory.SpehRec.isL_of_equiv hB (equivRep (ParLaws.toRep σ'))), L.langlands _ _ (GlobalTheory.SpehRec.isL_of_equiv hA (equivRep (ParLaws.toRep σ)))]`. Simplify using `only [segSum]`. Rewrite using `[List.map_flatMap, GlobalTheory.SpehRec.sumList_flatMap]`. Use `congr 1`. Use `List.map_congr_left fun i _ => ?_` and prove the remaining obligations.

Conclude with `segSum_nu L.nu _ _`.
-/
private theorem rec_spehQuotT {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRecT h rc) (hTZ : GlobalTheory.Published.GenericUnitaryDualGL)
    (hLM : GlobalTheory.Published.StandardCosocleGL) (a d n : ℕ) (hd : ∑ _ : Fin d, a = n) (σ : LocIrr w a) (σ' : LocIrr w n)
    (hu : IsUnitarisable σ.ρ) (hg : IsGeneric σ.ρ) (hq : IsSpehQuot hd σ σ') :
    rc (cls (ParLaws.toRep σ')) =
      sumList ((List.range d).map fun k : ℕ => (rc (cls (ParLaws.toRep σ))).lpTw (((d : ℝ) - 1) / 2 - k)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨m, δ, Δ, s, hΔ, hδu, hs, hd0, hφ⟩ := hTZ.exists_prod σ.smooth σ.irred hu hg
  have hA := GlobalTheory.T.isLanglandsQuotient_of_irreducible_unitary_segment_product _ (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) a _ σ.ρ σ.irred m δ Δ s hΔ hδu hs hd0 hφ
  have hB := GlobalTheory.T.langlandsQuotient_of_speh_type_product_isL _ hLM (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) (GlobalTheory.T.parabolicInduction_in_stages_product_of_products _) a _ σ.ρ m δ Δ s hΔ hδu hs hd0 hφ d n hd _ σ'.ρ σ'.irred hq
  obtain ⟨a', ha', L⟩ := hrc
  rw [L.langlands _ _ (GlobalTheory.SpehRec.isL_of_equiv hB (equivRep (ParLaws.toRep σ'))),
    L.langlands _ _ (GlobalTheory.SpehRec.isL_of_equiv hA (equivRep (ParLaws.toRep σ)))]
  simp only [segSum]
  rw [List.map_flatMap, GlobalTheory.SpehRec.sumList_flatMap]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact segSum_nu L.nu _ _

/- English proof (translation)
Introduce `H _ E Ω _ _ _ _ _ _ a d P w ρ σ _ _ hP hu hS A h rc hrc`. Establish `L` using `H.litN.loc`. Establish `hd : ∑ _ : Fin d, a = d * a` using `by simp`. Conclude with `rec_spehQuotT hrc (GlobalTheory.T.generic_unitary_dual_gl L.unit L.sq L.gen L.multi L.cos) L.cos a d _ hd ρ σ hu (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E a P w ρ hP) (GlobalTheory.DiscreteSpectrumCM.isSpehQuot_of_isSpeh hd ρ σ hS)`.
-/
theorem UpperTheory.V.Z.Win.Gu.spehT :
    HypothesesH → ExtraV → SpehT := by
  intro H _ E Ω _ _ _ _ _ _ a d P w ρ σ _ _ hP hu hS A h rc hrc
  have L := H.litN.loc
  have hd : ∑ _ : Fin d, a = d * a := by simp
  exact rec_spehQuotT hrc (GlobalTheory.T.generic_unitary_dual_gl L.unit L.sq L.gen L.multi L.cos) L.cos a d _ hd ρ σ hu
    (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E a P w ρ hP)
    (GlobalTheory.DiscreteSpectrumCM.isSpehQuot_of_isSpeh hd ρ σ hS)

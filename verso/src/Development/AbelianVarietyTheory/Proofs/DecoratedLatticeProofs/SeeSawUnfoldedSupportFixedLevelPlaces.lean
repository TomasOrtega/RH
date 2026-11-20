import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalPartsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderedProdLocalPartsSeparatesPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelCombinationEqSinglePlaceOnVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFirstFlatMapSupportAtLevelPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFlatMapContractionSupportAtLevelPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawProdLocalCellsDistinctPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.GSuppAsm

/- English proof (translation)
Introduce `D c v n G hc hv hG h1 h2 _hfl t ht hch j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂`. Establish `hj : j + 1 < D.R.m` using `by omega`. Establish `hj2 : j + 1 + 1 < D.R.m` using `by omega`. Use `⟨fun x hx hne => ?_, fun x hx hne => ?_⟩` and prove the remaining obligations. Take `⟨xs, hxs, rfl⟩` from `GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts hc hv G hG (j + 1) x hx`.

Establish `hb : ∀ i, j + 1 + (2 * σ + 1 + 1) = (G i).s + 1` using `fun i => by have := (G i).hs; omega`. Use `GlobalTheory.T.seeSaw_prod_local_cells_distinct_places G hG (j + 1) hj (jacGrp (c.jac j (σ + 1) h).d) (fun _ => 2 * σ + 1 + 1) hb xs (fun i => ?_)` and prove the remaining obligations. Take `⟨F, hF, hcomb⟩` from `GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG j hj Ψ₁ hΨ₁ i`. Take `⟨y, hy, hprod⟩` from `GlobalTheory.T.ordered_prod_local_parts_separates_place G hG (j + 1) xs hxs i`. Establish `hw : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j (σ + 1) h).χV (t.sBF j (σ + 1) h).χW (t.om j)`.

Use `(t.sBF j (σ + 1) h).weil` as an intermediate fact. Rewrite `this` using `[(ht.sBF j (σ + 1) h).1]`. Conclude with `this`. Take `⟨hF', hcm⟩` from `GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum hc hv (G i) j hj _ _ (t.om j) hw F hF y hy`. Use `GlobalTheory.T.seesaw_first_flatMap_support_at_level_place hc hv h1 t ht (G i) (hch i) j σ h _ hF' (xs i) (hxs i) ?_` and prove the remaining obligations.

Rewrite `hne` using `[hprod, hcomb]`. Establish `e : t.om j (1, xs i * y) = t.om j (1, xs i) * t.om j (1, y)`. Rewrite using `[← map_mul, Prod.mk_mul_mk, one_mul]`. Rewrite `hne` using `[e, Module.End.mul_apply, hcm]`. Conclude with `hne`.

Take `⟨xs, hxs, rfl⟩` from `GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts hc hv G hG (j + 1 + 1) x hx`. Establish `hb : ∀ i, j + 1 + 1 + (2 * σ + 1) = (G i).s + 1` using `fun i => by have := (G i).hs; omega`. Use `GlobalTheory.T.seeSaw_prod_local_cells_distinct_places G hG (j + 1 + 1) (by omega) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) (fun _ => 2 * σ + 1) hb xs (fun i => ?_)` and prove the remaining obligations. Take `⟨F₁, hF₁, hcomb₁⟩` from `GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG j hj Ψ₁ hΨ₁ i`. Take `⟨F₂, hF₂, hcomb₂⟩` from `GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG (j + 1) hj2 Ψ₂ hΨ₂ i`.

Take `⟨y, hy, hprod⟩` from `GlobalTheory.T.ordered_prod_local_parts_separates_place G hG (j + 1 + 1) xs hxs i`. Establish `hw : IsWeilDatumO c.ψ (c.V (j + 1)) (c.V (j + 1 + 1)) (t.sFB j σ h).χV (t.sFB j σ h).χW (t.om (j + 1))`. Use `(t.sFB j σ h).weil` as an intermediate fact. Rewrite `this` using `[(ht.sFB j σ h).1]`. Conclude with `this`.

Take `⟨hF₂', hcm⟩` from `GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum hc hv (G i) (j + 1) hj2 _ _ (t.om (j + 1)) hw F₂ hF₂ y hy`. Use `GlobalTheory.T.seeSaw_flatMap_contraction_support_at_level_place hc hv h2 t ht (G i) (hch i) j σ h F₁ hF₁ _ hF₂' (xs i) (hxs i) ?_` and prove the remaining obligations. Rewrite `hne` using `[hprod, hcomb₁, hcomb₂]`. Establish `e : t.om (j + 1) (1, xs i * y) = t.om (j + 1) (1, xs i) * t.om (j + 1) (1, y)`. Rewrite using `[← map_mul, Prod.mk_mul_mk, one_mul]`.

Rewrite `hne` using `[e, Module.End.mul_apply, hcm]`. Conclude with `hne`.
-/
theorem gsupp_of_local : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → GlobalTheory.LocMod.GSupp1 D → GlobalTheory.LocMod.GSupp2 D → FlatLaw D → ∀ t : Tup c, t.Is → (∀ i, (G i).Chars t) → GSupp (t := t) v := by
  intro D c v n G hc hv hG h1 h2 _hfl t ht hch j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂
  have hj : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  refine ⟨fun x hx hne => ?_, fun x hx hne => ?_⟩
  · obtain ⟨xs, hxs, rfl⟩ := GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts hc hv G hG (j + 1) x hx
    have hb : ∀ i, j + 1 + (2 * σ + 1 + 1) = (G i).s + 1 := fun i => by have := (G i).hs; omega
    refine GlobalTheory.T.seeSaw_prod_local_cells_distinct_places G hG (j + 1) hj (jacGrp (c.jac j (σ + 1) h).d) (fun _ => 2 * σ + 1 + 1) hb xs (fun i => ?_)
    obtain ⟨F, hF, hcomb⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG j hj Ψ₁ hΨ₁ i
    obtain ⟨y, hy, hprod⟩ := GlobalTheory.T.ordered_prod_local_parts_separates_place G hG (j + 1) xs hxs i
    have hw : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j (σ + 1) h).χV (t.sBF j (σ + 1) h).χW (t.om j) := by
      have := (t.sBF j (σ + 1) h).weil
      rw [(ht.sBF j (σ + 1) h).1] at this
      exact this
    obtain ⟨hF', hcm⟩ := GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum hc hv (G i) j hj _ _ (t.om j) hw F hF y hy
    refine GlobalTheory.T.seesaw_first_flatMap_support_at_level_place hc hv h1 t ht (G i) (hch i) j σ h _ hF' (xs i) (hxs i) ?_
    rw [hprod, hcomb] at hne
    have e : t.om j (1, xs i * y) = t.om j (1, xs i) * t.om j (1, y) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, Module.End.mul_apply, hcm] at hne
    exact hne
  · obtain ⟨xs, hxs, rfl⟩ := GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts hc hv G hG (j + 1 + 1) x hx
    have hb : ∀ i, j + 1 + 1 + (2 * σ + 1) = (G i).s + 1 := fun i => by have := (G i).hs; omega
    refine GlobalTheory.T.seeSaw_prod_local_cells_distinct_places G hG (j + 1 + 1) (by omega) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
      (fun _ => 2 * σ + 1) hb xs (fun i => ?_)
    obtain ⟨F₁, hF₁, hcomb₁⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG j hj Ψ₁ hΨ₁ i
    obtain ⟨F₂, hF₂, hcomb₂⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG (j + 1) hj2 Ψ₂ hΨ₂ i
    obtain ⟨y, hy, hprod⟩ := GlobalTheory.T.ordered_prod_local_parts_separates_place G hG (j + 1 + 1) xs hxs i
    have hw : IsWeilDatumO c.ψ (c.V (j + 1)) (c.V (j + 1 + 1)) (t.sFB j σ h).χV (t.sFB j σ h).χW (t.om (j + 1)) := by
      have := (t.sFB j σ h).weil
      rw [(ht.sFB j σ h).1] at this
      exact this
    obtain ⟨hF₂', hcm⟩ := GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum hc hv (G i) (j + 1) hj2 _ _ (t.om (j + 1)) hw F₂ hF₂ y hy
    refine GlobalTheory.T.seeSaw_flatMap_contraction_support_at_level_place hc hv h2 t ht (G i) (hch i) j σ h F₁ hF₁ _ hF₂' (xs i) (hxs i) ?_
    rw [hprod, hcomb₁, hcomb₂] at hne
    have e : t.om (j + 1) (1, xs i * y) = t.om (j + 1) (1, xs i) * t.om (j + 1) (1, y) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, Module.End.mul_apply, hcm] at hne
    exact hne

end GlobalTheory.SeeSaw.GSuppAsm

end

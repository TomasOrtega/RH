import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeBaseChangeFieldAndCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionKillingFiniteTateModuleImagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingOfIsAboveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResiduePerfectAndCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisRepresentationTateModuleBaseChangeEqOneIffStatement

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Rewrite `h`, the goal using `[mem_inertia_iff]`. Use `⟨?_, h.2⟩` and prove the remaining obligations. Establish `h1` using `h.1`. Use extensionality with `x`. Use `conv_rhs => rw [← h1]`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Both sides reduce to the same expression.
-/
theorem restrictScalars_mem_inertia_of_mem {K L Ω : Type} [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (V : ValuationSubring Ω) (σ : Ω ≃ₐ[L] Ω)
    (h : σ ∈ inertia L V) : σ.restrictScalars K ∈ inertia K V := by
  rw [mem_inertia_iff] at h ⊢
  refine ⟨?_, h.2⟩
  have h1 := h.1
  ext x
  conv_rhs => rw [← h1]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

/- English proof (translation)
Introduce `hN R K Ω _ _ _ _ _ _ _ _ _ hs V hV A _ _ hA l _ hl hfin`. Use `haveI : Algebra.IsSeparable K Ω := hs.separable`. Use `haveI : IsSepClosed Ω := hs.sep_closed`. Use `haveI : IsProper A.hom := hA.proper`. Take `⟨L, hL, hfix⟩` from `GlobalTheory.T.exists_finite_extension_killing_finite_tateModule_image K Ω A inferInstance l _ hfin`.

Set `W : ValuationSubring L` to `V.comap (algebraMap L Ω)`. Establish `hW : IsAbove R K W.toSubring`. Unfold `IsAbove at hV ⊢`. Rewrite using `[← hV]`. Use extensionality with `x`.

Both sides reduce to the same expression. Use `haveI : IsDiscreteValuationRing W := GlobalTheory.T.isDiscreteValuationRing_of_isAbove_alt R K L W hW`. Establish `hr : (algebraMap W L).range = W.toSubring`. Use extensionality with `x`. Conclude with `⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩`.

Establish `hW' : IsAbove R K (algebraMap W L).range` using `hr ▸ hW`. Take `⟨hp, hm⟩` from `GlobalTheory.T.residue_perfect_and_char_alt R K L W hW'`. Take `⟨hab, hc⟩` from `GlobalTheory.T.isAbelianScheme_and_comm_baseChange_field K L A hA`. Use `haveI : IsSepClosure L Ω := ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩`. Establish `hV' : IsAbove W L V.toSubring`.

Unfold `IsAbove`. Rewrite using `[hr]`. Both sides reduce to the same expression. Use `⟨L, W, inferInstance, inferInstance, hL, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hW', ?_⟩` and prove the remaining obligations. Use `(hN.iff_tateUnramified hV' hab l (hm l hl)).2 fun σ hσ => ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.T.galoisRepresentationTateModule_baseChange_eq_one_iff K L Ω A l σ]`. Conclude with `hfix _ (restrictScalars_mem_inertia_of_mem V σ hσ) fun a ha => σ.commutes ⟨a, ha⟩`.
-/
theorem hasPotentialGoodReduction_of_finite_image_inertia : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite → HasPotentialGoodReduction R K A := by
  intro hN R K Ω _ _ _ _ _ _ _ _ _ hs V hV A _ _ hA l _ hl hfin
  haveI : Algebra.IsSeparable K Ω := hs.separable
  haveI : IsSepClosed Ω := hs.sep_closed
  haveI : IsProper A.hom := hA.proper
  obtain ⟨L, hL, hfix⟩ := GlobalTheory.T.exists_finite_extension_killing_finite_tateModule_image K Ω A inferInstance l _ hfin
  let W : ValuationSubring L := V.comap (algebraMap L Ω)
  have hW : IsAbove R K W.toSubring := by
    unfold IsAbove at hV ⊢
    rw [← hV]
    ext x
    rfl
  haveI : IsDiscreteValuationRing W := GlobalTheory.T.isDiscreteValuationRing_of_isAbove_alt R K L W hW
  have hr : (algebraMap W L).range = W.toSubring := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hW' : IsAbove R K (algebraMap W L).range := hr ▸ hW
  obtain ⟨hp, hm⟩ := GlobalTheory.T.residue_perfect_and_char_alt R K L W hW'
  obtain ⟨hab, hc⟩ := GlobalTheory.T.isAbelianScheme_and_comm_baseChange_field K L A hA
  haveI : IsSepClosure L Ω := ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  have hV' : IsAbove W L V.toSubring := by
    unfold IsAbove
    rw [hr]
    rfl
  refine ⟨L, W, inferInstance, inferInstance, hL, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hW', ?_⟩
  refine (hN.iff_tateUnramified hV' hab l (hm l hl)).2 fun σ hσ => ?_
  rw [GlobalTheory.T.galoisRepresentationTateModule_baseChange_eq_one_iff K L Ω A l σ]
  exact hfix _ (restrictScalars_mem_inertia_of_mem V σ hσ) fun a ha => σ.commutes ⟨a, ha⟩

end GlobalTheory

import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCompletionFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalExtensionWithSimpleRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonicSimpleRootGeneratorResidueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFlatOfCompFlatOfMapMaximalIdealStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory

/- English proof (translation)
Introduce `O R₁ R' Ω _ _ _ _ _ _ _ _ _ φ₁ φ' u u' hφ₁ hloc _hR' het hunr hu hu' hcomm`. Take `⟨G, β, hGm, hGr, hGs, hspan⟩` from `GlobalTheory.T.exists_monic_simple_root_generating_residue O R' Ω φ' u' het hunr hu'`. Take `⟨C, _, _, c, uC, hcf, hcm, hcc, huC, huCc⟩` from `GlobalTheory.T.exists_regular_completion_flat R₁ Ω u hu`. Establish `hcomp : uC.comp (c.comp φ₁) = u'.comp φ'` using `by rw [← RingHom.comp_assoc, huCc, hcomm]`. Take `⟨E, _, _, e, v, hef, hem, hec, hv, hve, hβ⟩` from `GlobalTheory.T.exists_regular_local_extension_with_simple_root C Ω uC (G.map (c.comp φ₁)) β huC hcc (hGm.map _) (by rw [Polynomial.map_map, hcomp]; exact hGr) (by rw [Polynomial.map_map, hcomp]; exact hGs)`.

Establish `hdom : IsDomain E` using `GlobalTheory.isDomain_of_isRegularLocalRing E`. Establish `hmapE : (maximalIdeal R₁).map (e.comp c) = maximalIdeal E`. Rewrite using `[← Ideal.map_map, hcm, hem]`. Establish `hva : v.comp (e.comp c) = u` using `by rw [← RingHom.comp_assoc, hve, huCc]`. Establish `hψl : IsLocalHom ((e.comp c).comp φ₁)`.

Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `h1 : φ₁ x ∈ maximalIdeal R₁`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun h' => h (isUnit_of_map_unit φ₁ x h')`.

Establish `h2 : (e.comp c) (φ₁ x) ∈ maximalIdeal E` using `hmapE ▸ Ideal.mem_map_of_mem _ h1`. Conclude with `(mem_maximalIdeal _).1 h2 hx`. Establish `hv' : v.comp ((e.comp c).comp φ₁) = u'.comp φ'` using `by rw [← RingHom.comp_assoc, hva, hcomm]`. Establish `hrange : ∀ r : R', u' r ∈ v.range`. Introduce `r`.

Take `⟨q, hq⟩` from `hspan r`. Take `⟨y, hy⟩` from `hβ`. Use `⟨Polynomial.eval₂ ((e.comp c).comp φ₁) y q, ?_⟩` and prove the remaining obligations. Rewrite using `[hq, ← hv', Polynomial.eval_map, ← hy, Polynomial.hom_eval₂]`. Take `⟨b, hb1, hb2⟩` from `GlobalTheory.T.exists_extension_etaleCompletion_to_complete_local O R' E Ω φ' ((e.comp c).comp φ₁) u' v het hunr hec hψl hu' hv hv' hrange`.

Establish `hbl : IsLocalHom b`. Use `⟨fun r hr => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `h1 : r ∈ maximalIdeal R'` using `(mem_maximalIdeal _).2 h`. Rewrite `h1` using `[← hu', RingHom.mem_ker]`.

Establish `h2 : b r ∈ RingHom.ker v` using `by rw [RingHom.mem_ker, ← RingHom.comp_apply, hb2, h1]`. Rewrite `h2` using `[hv, mem_maximalIdeal]`. Conclude with `h2 hr`. Establish `haf : (e.comp c).Flat` using `RingHom.Flat.comp hcf hef`. Establish `hbf : b.Flat` using `GlobalTheory.T.flat_of_flat_comp_of_map_maximalIdeal_eq O R' E φ' b het.1 het.2.1 hbl (by rw [hb1]; exact RingHom.Flat.comp hφ₁ haf)`.

Conclude with `⟨E, inferInstance, inferInstance, hdom, e.comp c, b, v, haf, hbf, hb1.symm, hv, hva, hb2, hmapE, hec⟩`.
-/
theorem exists_complete_regular_meet : ∀ (O R₁ R' Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R₁] [IsRegularLocalRing R₁] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Field Ω] (φ₁ : O →+* R₁) (φ' : O →+* R') (u : R₁ →+* Ω) (u' : R' →+* Ω), φ₁.Flat → IsLocalHom φ₁ → IsAdicComplete (maximalIdeal R') R' → IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → RingHom.ker u = maximalIdeal R₁ → RingHom.ker u' = maximalIdeal R' → u.comp φ₁ = u'.comp φ' → ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : R₁ →+* E) (b : R' →+* E) (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp φ₁ = b.comp φ' ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (maximalIdeal R₁).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E := by
  intro O R₁ R' Ω _ _ _ _ _ _ _ _ _ φ₁ φ' u u' hφ₁ hloc _hR' het hunr hu hu' hcomm
  obtain ⟨G, β, hGm, hGr, hGs, hspan⟩ := GlobalTheory.T.exists_monic_simple_root_generating_residue O R' Ω φ' u' het hunr hu'
  obtain ⟨C, _, _, c, uC, hcf, hcm, hcc, huC, huCc⟩ := GlobalTheory.T.exists_regular_completion_flat R₁ Ω u hu
  have hcomp : uC.comp (c.comp φ₁) = u'.comp φ' := by rw [← RingHom.comp_assoc, huCc, hcomm]
  obtain ⟨E, _, _, e, v, hef, hem, hec, hv, hve, hβ⟩ := GlobalTheory.T.exists_regular_local_extension_with_simple_root C Ω uC (G.map (c.comp φ₁)) β huC hcc
    (hGm.map _) (by rw [Polynomial.map_map, hcomp]; exact hGr) (by rw [Polynomial.map_map, hcomp]; exact hGs)
  have hdom : IsDomain E := GlobalTheory.isDomain_of_isRegularLocalRing E
  have hmapE : (maximalIdeal R₁).map (e.comp c) = maximalIdeal E := by
    rw [← Ideal.map_map, hcm, hem]
  have hva : v.comp (e.comp c) = u := by rw [← RingHom.comp_assoc, hve, huCc]
  have hψl : IsLocalHom ((e.comp c).comp φ₁) := by
    refine ⟨fun x hx => ?_⟩
    by_contra h
    have h1 : φ₁ x ∈ maximalIdeal R₁ := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; exact fun h' => h (isUnit_of_map_unit φ₁ x h')
    have h2 : (e.comp c) (φ₁ x) ∈ maximalIdeal E := hmapE ▸ Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).1 h2 hx
  have hv' : v.comp ((e.comp c).comp φ₁) = u'.comp φ' := by rw [← RingHom.comp_assoc, hva, hcomm]
  have hrange : ∀ r : R', u' r ∈ v.range := by
    intro r
    obtain ⟨q, hq⟩ := hspan r
    obtain ⟨y, hy⟩ := hβ
    refine ⟨Polynomial.eval₂ ((e.comp c).comp φ₁) y q, ?_⟩
    rw [hq, ← hv', Polynomial.eval_map, ← hy, Polynomial.hom_eval₂]
  obtain ⟨b, hb1, hb2⟩ := GlobalTheory.T.exists_extension_etaleCompletion_to_complete_local O R' E Ω φ' ((e.comp c).comp φ₁) u' v het hunr hec hψl hu' hv hv' hrange
  have hbl : IsLocalHom b := by
    refine ⟨fun r hr => ?_⟩
    by_contra h
    have h1 : r ∈ maximalIdeal R' := (mem_maximalIdeal _).2 h
    rw [← hu', RingHom.mem_ker] at h1
    have h2 : b r ∈ RingHom.ker v := by rw [RingHom.mem_ker, ← RingHom.comp_apply, hb2, h1]
    rw [hv, mem_maximalIdeal] at h2
    exact h2 hr
  have haf : (e.comp c).Flat := RingHom.Flat.comp hcf hef
  have hbf : b.Flat := GlobalTheory.T.flat_of_flat_comp_of_map_maximalIdeal_eq O R' E φ' b het.1 het.2.1 hbl (by rw [hb1]; exact RingHom.Flat.comp hφ₁ haf)
  exact ⟨E, inferInstance, inferInstance, hdom, e.comp c, b, v, haf, hbf, hb1.symm, hv, hva, hb2, hmapE, hec⟩

end GlobalTheory

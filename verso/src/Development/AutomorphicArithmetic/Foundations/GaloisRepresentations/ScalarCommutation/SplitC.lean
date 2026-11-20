import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.T2SpaceAfP

set_option autoImplicit false

namespace UpperTheory.Gal.Spc

open UpperTheory.Gal.W2.Seed GlobalTheory.LKTrip GlobalTheory.UPel.HT

private def splitEquiv {X M : Type} [Group X] [Group M] (L : Loc X M) : X ≃* M × L.pr.ker where
  toFun g := (L.pr g, ⟨(L.loc (L.pr g))⁻¹ * g, by simp [MonoidHom.mem_ker, L.pr_loc]⟩)
  invFun x := L.loc x.1 * (x.2 : X)
  left_inv g := by simp
  right_inv x := by
    obtain ⟨m, h, hh⟩ := x
    have hh' : L.pr h = 1 := hh
    ext <;> simp [L.pr_loc, hh']
  map_mul' g h := by
    have hc : L.pr ((L.loc (L.pr g))⁻¹ * g) = 1 := by simp [L.pr_loc]
    have key := L.comm (L.pr h)⁻¹ _ hc
    rw [map_inv] at key
    refine Prod.ext (map_mul _ _ _) (Subtype.ext ?_)
    show (L.loc (L.pr (g * h)))⁻¹ * (g * h) = (L.loc (L.pr g))⁻¹ * g * ((L.loc (L.pr h))⁻¹ * h)
    rw [← mul_assoc ((L.loc (L.pr g))⁻¹ * g), ← key]
    simp [mul_assoc]

/- English proof (translation)
Use `haveI := GlobalTheory.GfTop.t2Space_afP p`. Use `haveI := GlobalTheory.GfTop.finiteAdeleRingAway_locallyCompactSpace p`. Use `haveI := GlobalTheory.GfTop.finiteAdeleRingAway_totallyDisconnectedSpace p`. Use `haveI := GlobalTheory.GfTop.finiteAdeleRingAway_secondCountableTopology p`. Conclude with `(GlobalTheory.GfTop.upts_props G.star (AfP p)).2.1`.
-/
private theorem t2Space_hTGroup_gAf {p : ℕ} [Fact p.Prime] (G : HTGroup p) : T2Space G.GAf := by
  haveI := GlobalTheory.GfTop.t2Space_afP p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_locallyCompactSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_totallyDisconnectedSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_secondCountableTopology p
  exact (GlobalTheory.GfTop.upts_props G.star (AfP p)).2.1

/- English proof (translation)
Introduce `p _ G Lv k _ _ _ _ P L hcont hat Kw hKo hKc hF`. Use `haveI := t2Space_hTGroup_gAf G`. Establish `hker : IsClosed (L.pr.ker : Set G.GAf)` using `isClosed_singleton.preimage hcont`. Use `⟨inferInstance, inferInstance, inferInstance, ⟨splitEquiv L, fun g => (hat g).symm, Kw, (Lv.K : Subgroup G.GAf).subgroupOf L.pr.ker, hKo, hKc, ?_, ?_, ?_⟩, fun g h => rfl⟩` and prove the remaining obligations. Conclude with `Lv.K.isOpen.preimage continuous_subtype_val`.

Conclude with `hker.isClosedEmbedding_subtypeVal.isCompact_preimage Lv.compact`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`. Use `⟨hF.2 g hg, ?_⟩` and prove the remaining obligations.

Use `show (L.loc (L.pr g))⁻¹ * g ∈ (Lv.K : Subgroup G.GAf)`. Conclude with `mul_mem (inv_mem (hF.1 _ (hF.2 g hg))) hg`. Introduce and unpack `⟨hm, hh⟩`. Conclude with `⟨L.loc x.1 * (x.2 : G.GAf), mul_mem (hF.1 _ hm) hh, (splitEquiv L).apply_symm_apply x⟩`.
-/
theorem splitC : SplitC := by
  intro p _ G Lv k _ _ _ _ P L hcont hat Kw hKo hKc hF
  haveI := t2Space_hTGroup_gAf G
  have hker : IsClosed (L.pr.ker : Set G.GAf) := isClosed_singleton.preimage hcont
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨splitEquiv L, fun g => (hat g).symm, Kw, (Lv.K : Subgroup G.GAf).subgroupOf L.pr.ker,
      hKo, hKc, ?_, ?_, ?_⟩, fun g h => rfl⟩
  · exact Lv.K.isOpen.preimage continuous_subtype_val
  · exact hker.isClosedEmbedding_subtypeVal.isCompact_preimage Lv.compact
  · ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hF.2 g hg, ?_⟩
      show (L.loc (L.pr g))⁻¹ * g ∈ (Lv.K : Subgroup G.GAf)
      exact mul_mem (inv_mem (hF.1 _ (hF.2 g hg))) hg
    · rintro ⟨hm, hh⟩
      exact ⟨L.loc x.1 * (x.2 : G.GAf), mul_mem (hF.1 _ hm) hh,
        (splitEquiv L).apply_symm_apply x⟩

end UpperTheory.Gal.Spc

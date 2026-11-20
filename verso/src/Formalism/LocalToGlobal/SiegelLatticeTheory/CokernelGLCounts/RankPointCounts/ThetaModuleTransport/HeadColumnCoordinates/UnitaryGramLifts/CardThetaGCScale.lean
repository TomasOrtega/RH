import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.GamConIff

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA7

variable {E : Type} [CommRing E] {O : Subring E} {cj : E →+* E} {qi : E} {r : ℕ} {T T' α : E} (q : E)

/- English proof (translation)
Establish `hc : (fun b => ((scPhi h Y (Sum.inl b) : O) : E) + q * (scPhi h Y (Sum.inr b) : O)) = fun b => cj (if b = Fin.last r then α else 1) * ((Y (Sum.inl b) : E) + q * Y (Sum.inr b))`. Use function extensionality and compare the values at `(phi_comb h q hq Y)`. Establish `hl : (fun a => ((scPhi h Y' (Sum.inl a) : O) : E)) = fun a => (Y' (Sum.inl a) : E)` using `funext (phi_inl h Y')`. Establish `hz` using `phi_comb h q hq Y' (Fin.last r)`. Simplify using `only [if_true] at hz`.

Simplify using `only [scTr, scBar_mk, psiD, Prod.mk.injEq]`. Use `⟨trivial, trivial, ⟨phi_inl h Y _, ?_⟩, ?_, hz⟩` and prove the remaining obligations. Rewrite using `[hc, lamStarC_scale h Zh]`. Rewrite using `[hl, lamC_scale h Zh]`.
-/
theorem gamTup_scale (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (Y Y' Y'' : Ix r → O) :
    ((Submodule.Quotient.mk (scPhi h Y) : DDg O cj qi (Zh * dlast r α) T T'),
      (Submodule.Quotient.mk (scPhi h Y'') : DDg O cj qi (Zh * dlast r α) T T'),
      (((scPhi h Y (Sum.inl (Fin.last r)) : O) : E),
        lamStarC cj (Zh * dlast r α) (fun b => ((scPhi h Y (Sum.inl b) : O) : E) + q * (scPhi h Y (Sum.inr b) : O))),
      (lamC (Zh * dlast r α) (fun a => ((scPhi h Y' (Sum.inl a) : O) : E)),
        ((scPhi h Y' (Sum.inl (Fin.last r)) : O) : E) + q * (scPhi h Y' (Sum.inr (Fin.last r)) : O))) =
    scTr h Zh ((Submodule.Quotient.mk Y : DDg O cj qi Zh T T'), (Submodule.Quotient.mk Y'' : DDg O cj qi Zh T T'),
      ((Y (Sum.inl (Fin.last r)) : E), lamStarC cj Zh (fun b => (Y (Sum.inl b) : E) + q * Y (Sum.inr b))),
      (lamC Zh (fun a => (Y' (Sum.inl a) : E)), (Y' (Sum.inl (Fin.last r)) : E) + q * Y' (Sum.inr (Fin.last r)))) := by
  have hc : (fun b => ((scPhi h Y (Sum.inl b) : O) : E) + q * (scPhi h Y (Sum.inr b) : O)) =
      fun b => cj (if b = Fin.last r then α else 1) * ((Y (Sum.inl b) : E) + q * Y (Sum.inr b)) :=
    funext (phi_comb h q hq Y)
  have hl : (fun a => ((scPhi h Y' (Sum.inl a) : O) : E)) = fun a => (Y' (Sum.inl a) : E) := funext (phi_inl h Y')
  have hz := phi_comb h q hq Y' (Fin.last r)
  simp only [if_true] at hz
  simp only [scTr, scBar_mk, psiD, Prod.mk.injEq]
  refine ⟨trivial, trivial, ⟨phi_inl h Y _, ?_⟩, ?_, hz⟩
  · rw [hc, lamStarC_scale h Zh]
  · rw [hl, lamC_scale h Zh]

/- English proof (translation)
Use extensionality with `p`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Y, Y', Y'', c1, c2, c3, rfl⟩`. Establish `hc` using `(gamCon_iff q h hqO ((scPhi h).symm Y) ((scPhi h).symm Y') ((scPhi h).symm Y'')).2`. Simplify using `only [LinearEquiv.apply_symm_apply] at hc`.

Take `⟨d1, d2, d3⟩` from `hc ⟨c1, c2, c3⟩`. Use `⟨_, ⟨(scPhi h).symm Y, (scPhi h).symm Y', (scPhi h).symm Y'', d1, d2, d3, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← gamTup_scale q h hq]`. Simplify using `only [LinearEquiv.apply_symm_apply]`. Introduce and unpack `⟨_, ⟨Y, Y', Y'', c1, c2, c3, rfl⟩, rfl⟩`.

Take `⟨d1, d2, d3⟩` from `(gamCon_iff q h hqO Y Y' Y'').1 ⟨c1, c2, c3⟩`. Conclude with `⟨scPhi h Y, scPhi h Y', scPhi h Y'', d1, d2, d3, (gamTup_scale q h hq Zh Y Y' Y'').symm⟩`.
-/
theorem gamRC_scale (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (hqO : q ∈ O)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    GamRC O cj q qi (Zh * dlast r α) T T' = scTr h Zh '' GamRC O cj q qi Zh T T' := by
  ext p
  constructor
  · rintro ⟨Y, Y', Y'', c1, c2, c3, rfl⟩
    have hc := (gamCon_iff q h hqO ((scPhi h).symm Y) ((scPhi h).symm Y') ((scPhi h).symm Y'')).2
    simp only [LinearEquiv.apply_symm_apply] at hc
    obtain ⟨d1, d2, d3⟩ := hc ⟨c1, c2, c3⟩
    refine ⟨_, ⟨(scPhi h).symm Y, (scPhi h).symm Y', (scPhi h).symm Y'', d1, d2, d3, rfl⟩, ?_⟩
    rw [← gamTup_scale q h hq]
    simp only [LinearEquiv.apply_symm_apply]
  · rintro ⟨_, ⟨Y, Y', Y'', c1, c2, c3, rfl⟩, rfl⟩
    obtain ⟨d1, d2, d3⟩ := (gamCon_iff q h hqO Y Y' Y'').1 ⟨c1, c2, c3⟩
    exact ⟨scPhi h Y, scPhi h Y', scPhi h Y'', d1, d2, d3, (gamTup_scale q h hq Zh Y Y' Y'').symm⟩

/- English proof (translation)
Rewrite using `[LinearEquiv.symm_apply_eq, scBar_mk, LinearEquiv.apply_symm_apply]`.
-/
theorem scBar_symm_mk (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Y : Ix r → O) :
    (scBar h Zh).symm (Submodule.Quotient.mk Y) = Submodule.Quotient.mk ((scPhi h).symm Y) := by
  rw [LinearEquiv.symm_apply_eq, scBar_mk, LinearEquiv.apply_symm_apply]

def scConj (h : ScHyp O cj qi T T' α) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    (DDg O cj qi Zh₁ T T' ≃ₗ[O] DDg O cj qi Zh₂ T T') ≃
      (DDg O cj qi (Zh₁ * dlast r α) T T' ≃ₗ[O] DDg O cj qi (Zh₂ * dlast r α) T T') where
  toFun θ := (scBar h Zh₁).symm.trans (θ.trans (scBar h Zh₂))
  invFun θ' := (scBar h Zh₁).trans (θ'.trans (scBar h Zh₂).symm)
  left_inv θ := by ext x; simp
  right_inv θ' := by ext x; simp

/- English proof (translation)
Establish `hθ' : ∀ Y : Ix r → O, scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h Y)) = scBar h Zh₂ (θ (Submodule.Quotient.mk Y))`. Introduce `Y`. Use `show scBar h Zh₂ (θ ((scBar h Zh₁).symm (Submodule.Quotient.mk (scPhi h Y)))) = _`. Rewrite using `[scBar_symm_mk, LinearEquiv.symm_apply_apply]`. Establish `hcomm : (fun p => (scConj h Zh₁ Zh₂ θ p.1, scConj h Zh₁ Zh₂ θ p.2.1, p.2.2.1, p.2.2.2)) ∘ scTr h Zh₁ = scTr h Zh₂ ∘ (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2))`.

Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, scTr]`. Use `show (scBar h Zh₂ (θ ((scBar h Zh₁).symm (scBar h Zh₁ p.1))), scBar h Zh₂ (θ ((scBar h Zh₁).symm (scBar h Zh₁ p.2.1))), _) = _`. Simplify using `only [LinearEquiv.symm_apply_apply]`. Unfold `ThetaGC`.

Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[gamRC_scale q h hq hqO Zh₁, gamRC_scale q h hq hqO Zh₂, Set.image_image]`. Rewrite using `[show (fun p => (scConj h Zh₁ Zh₂ θ (scTr h Zh₁ p).1, scConj h Zh₁ Zh₂ θ (scTr h Zh₁ p).2.1, (scTr h Zh₁ p).2.2.1, (scTr h Zh₁ p).2.2.2)) = scTr h Zh₂ ∘ (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)) from hcomm, Set.image_comp, (Set.image_injective.2 (scTr_inj h Zh₂)).eq_iff]`. Use `and_congr ?_ Iff.rfl` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `hF Y W Y₂ W₂ hY hW`. Establish `eY : θ (Submodule.Quotient.mk ((scPhi h).symm Y)) = Submodule.Quotient.mk ((scPhi h).symm Y₂)`. Rewrite using `[← scBar_symm_mk h Zh₁, ← scBar_symm_mk h Zh₂, LinearEquiv.eq_symm_apply]`. Conclude with `hY`. Establish `eW : θ (Submodule.Quotient.mk ((scPhi h).symm W)) = Submodule.Quotient.mk ((scPhi h).symm W₂)`.

Rewrite using `[← scBar_symm_mk h Zh₁, ← scBar_symm_mk h Zh₂, LinearEquiv.eq_symm_apply]`. Conclude with `hW`. Use `hF _ _ _ _ eY eW` as an intermediate fact. Rewrite `this` using `[← formG_scale h Zh₂, ← formG_scale h Zh₁]`. Simplify `this` using `only [LinearEquiv.apply_symm_apply]`.

Introduce `hF Y W Y₂ W₂ hY hW`. Establish `eY : scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h Y)) = Submodule.Quotient.mk (scPhi h Y₂)`. Rewrite using `[hθ', hY, scBar_mk]`. Establish `eW : scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h W)) = Submodule.Quotient.mk (scPhi h W₂)`. Rewrite using `[hθ', hW, scBar_mk]`.

Use `hF _ _ _ _ eY eW` as an intermediate fact. Rewrite `this` using `[formG_scale h Zh₂, formG_scale h Zh₁]`. Then use the resulting hypothesis.
-/
theorem thetaGC_scale_iff (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (hqO : q ∈ O)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (θ : DDg O cj qi Zh₁ T T' ≃ₗ[O] DDg O cj qi Zh₂ T T') :
    θ ∈ ThetaGC O cj q qi Zh₁ Zh₂ T T' ↔
      scConj h Zh₁ Zh₂ θ ∈ ThetaGC O cj q qi (Zh₁ * dlast r α) (Zh₂ * dlast r α) T T' := by
  have hθ' : ∀ Y : Ix r → O, scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h Y)) =
      scBar h Zh₂ (θ (Submodule.Quotient.mk Y)) := by
    intro Y
    show scBar h Zh₂ (θ ((scBar h Zh₁).symm (Submodule.Quotient.mk (scPhi h Y)))) = _
    rw [scBar_symm_mk, LinearEquiv.symm_apply_apply]
  have hcomm : (fun p => (scConj h Zh₁ Zh₂ θ p.1, scConj h Zh₁ Zh₂ θ p.2.1, p.2.2.1, p.2.2.2)) ∘ scTr h Zh₁ =
      scTr h Zh₂ ∘ (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)) := by
    funext p
    simp only [Function.comp_apply, scTr]
    show (scBar h Zh₂ (θ ((scBar h Zh₁).symm (scBar h Zh₁ p.1))),
      scBar h Zh₂ (θ ((scBar h Zh₁).symm (scBar h Zh₁ p.2.1))), _) = _
    simp only [LinearEquiv.symm_apply_apply]
  unfold ThetaGC
  simp only [Set.mem_setOf_eq]
  rw [gamRC_scale q h hq hqO Zh₁, gamRC_scale q h hq hqO Zh₂, Set.image_image]
  rw [show (fun p => (scConj h Zh₁ Zh₂ θ (scTr h Zh₁ p).1, scConj h Zh₁ Zh₂ θ (scTr h Zh₁ p).2.1,
      (scTr h Zh₁ p).2.2.1, (scTr h Zh₁ p).2.2.2)) = scTr h Zh₂ ∘ (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)) from
      hcomm, Set.image_comp, (Set.image_injective.2 (scTr_inj h Zh₂)).eq_iff]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro hF Y W Y₂ W₂ hY hW
    have eY : θ (Submodule.Quotient.mk ((scPhi h).symm Y)) = Submodule.Quotient.mk ((scPhi h).symm Y₂) := by
      rw [← scBar_symm_mk h Zh₁, ← scBar_symm_mk h Zh₂, LinearEquiv.eq_symm_apply]; exact hY
    have eW : θ (Submodule.Quotient.mk ((scPhi h).symm W)) = Submodule.Quotient.mk ((scPhi h).symm W₂) := by
      rw [← scBar_symm_mk h Zh₁, ← scBar_symm_mk h Zh₂, LinearEquiv.eq_symm_apply]; exact hW
    have := hF _ _ _ _ eY eW
    rw [← formG_scale h Zh₂, ← formG_scale h Zh₁] at this
    simpa only [LinearEquiv.apply_symm_apply] using this
  · intro hF Y W Y₂ W₂ hY hW
    have eY : scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h Y)) = Submodule.Quotient.mk (scPhi h Y₂) := by
      rw [hθ', hY, scBar_mk]
    have eW : scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h W)) = Submodule.Quotient.mk (scPhi h W₂) := by
      rw [hθ', hW, scBar_mk]
    have := hF _ _ _ _ eY eW
    rwa [formG_scale h Zh₂, formG_scale h Zh₁] at this

/- English proof (translation)
The claim follows from `(Nat.card_congr ((scConj h Zh₁ Zh₂).subtypeEquiv (thetaGC_scale_iff q h hq hqO Zh₁ Zh₂))).symm`.
-/
theorem card_thetaGC_scale (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (hqO : q ∈ O)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Nat.card (ThetaGC O cj q qi (Zh₁ * dlast r α) (Zh₂ * dlast r α) T T') = Nat.card (ThetaGC O cj q qi Zh₁ Zh₂ T T') :=
  (Nat.card_congr ((scConj h Zh₁ Zh₂).subtypeEquiv (thetaGC_scale_iff q h hq hqO Zh₁ Zh₂))).symm

end ScaleA7

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `phiFun_of_globalFns hG R I D F k hk p w hw`. Take `⟨Φ', hΦ'⟩` from `phiFun_of_globalFns hG R I D F k hk p' w' hw'`. Establish `r : ∀ s, PhiRel D.toPre F k p w s (Φ s)` using `fun s => (hΦ _ _).2 rfl`. Establish `r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ' s)` using `fun s => (hΦ' _ _).2 rfl`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨s, s₃, s₄, h₃, h₄, h0⟩` from `hne`. Establish `a` using `(isSmul_iff _ _ _).1 (h w w' hw hw' s _ _ s₃ s₄ (r' s) (r _) h₃ h₄)`. Establish `b` using `H s _ _ s₃ s₄ (r' s) (r _) h₃ h₄`. Conclude with `smul_left_injective F h0 (a.symm.trans b)`.

Introduce and unpack `rfl v v' hv hv' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄`. Take `⟨c, -, hc⟩` from `TorsionImage.exists_smul_of_phiVal p w v hw hv`. Take `⟨c', -, hc'⟩` from `TorsionImage.exists_smul_of_phiVal p' w' v' hw' hv'`. Establish `q : ∀ s t, PhiRel D.toPre F k p v s t → t = c • Φ s` using `fun s t h => hc s _ t ((phiRel_iff hG p w hw _ _).1 (r s)) ((phiRel_iff hG p v hv _ _).1 h)`. Establish `q' : ∀ s t, PhiRel D.toPre F k p' v' s t → t = c' • Φ' s` using `fun s t h => hc' s _ t ((phiRel_iff hG p' w' hw' _ _).1 (r' s)) ((phiRel_iff hG p' v' hv' _ _).1 h)`.

Rewrite using `[isSmul_iff, q _ _ h₂, q' _ _ h₁, q' _ _ h₄, q _ _ h₃, map_smul, map_smul, H s _ _ _ _ (r' s) (r _) (r s) (r' _), smul_comm c' ζ, smul_comm c ζ, smul_comm c c']`.
-/
theorem weilQkIs_iff_of_comm (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (D : DegData R I) {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
    (p p' : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b) (w' : Frm D.toPre F k p'.g.b)
    (hw : w.IsGen) (hw' : w'.IsGen) (z : F)
    (H : ∀ s s₁ s₂ s₃ s₄ : Fam D.toPre F k, PhiRel D.toPre F k p' w' s s₁ → PhiRel D.toPre F k p w s₁ s₂ →
      PhiRel D.toPre F k p w s s₃ → PhiRel D.toPre F k p' w' s₃ s₄ → s₂ = z • s₄)
    (hne : ∃ s s₃ s₄ : Fam D.toPre F k, PhiRel D.toPre F k p w s s₃ ∧ PhiRel D.toPre F k p' w' s₃ s₄ ∧ s₄ ≠ 0)
    (hk : 1 ≤ k) (ζ : F) : WeilQkIs D.toPre F k p p' ζ ↔ ζ = z := by
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R I D F k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG R I D F k hk p' w' hw'
  have r : ∀ s, PhiRel D.toPre F k p w s (Φ s) := fun s => (hΦ _ _).2 rfl
  have r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ' s) := fun s => (hΦ' _ _).2 rfl
  constructor
  · intro h
    obtain ⟨s, s₃, s₄, h₃, h₄, h0⟩ := hne
    have a := (isSmul_iff _ _ _).1 (h w w' hw hw' s _ _ s₃ s₄ (r' s) (r _) h₃ h₄)
    have b := H s _ _ s₃ s₄ (r' s) (r _) h₃ h₄
    exact smul_left_injective F h0 (a.symm.trans b)
  · rintro rfl v v' hv hv' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
    obtain ⟨c, -, hc⟩ := TorsionImage.exists_smul_of_phiVal p w v hw hv
    obtain ⟨c', -, hc'⟩ := TorsionImage.exists_smul_of_phiVal p' w' v' hw' hv'
    have q : ∀ s t, PhiRel D.toPre F k p v s t → t = c • Φ s := fun s t h =>
      hc s _ t ((phiRel_iff hG p w hw _ _).1 (r s)) ((phiRel_iff hG p v hv _ _).1 h)
    have q' : ∀ s t, PhiRel D.toPre F k p' v' s t → t = c' • Φ' s := fun s t h =>
      hc' s _ t ((phiRel_iff hG p' w' hw' _ _).1 (r' s)) ((phiRel_iff hG p' v' hv' _ _).1 h)
    rw [isSmul_iff, q _ _ h₂, q' _ _ h₁, q' _ _ h₄, q _ _ h₃, map_smul, map_smul,
      H s _ _ _ _ (r' s) (r _) (r s) (r' _), smul_comm c' ζ, smul_comm c ζ, smul_comm c c']

/- English proof (translation)
Introduce `hL R _ _ _ I _ D A G _ _ _ U F _ _ _ k hk p p' x x' hx hx' ζ`. Establish `hG` using `hL.1.globalFns`. Take `⟨w₀, hw₀⟩` from `U.ext`. Take `⟨θ, rfl, -⟩` from `TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x (hx w₀ hw₀).1`. Take `⟨θ', rfl, -⟩` from `TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x' (hx' w₀ hw₀).1`.

Take `⟨w, hw, h⟩` from `(hx w₀ hw₀).2 θ rfl`. Take `⟨w', hw', h'⟩` from `(hx' w₀ hw₀).2 θ' rfl`. Take `⟨e, he⟩` from `exists_linearEquiv_expandsF hG U F hk w₀ hw₀`. Take `⟨ρ, hρ, hcomm, -⟩` from `thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)`. Take `⟨c, hc⟩` from `CommutatorPairing.exists_commIsOf hG A.isAb A.isLB θ θ'`.

Take `⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c` from `⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, Units.ext (by simp [unitOn])⟩`. Set `E : SecM A.A A.L (k : ℤ) (TFK (R` to `R) F) → Fam D.toPre F k := fun v => e (SecM.toSec A.A v)`. Establish `hE : ∀ s, ∃ v, E v = s` using `fun s => ⟨SecM.ofSec A.A (e.symm s), e.apply_symm_apply s⟩`. Establish `a : ∀ v, PhiRel D.toPre F k p w (E v) (E (ρ θ v))` using `fun v => h _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)`. Establish `a' : ∀ v, PhiRel D.toPre F k p' w' (E v) (E (ρ θ' v))` using `fun v => h' _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)`.

Establish `b : ∀ v t, PhiRel D.toPre F k p w (E v) t → t = E (ρ θ v)` using `fun v t H => phi_unique p w ((phiRel_iff hG p w hw _ _).1 H) ((phiRel_iff hG p w hw _ _).1 (a v))`. Establish `b' : ∀ v t, PhiRel D.toPre F k p' w' (E v) t → t = E (ρ θ' v)` using `fun v t H => phi_unique p' w' ((phiRel_iff hG p' w' hw' _ _).1 H) ((phiRel_iff hG p' w' hw' _ _).1 (a' v))`. Establish `key` using `weilQkIs_iff_of_comm hG D p p' w w' hw hw' (z : F) (fun s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ => by`. Take `⟨v, rfl⟩` from `hE s`. Take `rfl` from `b' _ _ h₁`.

Take `rfl` from `b _ _ h₂`. Take `rfl` from `b _ _ h₃`. Take `rfl` from `b' _ _ h₄`. Rewrite using `[hcomm θ θ' _ hc v]`. Conclude with `e.map_smul (z : F) (SecM.toSec A.A (ρ θ' (ρ θ v)))) (by`.

Take `⟨B, hB, -⟩` from `BoxSpan.exists_basis hL.1.secBaseChange A k hk F (jFK (R := R) F)`. Establish `: Nontrivial Γ((TFK (R` using `R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial`. Establish `hne` using `hB.ne_zero ⟨0, pow_pos hk _⟩`. Use `⟨_, _, _, a (B ⟨0, pow_pos hk _⟩), a' _, fun h0 => hne ?_⟩` and prove the remaining obligations. Establish `h1 : SecM.toSec A.A (ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩))) = _` using `e.map_eq_zero_iff.1 h0`.

Establish `h2 : ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩)) = 0` using `congrArg (SecM.ofSec A.A) h1`. Conclude with `(ρ θ).map_eq_zero_iff.1 ((ρ θ').map_eq_zero_iff.1 h2)) hk (ζ : F)`. Establish `hz` using `GlobalLift.weilIs_of_commIsOf hG A.isAb A.isLB hc`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion.

Introduce `H`. Take `rfl : ζ = z` from `Units.ext H`. Conclude with `hz`. Introduce `H`. Conclude with `congrArg Units.val (H1.unitOn_injective (CommutatorPairing.weilIs_unique hG A.isAb A.isLB H hz))`.
-/
theorem weilQkIs_iff_weilIs : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ) := by
  intro hL R _ _ _ I _ D A G _ _ _ U F _ _ _ k hk p p' x x' hx hx' ζ
  have hG := hL.1.globalFns
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  obtain ⟨ρ, hρ, hcomm, -⟩ := thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_commIsOf hG A.isAb A.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, Units.ext (by simp [unitOn])⟩
  let E : SecM A.A A.L (k : ℤ) (TFK (R := R) F) → Fam D.toPre F k := fun v => e (SecM.toSec A.A v)
  have hE : ∀ s, ∃ v, E v = s := fun s => ⟨SecM.ofSec A.A (e.symm s), e.apply_symm_apply s⟩
  have a : ∀ v, PhiRel D.toPre F k p w (E v) (E (ρ θ v)) := fun v =>
    h _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have a' : ∀ v, PhiRel D.toPre F k p' w' (E v) (E (ρ θ' v)) := fun v =>
    h' _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have b : ∀ v t, PhiRel D.toPre F k p w (E v) t → t = E (ρ θ v) := fun v t H =>
    phi_unique p w ((phiRel_iff hG p w hw _ _).1 H) ((phiRel_iff hG p w hw _ _).1 (a v))
  have b' : ∀ v t, PhiRel D.toPre F k p' w' (E v) t → t = E (ρ θ' v) := fun v t H =>
    phi_unique p' w' ((phiRel_iff hG p' w' hw' _ _).1 H) ((phiRel_iff hG p' w' hw' _ _).1 (a' v))
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' (z : F) (fun s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ => by
    obtain ⟨v, rfl⟩ := hE s
    obtain rfl := b' _ _ h₁
    obtain rfl := b _ _ h₂
    obtain rfl := b _ _ h₃
    obtain rfl := b' _ _ h₄
    rw [hcomm θ θ' _ hc v]
    exact e.map_smul (z : F) (SecM.toSec A.A (ρ θ' (ρ θ v)))) (by
    obtain ⟨B, hB, -⟩ := BoxSpan.exists_basis hL.1.secBaseChange A k hk F (jFK (R := R) F)
    have : Nontrivial Γ((TFK (R := R) F).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    have hne := hB.ne_zero ⟨0, pow_pos hk _⟩
    refine ⟨_, _, _, a (B ⟨0, pow_pos hk _⟩), a' _, fun h0 => hne ?_⟩
    have h1 : SecM.toSec A.A (ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩))) = _ := e.map_eq_zero_iff.1 h0
    have h2 : ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩)) = 0 := congrArg (SecM.ofSec A.A) h1
    exact (ρ θ).map_eq_zero_iff.1 ((ρ θ').map_eq_zero_iff.1 h2)) hk (ζ : F)
  have hz := GlobalLift.weilIs_of_commIsOf hG A.isAb A.isLB hc
  rw [key]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective (CommutatorPairing.weilIs_unique hG A.isAb A.isLB H hz))

end GlobalTheory.UT

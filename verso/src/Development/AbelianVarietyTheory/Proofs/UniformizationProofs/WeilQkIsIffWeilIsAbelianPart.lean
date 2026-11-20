import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorsProjectiveRepresentation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaPow
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.WeilAbelianPart

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
The claim follows from `(_root_.mul_comm (fst (TF (R := R) F) D.P.A ≫ b) (DegPre.prB D F)).trans (tr_pr D F b).symm`.
-/
theorem translPt_eq (b : TF (R := R) F ⟶ D.P.A) : translPt D.P.A b = DegPre.trPt D F b ≫ DegPre.prB D F :=
  (_root_.mul_comm (fst (TF (R := R) F) D.P.A ≫ b) (DegPre.prB D F)).trans (tr_pr D F b).symm

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[tr_fst, translT, lift_fst]`. Rewrite using `[translT, lift_snd, translPt_eq]`.
-/
theorem translT_eq (b : TF (R := R) F ⟶ D.P.A) : translT D.P.A b = DegPre.trPt D F b := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [tr_fst, translT, lift_fst]
  · rw [translT, lift_snd, translPt_eq]

/- English proof (translation)
Take `⟨⟨u, hu, hc⟩, hv⟩` from `gen_phi hG p w hw 0`. Take `⟨v, hvg, hvv⟩` from `exists_gen D.P.isLB (K' := Fin 2) (φ' := ![(snd (TF (R := R) F) D.P.A).left, (translPt D.P.A p.g.b).left]) (ε' := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by`. Establish `a` using `ThetaPow.prod_fam_zero D F k (fun q => h ((DegPre.trPt D F p.g.b).left ≫ q))`. Establish `c : ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε k i = h (DegPre.prB D F).left ^ k`. Rewrite using `[hy, add_zero]`.

Conclude with `ThetaPow.prod_fam_zero D F k h`. Use `Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ c (prod_neg _ _ a)) ?_` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_two, translPt_eq]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast, Over.comp_left]) u hu`. Use `⟨⟨p.g.b, v, hvg⟩, rfl, fun s t H ρ z J hJ => ?_⟩` and prove the remaining obligations.

Establish `e` using `(phiRel_iff hG p w hw s t).1 H 0 0 (by rw [hy, add_zero]) _ ρ z J hJ`. Rewrite `e` using `[← hv u hu hc _ ρ z J hJ, ← hvv _ _ z J hJ]`. Conclude with `e`.
-/
theorem exists_theta (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) (hy : p.y = 0) (w : Frm D F k p.g.b)
    (hw : w.IsGen) : ∃ θ : ThetaGrp D.P.A D.P.L (k : ℤ) (TF (R := R) F), θ.pt = p.g.b ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → ∀ (ρ : DegPre.BF D F ⟶ DegPre.BF D F) z J, Good D.P.L z J →
        sval (t.s 0) ρ.left z J = sval (s.s 0) (ρ ≫ DegPre.trPt D F p.g.b).left z J *
          (CommPairing.tval θ ρ.left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_phi hG p w hw 0
  obtain ⟨v, hvg, hvv⟩ := exists_gen D.P.isLB (K' := Fin 2)
    (φ' := ![(snd (TF (R := R) F) D.P.A).left, (translPt D.P.A p.g.b).left])
    (ε' := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
      have a := ThetaPow.prod_fam_zero D F k (fun q => h ((DegPre.trPt D F p.g.b).left ≫ q))
      have c : ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε k i = h (DegPre.prB D F).left ^ k := by
        rw [hy, add_zero]; exact ThetaPow.prod_fam_zero D F k h
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ c (prod_neg _ _ a)) ?_
      rw [Fin.prod_univ_two, translPt_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast, Over.comp_left]) u hu
  refine ⟨⟨p.g.b, v, hvg⟩, rfl, fun s t H ρ z J hJ => ?_⟩
  have e := (phiRel_iff hG p w hw s t).1 H 0 0 (by rw [hy, add_zero]) _ ρ z J hJ
  rw [← hv u hu hc _ ρ z J hJ, ← hvv _ _ z J hJ] at e
  exact e

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `hs fun j => sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j` and prove the remaining obligations. Establish `e : s = (c - c')⁻¹ • (c • s + (-1 : F) • c' • s)`. Rewrite using `[neg_one_smul, ← sub_eq_add_neg, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul]`. Establish `e₀ : c' • s + (-1 : F) • c' • s = 0` using `by rw [neg_one_smul, add_neg_cancel]`.

Establish `e₁` using `sval_add (c' • s) ((-1 : F) • c' • s) 0 (𝟙 _) y hJ`. Rewrite `e₁` using `[e₀, UUA.sval_zero_of (s := (0 : Fam D F k).s 0) (fun _ => rfl) _ y J (hJ.mem _ _)]`. Rewrite using `[e, sval_smul _ _ _ _ y hJ, sval_add _ _ _ _ y hJ, h y J hJ, ← e₁, mul_zero, UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]`.
-/
theorem eq_of_sval {k : ℕ} (s : Fam D F k) (hs : ¬ ∀ j, (s.s 0).f j = 0) {c c' : F}
    (h : ∀ y J, Good D.P.L y J → sval ((c • s).s 0) (𝟙 _) y J = sval ((c' • s).s 0) (𝟙 _) y J) : c = c' := by
  by_contra hne
  refine hs fun j => sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e : s = (c - c')⁻¹ • (c • s + (-1 : F) • c' • s) := by
    rw [neg_one_smul, ← sub_eq_add_neg, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul]
  have e₀ : c' • s + (-1 : F) • c' • s = 0 := by rw [neg_one_smul, add_neg_cancel]
  have e₁ := sval_add (c' • s) ((-1 : F) • c' • s) 0 (𝟙 _) y hJ
  rw [e₀, UUA.sval_zero_of (s := (0 : Fam D F k).s 0) (fun _ => rfl) _ y J (hJ.mem _ _)] at e₁
  rw [e, sval_smul _ _ _ _ y hJ, sval_add _ _ _ _ y hJ, h y J hJ, ← e₁, mul_zero,
    UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]

attribute [local instance] TorusExt.gtGroup in
/- English proof (translation)
Establish `: TorusExt.qkAdd hB p p' = TorusExt.qkAdd hB p' p` using `TorusExt.qk_ext (add_comm _ _) (add_comm p.g p'.g)`. Rewrite using `[this]`. Conclude with `TorusExt.qkAdd_qkAdd hB p' p`.
-/
theorem qkAdd_swap (hB : D.TauBimult) {k : ℕ} (p p' : QkPt D F k) : QkAdd p' p (TorusExt.qkAdd hB p p') := by
  have : TorusExt.qkAdd hB p p' = TorusExt.qkAdd hB p' p := TorusExt.qk_ext (add_comm _ _) (add_comm p.g p'.g)
  rw [this]
  exact TorusExt.qkAdd_qkAdd hB p' p

/- English proof (translation)
Introduce `hL R _ _ _ I hI D F _ _ _ k hk p p' hy hy' ζ`. Establish `hG` using `hL.1.globalFns`. Establish `hB` using `D.tau_bimult`. Take `⟨Φ, h₁, -, h₃, -, h₅, -⟩` from `PhiProj.phi_projective hL R I hI D F k hk`. Take `⟨w, hw⟩` from `(CoefBasic.coef_basic R D.toPre F k p.g).1`.

Take `⟨w', hw'⟩` from `(CoefBasic.coef_basic R D.toPre F k p'.g).1`. Take `⟨v, hv, ev⟩` from `h₅ p p' _ w w' hw hw' (TorusExt.qkAdd_qkAdd hB p p')`. Take `⟨v', hv', ev'⟩` from `h₅ p' p _ w' w hw' hw (qkAdd_swap hB p p')`. Take `⟨c, -, hc⟩` from `h₃ _ v' v hv' hv`. Rewrite `hc` using `[ev, ev']`.

Establish `hc' : ∀ s, Φ p w (Φ p' w' s) = c • Φ p' w' (Φ p w s)` using `fun s => LinearMap.congr_fun hc s`. Establish `r : ∀ s, PhiRel D.toPre F k p w s (Φ p w s)` using `fun s => ((h₁ p w hw).2 _ _).2 rfl`. Establish `r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ p' w' s)` using `fun s => ((h₁ p' w' hw').2 _ _).2 rfl`. Take `⟨σ, hσ⟩` from `FamFree.exists_sec_ne_zero (D := D.toPre) (F := F) hL.2.1.secTwist hk 0`. Take `⟨t, rfl, -⟩` from `FamFree.exists_fam_single hG hB hk 0 σ`.

Take `⟨t, rfl⟩` from `(h₁ p' w' hw').1.2 t`. Take `⟨s, rfl⟩` from `(h₁ p w hw).1.2 t`. Establish `key` using `weilQkIs_iff_of_comm hG D p p' w w' hw hw' c (fun s s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ => by`. Rewrite using `[((h₁ p w hw).2 _ _).1 a₂, ((h₁ p' w' hw').2 _ _).1 a₁, ((h₁ p' w' hw').2 _ _).1 a₄, ((h₁ p w hw).2 _ _).1 a₃, hc']) ⟨s, _, _, r s, r' _, fun h0 => hσ fun j => by rw [h0]; rfl⟩ hk (ζ : F)`. Take `⟨θ, hp, hθ⟩` from `exists_theta hG p hy w hw`.

Take `⟨θ', hp', hθ'⟩` from `exists_theta hG p' hy' w' hw'`. Take `⟨c₀, hc₀⟩` from `CommutatorPairing.exists_commIsOf hG D.toPre.P.isAb D.toPre.P.isLB θ θ'`. Take `⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c₀` from `⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c₀, Units.ext (by simp [unitOn])⟩`. Establish `hz` using `GlobalLift.weilIs_of_commIsOf hG D.toPre.P.isAb D.toPre.P.isLB hc₀`. Rewrite `hz` using `[hp, hp']`.

Establish `hcz : c = (z : F)` using `eq_of_sval _ hσ fun y J hJ => by`. Establish `e` using `congrArg Units.val ((CommPairing.commIsOf_iff D.toPre.P.isLB θ θ' _).1 hc₀ _ (𝟙 _) y J hJ)`. Rewrite `e` using `[Units.val_mul, Units.val_mul, Units.val_mul, ← gs_unit _ _ ⊤ trivial, hp, hp', translT_eq, translT_eq]`. Establish `a₂` using `hθ _ _ (r (Φ p' w' s)) (𝟙 _) y J hJ`. Establish `a₁` using `hθ' _ _ (r' s) (𝟙 _ ≫ DegPre.trPt D.toPre F p.g.b) y J hJ`.

Establish `a₄` using `hθ' _ _ (r' (Φ p w s)) (𝟙 _) y J hJ`. Establish `a₃` using `hθ _ _ (r s) (𝟙 _ ≫ DegPre.trPt D.toPre F p'.g.b) y J hJ`. Rewrite `a₂` using `[a₁]`. Rewrite `a₄` using `[a₃]`. Simplify using `only [Category.id_comp, Over.id_left] at a₂ a₄ e`.

Rewrite using `[← hc', sval_smul _ _ _ _ y hJ, a₂, a₄, tr_comm, _root_.mul_assoc, _root_.mul_comm (Units.val _), e, Category.id_comp]`. Use `show _ * (_ * _ * gs _ y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (z : F))) = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, hcz]`. Prove the components needed by the constructor for the conclusion.

Introduce `H`. Take `rfl : ζ = z` from `Units.ext H`. Conclude with `hz`. Introduce `H`. Conclude with `congrArg Units.val (H1.unitOn_injective (CommutatorPairing.weilIs_unique hG D.toPre.P.isAb D.toPre.P.isLB H hz))`.
-/
theorem weilQkIs_iff_weilIs_abelianPart : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, p.y = 0 → p'.y = 0 → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs D.toPre.P.A D.toPre.P.L k p.g.b p'.g.b (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ) := by
  intro hL R _ _ _ I hI D F _ _ _ k hk p p' hy hy' ζ
  have hG := hL.1.globalFns
  have hB := D.tau_bimult
  obtain ⟨Φ, h₁, -, h₃, -, h₅, -⟩ := PhiProj.phi_projective hL R I hI D F k hk
  obtain ⟨w, hw⟩ := (CoefBasic.coef_basic R D.toPre F k p.g).1
  obtain ⟨w', hw'⟩ := (CoefBasic.coef_basic R D.toPre F k p'.g).1
  obtain ⟨v, hv, ev⟩ := h₅ p p' _ w w' hw hw' (TorusExt.qkAdd_qkAdd hB p p')
  obtain ⟨v', hv', ev'⟩ := h₅ p' p _ w' w hw' hw (qkAdd_swap hB p p')
  obtain ⟨c, -, hc⟩ := h₃ _ v' v hv' hv
  rw [ev, ev'] at hc
  have hc' : ∀ s, Φ p w (Φ p' w' s) = c • Φ p' w' (Φ p w s) := fun s => LinearMap.congr_fun hc s
  have r : ∀ s, PhiRel D.toPre F k p w s (Φ p w s) := fun s => ((h₁ p w hw).2 _ _).2 rfl
  have r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ p' w' s) := fun s => ((h₁ p' w' hw').2 _ _).2 rfl
  obtain ⟨σ, hσ⟩ := FamFree.exists_sec_ne_zero (D := D.toPre) (F := F) hL.2.1.secTwist hk 0
  obtain ⟨t, rfl, -⟩ := FamFree.exists_fam_single hG hB hk 0 σ
  obtain ⟨t, rfl⟩ := (h₁ p' w' hw').1.2 t
  obtain ⟨s, rfl⟩ := (h₁ p w hw).1.2 t
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' c (fun s s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ => by
    rw [((h₁ p w hw).2 _ _).1 a₂, ((h₁ p' w' hw').2 _ _).1 a₁, ((h₁ p' w' hw').2 _ _).1 a₄,
      ((h₁ p w hw).2 _ _).1 a₃, hc']) ⟨s, _, _, r s, r' _, fun h0 => hσ fun j => by rw [h0]; rfl⟩ hk (ζ : F)
  obtain ⟨θ, hp, hθ⟩ := exists_theta hG p hy w hw
  obtain ⟨θ', hp', hθ'⟩ := exists_theta hG p' hy' w' hw'
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_commIsOf hG D.toPre.P.isAb D.toPre.P.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c₀ :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c₀, Units.ext (by simp [unitOn])⟩
  have hz := GlobalLift.weilIs_of_commIsOf hG D.toPre.P.isAb D.toPre.P.isLB hc₀
  rw [hp, hp'] at hz
  have hcz : c = (z : F) := eq_of_sval _ hσ fun y J hJ => by
    have e := congrArg Units.val ((CommPairing.commIsOf_iff D.toPre.P.isLB θ θ' _).1 hc₀ _ (𝟙 _) y J hJ)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, ← gs_unit _ _ ⊤ trivial, hp, hp', translT_eq, translT_eq] at e
    have a₂ := hθ _ _ (r (Φ p' w' s)) (𝟙 _) y J hJ
    have a₁ := hθ' _ _ (r' s) (𝟙 _ ≫ DegPre.trPt D.toPre F p.g.b) y J hJ
    have a₄ := hθ' _ _ (r' (Φ p w s)) (𝟙 _) y J hJ
    have a₃ := hθ _ _ (r s) (𝟙 _ ≫ DegPre.trPt D.toPre F p'.g.b) y J hJ
    rw [a₁] at a₂
    rw [a₃] at a₄
    simp only [Category.id_comp, Over.id_left] at a₂ a₄ e
    rw [← hc', sval_smul _ _ _ _ y hJ, a₂, a₄, tr_comm, _root_.mul_assoc, _root_.mul_comm (Units.val _), e,
      Category.id_comp]
    show _ * (_ * _ * gs _ y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (z : F))) = _
    ring
  rw [key, hcz]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective
      (CommutatorPairing.weilIs_unique hG D.toPre.P.isAb D.toPre.P.isLB H hz))

end GlobalTheory.UT.WeilAbelianPart

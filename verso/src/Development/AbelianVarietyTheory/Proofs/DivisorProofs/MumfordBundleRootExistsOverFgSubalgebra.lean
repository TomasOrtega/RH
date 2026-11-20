import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section

open GlobalTheory

namespace GlobalTheory.RootFG

/- English proof (translation)
The claim follows from `LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h`.
-/
theorem lbIso_of_factor {Y Y' X₀ : Scheme.{0}} {M N : LB X₀} (a : Y ⟶ X₀) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀)
    (e : a' = j ≫ a) (h : LBIso (M.pull a) (N.pull a)) : LBIso (M.pull a') (N.pull a') :=
  LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h

/- English proof (translation)
Set `e : pullback pB (spMap (algebraMap k R₀)) ⟶ Y₀` to `hY₀.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition`. Establish `e₁ : e ≫ a₀ = pullback.fst _ _` using `hY₀.lift_fst _ _ _`. Establish `e₂ : e ≫ q₀ = pullback.snd _ _` using `hY₀.lift_snd _ _ _`. Set `f : pullback pB (spMap (algebraMap k C)) ⟶ Y` to `hY.lift (baseChangeMap pB R₀.val ≫ e) (pullback.snd _ _) (by`. Rewrite using `[Category.assoc, e₂, baseChangeMap_snd])`.

Establish `hf : f ≫ y = baseChangeMap pB R₀.val ≫ e` using `hY.lift_fst _ _ _`. Establish `H₀ : LBIso ((M.pull e).pull (baseChangeMap pB R₀.val)) ((N.pull e).pull (baseChangeMap pB R₀.val))`. Use `lbIso_of_factor y f _ hf.symm H` as an intermediate fact. Conclude with `LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _) (Spread.lbIso_pull_pull hM _ rfl).symm (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) this (Spread.lbIso_pull_pull hN _ rfl))`. Take `⟨R, hR, hRfg, H₁⟩` from `exists_fg_lbIso pB h₀ (M.pull e) (N.pull e) (pull_isLB hM _) (pull_isLB hN _) H₀`.

Use `⟨R, hR, hRfg, fun Y₁ q₁ y₁ w => ?_⟩` and prove the remaining obligations. Establish `H₂ : LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e)) (N.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e))` using `LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _) (Spread.lbIso_pull_pull hM _ rfl) (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) H₁ (Spread.lbIso_pull_pull hN _ rfl).symm)`. Establish `hs : spMap (Subalgebra.inclusion hR).toRingHom ≫ spMap (algebraMap k R₀) = spMap (algebraMap k R)`. Rewrite using `[spMap_comp_ring]`. Both sides reduce to the same expression.

Set `m : Y₁ ⟶ pullback pB (spMap (algebraMap k R))` to `pullback.lift (y₁ ≫ a₀) q₁ (by rw [Category.assoc, hY₀.w, ← Category.assoc, w, Category.assoc, hs])`. Use `lbIso_of_factor _ m y₁ ?_ H₂` and prove the remaining obligations. Apply `hY₀.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, e₁, baseChangeMap_fst, pullback.lift_fst]`. Rewrite using `[Category.assoc, Category.assoc, e₂, baseChangeMap_snd, pullback.lift_snd_assoc, w]`.
-/
theorem exists_fg_lbIso_of_isPullback {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C] {X : Scheme.{0}}
    (pB : X ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] {R₀ : Subalgebra k C} (h₀ : R₀.FG) {Y₀ Y : Scheme.{0}}
    (q₀ : Y₀ ⟶ Sp R₀) (a₀ : Y₀ ⟶ X) (hY₀ : IsPullback a₀ q₀ pB (spMap (algebraMap k R₀)))
    (y : Y ⟶ Y₀) (q : Y ⟶ Sp C) (hY : IsPullback y q q₀ (spMap R₀.val.toRingHom))
    (M N : LB Y₀) (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull y) (N.pull y)) :
    ∃ (R : Subalgebra k C) (hR : R₀ ≤ R), R.FG ∧ ∀ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp R) (y₁ : Y₁ ⟶ Y₀),
      y₁ ≫ q₀ = q₁ ≫ spMap (Subalgebra.inclusion hR).toRingHom → LBIso (M.pull y₁) (N.pull y₁) := by
  let e : pullback pB (spMap (algebraMap k R₀)) ⟶ Y₀ :=
    hY₀.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have e₁ : e ≫ a₀ = pullback.fst _ _ := hY₀.lift_fst _ _ _
  have e₂ : e ≫ q₀ = pullback.snd _ _ := hY₀.lift_snd _ _ _
  let f : pullback pB (spMap (algebraMap k C)) ⟶ Y :=
    hY.lift (baseChangeMap pB R₀.val ≫ e) (pullback.snd _ _) (by
      rw [Category.assoc, e₂, baseChangeMap_snd])
  have hf : f ≫ y = baseChangeMap pB R₀.val ≫ e := hY.lift_fst _ _ _
  have H₀ : LBIso ((M.pull e).pull (baseChangeMap pB R₀.val)) ((N.pull e).pull (baseChangeMap pB R₀.val)) := by
    have := lbIso_of_factor y f _ hf.symm H
    exact LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (Spread.lbIso_pull_pull hM _ rfl).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) this
        (Spread.lbIso_pull_pull hN _ rfl))
  obtain ⟨R, hR, hRfg, H₁⟩ := exists_fg_lbIso pB h₀ (M.pull e) (N.pull e) (pull_isLB hM _) (pull_isLB hN _) H₀
  refine ⟨R, hR, hRfg, fun Y₁ q₁ y₁ w => ?_⟩
  have H₂ : LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e))
      (N.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _)
      (Spread.lbIso_pull_pull hM _ rfl)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) H₁
        (Spread.lbIso_pull_pull hN _ rfl).symm)
  have hs : spMap (Subalgebra.inclusion hR).toRingHom ≫ spMap (algebraMap k R₀) = spMap (algebraMap k R) := by
    rw [spMap_comp_ring]; rfl
  let m : Y₁ ⟶ pullback pB (spMap (algebraMap k R)) :=
    pullback.lift (y₁ ≫ a₀) q₁ (by rw [Category.assoc, hY₀.w, ← Category.assoc, w, Category.assoc, hs])
  refine lbIso_of_factor _ m y₁ ?_ H₂
  apply hY₀.hom_ext
  · rw [Category.assoc, Category.assoc, e₁, baseChangeMap_fst, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, e₂, baseChangeMap_snd, pullback.lift_snd_assoc, w]

end GlobalTheory.RootFG

open GlobalTheory GlobalTheory.RootFG in

/- English proof (translation)
Introduce `S A _ hA P hP k _ t C _ _ hRt`. Take `⟨B', _, _, β, β₂, hβ, hsq, L, hL, H⟩` from `hRt`. Take `⟨A₀, _, φ₀, h₀⟩` from `GlobalTheory.FlagTan.exists_isGrpPullback A t`. Establish `hA₀ : IsAbelianScheme A₀` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₀`. Use `hA₀.proper` as an intermediate fact.

Establish `: IsProper (A₀ ⊗ A₀).hom`. Express the relevant statement in the definitionally equal form `IsProper (pullback.fst A₀.hom A₀.hom ≫ A₀.hom)`. Use `infer_instance`. Set `φ' : B'.left ⟶ A₀.left` to `h₀.1.lift β (B'.hom ≫ spMap (algebraMap k C)) (by rw [hβ.1.w, Category.assoc])`. Establish `hφ'₁ : φ' ≫ φ₀ = β` using `h₀.1.lift_fst _ _ _`.

Establish `hφ'₂ : φ' ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k C)` using `h₀.1.lift_snd _ _ _`. Establish `hB'₀ : IsGrpPullback B' A₀ (spMap (algebraMap k C)) φ'` using `IsGrpPullback.cancel h₀ (by rw [hφ'₁]; exact hβ) hφ'₂`. Take `⟨R₁, M, ρ, hR₁, hM, hρ₁, hρ₂, HL⟩` from `GlobalTheory.LBDescent.exists_fg_lb A₀.hom B'.hom φ' hB'₀.1 L hL`. Take `⟨B₁, _, β₁, h₁⟩` from `GlobalTheory.FlagTan.exists_isGrpPullback A₀ (spMap (algebraMap k R₁))`. Establish `hB₁ : IsAbelianScheme B₁` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ h₁`.

Use `haveI : IsCommMonObj B₁ := hB₁.comm`. Set `e₁ : B₁.left ⟶ pullback A₀.hom (spMap (algebraMap k R₁))` to `h₁.1.isoPullback.hom`. Set `L₁ : LB B₁.left` to `M.pull e₁`. Establish `hL₁ : L₁.IsLB` using `pull_isLB hM _`. Set `σ : Sp C ⟶ Sp R₁` to `spMap R₁.val.toRingHom`.

Establish `hσ : σ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k C)`. Rewrite using `[spMap_comp_ring]`. Both sides reduce to the same expression. Set `ψ : B'.left ⟶ B₁.left` to `h₁.1.lift φ' (B'.hom ≫ σ) (by rw [hφ'₂, Category.assoc, hσ])`. Establish `hψ₁ : ψ ≫ β₁ = φ'` using `h₁.1.lift_fst _ _ _`.

Establish `hψ₂ : ψ ≫ B₁.hom = B'.hom ≫ σ` using `h₁.1.lift_snd _ _ _`. Establish `hψ : IsGrpPullback B' B₁ σ ψ` using `IsGrpPullback.cancel h₁ (by rw [hψ₁, hσ]; exact hB'₀) hψ₂`. Establish `hρψ : ρ = ψ ≫ e₁`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[hρ₁, Category.assoc, IsPullback.isoPullback_hom_fst, hψ₁]`.

Rewrite using `[hρ₂, Category.assoc, IsPullback.isoPullback_hom_snd, hψ₂]`. Establish `HL₁ : LBIso L (L₁.pull ψ)` using `LBIso.trans hL (pull_isLB hM _) (pull_isLB hL₁ _) HL (Spread.lbIso_pull_pull hM ψ hρψ)`. Establish `hc : IsGrpPullback B₁ A (spMap (algebraMap k R₁) ≫ t) (β₁ ≫ φ₀)` using `h₁.comp h₀`. Set `β₂₁` to `(lift (pushPt hc.1.w (fst B₁ B₁)) (pushPt hc.1.w (snd B₁ B₁))).left`. Establish `hsq₁ : IsSquare (β₁ ≫ φ₀) β₂₁` using `GlobalTheory.LamPull.exists_isSquare hc.1.w`.

Set `V` to `lift (pushPt hψ.1.w (fst B' B')) (pushPt hψ.1.w (snd B' B'))`. Establish `hsqψ : IsSquare ψ V.left` using `GlobalTheory.LamPull.exists_isSquare hψ.1.w`. Apply the tactic sequence `have c₁ : LBIso (abelian₂ B' L) ((abelian₂ B₁ L₁).pull V.left) := GlobalTheory.SymSpread.lbIso_cube hψ hL₁ hL HL₁ (x2 B₁) (x2 B') V (fun i => by fin_cases i <;> simp [V, x2])`. Establish `hβ₂ : β₂ = V.left ≫ β₂₁`. Establish `h'` using `GlobalTheory.ZM.SiegPull.isSquare_comp hsqψ hsq₁`.

Establish `eβ : ψ ≫ β₁ ≫ φ₀ = β` using `by rw [← Category.assoc, hψ₁, hφ'₁]`. Rewrite `h'` using `[eβ]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `hsq.1.trans h'.1.symm`. Conclude with `hsq.2.trans h'.2.symm`.

Establish `hΛ₁ : (abelian₂ B₁ L₁).IsLB` using `LB.isLB_linComb hL₁ _ _`. Establish `hΛ' : (abelian₂ B' L).IsLB` using `LB.isLB_linComb hL _ _`. Establish `HV : LBIso ((abelian₂ B₁ L₁).pull V.left) ((P.pull β₂₁).pull V.left)` using `LBIso.trans (pull_isLB hΛ₁ _) hΛ' (pull_isLB (pull_isLB hP _) _) c₁.symm (LBIso.trans hΛ' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H (Spread.lbIso_pull_pull hP V.left hβ₂))`. Take `⟨R₂, h₁₂, hR₂, HD⟩` from `exists_fg_lbIso_of_isPullback (A₀ ⊗ A₀).hom hR₁ (B₁ ⊗ B₁).hom _ (GlobalTheory.SymSpread.isPullback_square h₁) V.left (B' ⊗ B').hom (GlobalTheory.SymSpread.isPullback_square hψ) (abelian₂ B₁ L₁) (P.pull β₂₁) hΛ₁ (pull_isLB hP _) HV`. Set `τ : Sp R₂ ⟶ Sp R₁` to `spMap (Subalgebra.inclusion h₁₂).toRingHom`.

Establish `hτ : τ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k R₂)`. Rewrite using `[spMap_comp_ring]`. Both sides reduce to the same expression. Take `⟨B₂, _, κ, hκ⟩` from `GlobalTheory.FlagTan.exists_isGrpPullback B₁ τ`. Establish `hB₂ : IsAbelianScheme B₂` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB₁ hκ`.

Use `haveI : IsCommMonObj B₂ := hB₂.comm`. Use `⟨R₂, hR₂, ?_⟩` and prove the remaining obligations. Rewrite using `[← hτ, Category.assoc]`. Set `W` to `lift (pushPt hκ.1.w (fst B₂ B₂)) (pushPt hκ.1.w (snd B₂ B₂))`. Establish `hsqW : IsSquare κ W.left` using `GlobalTheory.LamPull.exists_isSquare hκ.1.w`.

Establish `hL₂ : (L₁.pull κ).IsLB` using `pull_isLB hL₁ κ`. Use `⟨B₂, inferInstance, inferInstance, κ ≫ β₁ ≫ φ₀, W.left ≫ β₂₁, hκ.comp hc, GlobalTheory.ZM.SiegPull.isSquare_comp hsqW hsq₁, L₁.pull κ, hL₂, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have d₁ : LBIso (abelian₂ B₂ (L₁.pull κ)) ((abelian₂ B₁ L₁).pull W.left) := GlobalTheory.SymSpread.lbIso_cube hκ hL₁ hL₂ (lbIso_refl hL₂) (x2 B₁) (x2 B₂) W (fun i => by fin_cases i <;> simp [W, x2])`. Establish `d₂ : LBIso ((abelian₂ B₁ L₁).pull W.left) ((P.pull β₂₁).pull W.left)` using `HD _ (B₂ ⊗ B₂).hom W.left (GlobalTheory.SymSpread.isPullback_square hκ).w`. Conclude with `LBIso.trans (LB.isLB_linComb hL₂ _ _) (pull_isLB hΛ₁ _) (pull_isLB hP _) d₁ (LBIso.trans (pull_isLB hΛ₁ _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) d₂ (Spread.lbIso_pull_pull hP W.left rfl).symm)`.
-/
theorem GlobalTheory.RootFG.root_fg : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left),
    P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C],
    Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  intro S A _ hA P hP k _ t C _ _ hRt
  obtain ⟨B', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := hRt
  obtain ⟨A₀, _, φ₀, h₀⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₀
  have := hA₀.proper
  have : IsProper (A₀ ⊗ A₀).hom := by
    change IsProper (pullback.fst A₀.hom A₀.hom ≫ A₀.hom)
    infer_instance

  let φ' : B'.left ⟶ A₀.left := h₀.1.lift β (B'.hom ≫ spMap (algebraMap k C)) (by rw [hβ.1.w, Category.assoc])
  have hφ'₁ : φ' ≫ φ₀ = β := h₀.1.lift_fst _ _ _
  have hφ'₂ : φ' ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k C) := h₀.1.lift_snd _ _ _
  have hB'₀ : IsGrpPullback B' A₀ (spMap (algebraMap k C)) φ' :=
    IsGrpPullback.cancel h₀ (by rw [hφ'₁]; exact hβ) hφ'₂

  obtain ⟨R₁, M, ρ, hR₁, hM, hρ₁, hρ₂, HL⟩ := GlobalTheory.LBDescent.exists_fg_lb A₀.hom B'.hom φ' hB'₀.1 L hL
  obtain ⟨B₁, _, β₁, h₁⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A₀ (spMap (algebraMap k R₁))
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ h₁
  haveI : IsCommMonObj B₁ := hB₁.comm
  let e₁ : B₁.left ⟶ pullback A₀.hom (spMap (algebraMap k R₁)) := h₁.1.isoPullback.hom
  let L₁ : LB B₁.left := M.pull e₁
  have hL₁ : L₁.IsLB := pull_isLB hM _
  let σ : Sp C ⟶ Sp R₁ := spMap R₁.val.toRingHom
  have hσ : σ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k C) := by
    rw [spMap_comp_ring]; rfl
  let ψ : B'.left ⟶ B₁.left := h₁.1.lift φ' (B'.hom ≫ σ) (by rw [hφ'₂, Category.assoc, hσ])
  have hψ₁ : ψ ≫ β₁ = φ' := h₁.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ B₁.hom = B'.hom ≫ σ := h₁.1.lift_snd _ _ _
  have hψ : IsGrpPullback B' B₁ σ ψ := IsGrpPullback.cancel h₁ (by rw [hψ₁, hσ]; exact hB'₀) hψ₂
  have hρψ : ρ = ψ ≫ e₁ := by
    apply pullback.hom_ext
    · rw [hρ₁, Category.assoc, IsPullback.isoPullback_hom_fst, hψ₁]
    · rw [hρ₂, Category.assoc, IsPullback.isoPullback_hom_snd, hψ₂]
  have HL₁ : LBIso L (L₁.pull ψ) :=
    LBIso.trans hL (pull_isLB hM _) (pull_isLB hL₁ _) HL (Spread.lbIso_pull_pull hM ψ hρψ)

  have hc : IsGrpPullback B₁ A (spMap (algebraMap k R₁) ≫ t) (β₁ ≫ φ₀) := h₁.comp h₀
  let β₂₁ := (lift (pushPt hc.1.w (fst B₁ B₁)) (pushPt hc.1.w (snd B₁ B₁))).left
  have hsq₁ : IsSquare (β₁ ≫ φ₀) β₂₁ := GlobalTheory.LamPull.exists_isSquare hc.1.w
  let V := lift (pushPt hψ.1.w (fst B' B')) (pushPt hψ.1.w (snd B' B'))
  have hsqψ : IsSquare ψ V.left := GlobalTheory.LamPull.exists_isSquare hψ.1.w
  have c₁ : LBIso (abelian₂ B' L) ((abelian₂ B₁ L₁).pull V.left) :=
    GlobalTheory.SymSpread.lbIso_cube hψ hL₁ hL HL₁ (x2 B₁) (x2 B') V (fun i => by fin_cases i <;> simp [V, x2])
  have hβ₂ : β₂ = V.left ≫ β₂₁ := by
    have h' := GlobalTheory.ZM.SiegPull.isSquare_comp hsqψ hsq₁
    have eβ : ψ ≫ β₁ ≫ φ₀ = β := by rw [← Category.assoc, hψ₁, hφ'₁]
    rw [eβ] at h'
    apply pullback.hom_ext
    · exact hsq.1.trans h'.1.symm
    · exact hsq.2.trans h'.2.symm
  have hΛ₁ : (abelian₂ B₁ L₁).IsLB := LB.isLB_linComb hL₁ _ _
  have hΛ' : (abelian₂ B' L).IsLB := LB.isLB_linComb hL _ _
  have HV : LBIso ((abelian₂ B₁ L₁).pull V.left) ((P.pull β₂₁).pull V.left) :=
    LBIso.trans (pull_isLB hΛ₁ _) hΛ' (pull_isLB (pull_isLB hP _) _) c₁.symm
      (LBIso.trans hΛ' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H (Spread.lbIso_pull_pull hP V.left hβ₂))

  obtain ⟨R₂, h₁₂, hR₂, HD⟩ := exists_fg_lbIso_of_isPullback (A₀ ⊗ A₀).hom hR₁ (B₁ ⊗ B₁).hom _
    (GlobalTheory.SymSpread.isPullback_square h₁) V.left (B' ⊗ B').hom (GlobalTheory.SymSpread.isPullback_square hψ)
    (abelian₂ B₁ L₁) (P.pull β₂₁) hΛ₁ (pull_isLB hP _) HV
  let τ : Sp R₂ ⟶ Sp R₁ := spMap (Subalgebra.inclusion h₁₂).toRingHom
  have hτ : τ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k R₂) := by
    rw [spMap_comp_ring]; rfl
  obtain ⟨B₂, _, κ, hκ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback B₁ τ
  have hB₂ : IsAbelianScheme B₂ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB₁ hκ
  haveI : IsCommMonObj B₂ := hB₂.comm
  refine ⟨R₂, hR₂, ?_⟩
  rw [← hτ, Category.assoc]
  let W := lift (pushPt hκ.1.w (fst B₂ B₂)) (pushPt hκ.1.w (snd B₂ B₂))
  have hsqW : IsSquare κ W.left := GlobalTheory.LamPull.exists_isSquare hκ.1.w
  have hL₂ : (L₁.pull κ).IsLB := pull_isLB hL₁ κ
  refine ⟨B₂, inferInstance, inferInstance, κ ≫ β₁ ≫ φ₀, W.left ≫ β₂₁, hκ.comp hc,
    GlobalTheory.ZM.SiegPull.isSquare_comp hsqW hsq₁, L₁.pull κ, hL₂, ?_⟩
  have d₁ : LBIso (abelian₂ B₂ (L₁.pull κ)) ((abelian₂ B₁ L₁).pull W.left) :=
    GlobalTheory.SymSpread.lbIso_cube hκ hL₁ hL₂ (lbIso_refl hL₂) (x2 B₁) (x2 B₂) W (fun i => by fin_cases i <;> simp [W, x2])
  have d₂ : LBIso ((abelian₂ B₁ L₁).pull W.left) ((P.pull β₂₁).pull W.left) :=
    HD _ (B₂ ⊗ B₂).hom W.left (GlobalTheory.SymSpread.isPullback_square hκ).w
  exact LBIso.trans (LB.isLB_linComb hL₂ _ _) (pull_isLB hΛ₁ _) (pull_isLB hP _) d₁
    (LBIso.trans (pull_isLB hΛ₁ _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) d₂
      (Spread.lbIso_pull_pull hP W.left rfl).symm)

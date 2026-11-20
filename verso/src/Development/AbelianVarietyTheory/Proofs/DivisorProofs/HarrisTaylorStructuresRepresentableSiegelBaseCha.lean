import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushSecOfLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRelativelyRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectRigidityIdentificationsEqStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

open GlobalTheory.SiegelPull GlobalTheory.SiegelPullComp

/- English proof (translation)
Introduce `p _ D R _ b N h M e hN hNp hM hMo hMp hep Y s c hker hY`. Use `haveI := hY`. Take `⟨⟨c', hc'⟩, -⟩` from `GlobalTheory.siegPre_pullback h M (cycAway M) (zetaAway M) Y _ s (pullback.fst (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) ≫ s) (pullback.fst _ _) c rfl`. Establish `hker' : SiegKerBy c' e` using `siegKerBy_pull hc' hker`. Take `⟨Z, π, u, φu, φ₂u, hpb, hsq, hiso, hfin, hrep⟩` from `GlobalTheory.T.harrisTaylor_structures_relatively_representable p D R b N hN hNp h M (cycAway M) (zetaAway M) _ _ (pullback.snd _ _) c' e hep hker'`.

Set `lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A)` to `fun a => GlobalTheory.SiegelPull.secPull hpb (c'.lev a)`. Establish `hlev : ∀ a, (lev a).left ≫ φu = π ≫ (c'.lev a).left` using `fun a => GlobalTheory.SiegelPull.secPull_left hpb _`. Establish `hsl : IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev` using `isSympLev_pull hpb hsq c'.isLB u.isLB hiso hlev (GlobalTheory.UPel.HT.SiegPre.isSympLev c')`. Establish `hlevw : ∀ a, (lev a).left ≫ u.A.hom = 𝟙 Z` using `fun a => Over.w (lev a)`. Use `⟨Z, π, u, lev, hsl, hfin, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `T g t t₁ o l hl ⟨m, hm⟩`. Establish `h1 : SiegPB (o.toSieg hl) (u.toSieg hsl) g` using `⟨m.φ, m.φ₂, m.cart, m.sq, m.pol, hm⟩`. Establish `h2 : SiegPB (u.toSieg hsl) c' π` using `⟨φu, φ₂u, hpb, hsq, hiso, hlev⟩`. Conclude with `pb_comp (pb_comp hc' h2) h1`. Introduce `T t₀ t t₁ o l hl hS`.

Establish `hw : t₀ ≫ s ≫ spMap (Int.castRingHom (cycAway M)) = t ≫ spMap (Int.castRingHom R)` using `specZIsTerminal.hom_ext _ _`. Set `g₀ : T ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))` to `pullback.lift t₀ t hw`. Establish `hg₁ : g₀ ≫ pullback.fst _ _ = t₀` using `pullback.lift_fst _ _ _`. Establish `hg₂ : g₀ ≫ pullback.snd _ _ = t` using `pullback.lift_snd _ _ _`. Establish `hS' : SiegPB (o.toSieg hl) c' g₀` using `pb_cancel hc' (by rw [hg₁]; exact hS)`.

Take `⟨φ, φ₂, hφ, hsqφ, hisoφ, hlφ⟩` from `hS'`. Take `⟨z, ⟨hz, m, hm⟩, huniq⟩` from `hrep T g₀ t o φ φ₂ hg₂ hφ hsqφ hisoφ`. Establish `hlw : ∀ a, (l a).left ≫ o.A.hom = 𝟙 T` using `fun a => Over.w (l a)`. Use `⟨z, ⟨by rw [← Category.assoc, hz, hg₁], by rw [← Category.assoc, hz, hg₂], m, fun a => ?_⟩, ?_⟩` and prove the remaining obligations. Apply `hpb.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hm, Category.assoc, hlev, ← Category.assoc, hz]`. Conclude with `hlφ a`. Rewrite using `[Category.assoc, m.cart.1.w, ← Category.assoc, hlw, Category.assoc, hlevw]`. Simplify using the standard rewrite rules. Introduce and unpack `z' ⟨h1', h2', m', hm'⟩`.

Establish `hzπ : z' ≫ π = g₀` using `pullback.hom_ext (by rw [Category.assoc, h1', hg₁]) (by rw [Category.assoc, h2', hg₂])`. Use `huniq z' ⟨hzπ, m', ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.siegelObject_rigidity_identifications_eq h M hM _ T _ t₁ c' (o.toSieg hl) g₀ hker'.1 (m'.φ ≫ φu) φ (m'.φ₂ ≫ φ₂u) φ₂ (by rw [← hzπ]; exact m'.cart.comp hpb) ⟨?_, ?_⟩ ?_ (fun a => ?_) hφ hsqφ hisoφ hlφ` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.1).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φu) m'.sq.1).trans (Category.assoc _ _ _))))`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.2).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φu) m'.sq.2).trans (Category.assoc _ _ _))))`.

Conclude with `(m'.pol.trans o.isLB (pull_isLB u.isLB _) (pull_isLB (pull_isLB c'.isLB _) _) (iso_pull m'.φ₂ hiso)).trans o.isLB (pull_isLB (pull_isLB c'.isLB _) _) (pull_isLB c'.isLB _) (iso_pull_pull c'.isLB φ₂u m'.φ₂)`. Use `show (l a).left ≫ m'.φ ≫ φu = g₀ ≫ (c'.lev a).left`. Rewrite using `[← Category.assoc, hm' a, Category.assoc, hlev, ← Category.assoc, hzπ]`.
-/
theorem relRep_siegel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s), SiegKerBy c e → IsLocallyNoetherian (pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) → ∃ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) (u : Obj b N (π ≫ pullback.snd _ _)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A)), IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev ∧ IsFinite π ∧ (∀ (T : Scheme.{0}) (g : T ⟶ Z) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), (∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left) → SiegPB (o.toSieg hl) c (g ≫ π ≫ pullback.fst _ _)) ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ Y) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), SiegPB (o.toSieg hl) c t₀ → ∃! g : T ⟶ Z, g ≫ π ≫ pullback.fst _ _ = t₀ ∧ g ≫ π ≫ pullback.snd _ _ = t ∧ ∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left := by
  intro p _ D R _ b N h M e hN hNp hM hMo hMp hep Y s c hker hY
  haveI := hY
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback h M (cycAway M) (zetaAway M) Y _ s
    (pullback.fst (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) ≫ s) (pullback.fst _ _) c rfl
  have hker' : SiegKerBy c' e := siegKerBy_pull hc' hker
  obtain ⟨Z, π, u, φu, φ₂u, hpb, hsq, hiso, hfin, hrep⟩ :=
    GlobalTheory.T.harrisTaylor_structures_relatively_representable p D R b N hN hNp h M (cycAway M) (zetaAway M) _ _ (pullback.snd _ _) c' e hep hker'
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A) := fun a => GlobalTheory.SiegelPull.secPull hpb (c'.lev a)
  have hlev : ∀ a, (lev a).left ≫ φu = π ≫ (c'.lev a).left := fun a => GlobalTheory.SiegelPull.secPull_left hpb _
  have hsl : IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev :=
    isSympLev_pull hpb hsq c'.isLB u.isLB hiso hlev (GlobalTheory.UPel.HT.SiegPre.isSympLev c')
  have hlevw : ∀ a, (lev a).left ≫ u.A.hom = 𝟙 Z := fun a => Over.w (lev a)
  refine ⟨Z, π, u, lev, hsl, hfin, ?_, ?_⟩
  · rintro T g t t₁ o l hl ⟨m, hm⟩
    have h1 : SiegPB (o.toSieg hl) (u.toSieg hsl) g := ⟨m.φ, m.φ₂, m.cart, m.sq, m.pol, hm⟩
    have h2 : SiegPB (u.toSieg hsl) c' π := ⟨φu, φ₂u, hpb, hsq, hiso, hlev⟩
    exact pb_comp (pb_comp hc' h2) h1
  · intro T t₀ t t₁ o l hl hS
    have hw : t₀ ≫ s ≫ spMap (Int.castRingHom (cycAway M)) = t ≫ spMap (Int.castRingHom R) :=
      specZIsTerminal.hom_ext _ _
    let g₀ : T ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) :=
      pullback.lift t₀ t hw
    have hg₁ : g₀ ≫ pullback.fst _ _ = t₀ := pullback.lift_fst _ _ _
    have hg₂ : g₀ ≫ pullback.snd _ _ = t := pullback.lift_snd _ _ _
    have hS' : SiegPB (o.toSieg hl) c' g₀ := pb_cancel hc' (by rw [hg₁]; exact hS)
    obtain ⟨φ, φ₂, hφ, hsqφ, hisoφ, hlφ⟩ := hS'
    obtain ⟨z, ⟨hz, m, hm⟩, huniq⟩ := hrep T g₀ t o φ φ₂ hg₂ hφ hsqφ hisoφ
    have hlw : ∀ a, (l a).left ≫ o.A.hom = 𝟙 T := fun a => Over.w (l a)
    refine ⟨z, ⟨by rw [← Category.assoc, hz, hg₁], by rw [← Category.assoc, hz, hg₂], m, fun a => ?_⟩, ?_⟩
    · apply hpb.1.hom_ext
      · rw [Category.assoc, hm, Category.assoc, hlev, ← Category.assoc, hz]
        exact hlφ a
      · rw [Category.assoc, m.cart.1.w, ← Category.assoc, hlw, Category.assoc, hlevw]
        simp
    · rintro z' ⟨h1', h2', m', hm'⟩
      have hzπ : z' ≫ π = g₀ := pullback.hom_ext (by rw [Category.assoc, h1', hg₁])
        (by rw [Category.assoc, h2', hg₂])
      refine huniq z' ⟨hzπ, m', ?_⟩
      refine GlobalTheory.T.siegelObject_rigidity_identifications_eq h M hM _ T _ t₁ c' (o.toSieg hl) g₀ hker'.1 (m'.φ ≫ φu) φ (m'.φ₂ ≫ φ₂u) φ₂
        (by rw [← hzπ]; exact m'.cart.comp hpb) ⟨?_, ?_⟩ ?_ (fun a => ?_) hφ hsqφ hisoφ hlφ
      · exact (Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.1).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ φu) m'.sq.1).trans (Category.assoc _ _ _))))
      · exact (Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.2).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ φu) m'.sq.2).trans (Category.assoc _ _ _))))
      · exact (m'.pol.trans o.isLB (pull_isLB u.isLB _) (pull_isLB (pull_isLB c'.isLB _) _)
          (iso_pull m'.φ₂ hiso)).trans o.isLB (pull_isLB (pull_isLB c'.isLB _) _) (pull_isLB c'.isLB _)
          (iso_pull_pull c'.isLB φ₂u m'.φ₂)
      · show (l a).left ≫ m'.φ ≫ φu = g₀ ≫ (c'.lev a).left
        rw [← Category.assoc, hm' a, Category.assoc, hlev, ← Category.assoc, hzπ]

end GlobalTheory.UPel.HT

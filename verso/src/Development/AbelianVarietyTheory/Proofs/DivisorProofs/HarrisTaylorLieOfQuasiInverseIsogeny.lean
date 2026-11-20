import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteEtaleSurjectiveOfIsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotient

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

/- English proof (translation)
Introduce `p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq act' hact`. Take `⟨e, rfl⟩` from `hc`. Establish `hcY : IsUnit (((p ^ e : ℕ) : ℕ) : Γ(Y, ⊤))`. Use `(hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)` as an intermediate fact. Rewrite `this` using `[map_pow, map_natCast]`.

Rewrite using `[Nat.cast_pow]`. Conclude with `this`. Take `⟨-, hEt, -⟩` from `isFinite_etale_surjective_of_isQuasiInv Y o.A B (p ^ e) ψ ψ' o.ab hB hcY hq`. Use `haveI : IsMonHom ψ := hq.1`. Use `haveI : Etale ψ.left := hEt`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `R' _ β x hx v hv`. Take `⟨l, ⟨hl₁, hl₂⟩, -⟩` from `GlobalTheory.UPel.HT.EtaleLie.existsUnique_dual_lift ψ x v.left hv.1`. Set `u : epsPtR x ⟶ o.A` to `Over.homMk l (by show l ≫ o.A.hom = _`. Rewrite using `[← Over.w ψ, ← Category.assoc, hl₂]`.

Conclude with `Over.w v)`. Establish `hu : IsTanScal o.act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) u`. Use `⟨hl₁, ?_⟩` and prove the remaining obligations. Establish `hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ (spMap (epsScaleR (β b.ρ)) ≫ v.left) = (1 : Over.mk x ⟶ B).left`. Rewrite using `[← Category.assoc, GlobalTheory.UPel.HT.EtaleLie.fst_spMap_epsScaleR, hv.1]`.

Use `haveI := o.act.hom (algebraMap (𝓞 D.F) D.O D.ω)`. Use `(GlobalTheory.UPel.HT.EtaleLie.existsUnique_dual_lift ψ x _ hh).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩` and prove the remaining obligations. Use `show _ ≫ l ≫ (o.act.act _).left = _`. Rewrite using `[← Category.assoc, hl₁]`. Establish `e : ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O D.ω)).left = (1 : Over.mk x ⟶ o.A).left` using `congrArg Over.Hom.left (MonObj.one_comp _)`.

Conclude with `e`. Use `show (l ≫ (o.act.act _).left) ≫ ψ.left = _`. Rewrite using `[Category.assoc, ← Over.comp_left, hact, Over.comp_left, ← Category.assoc, hl₂, ← hv.2]`. Both sides reduce to the same expression. Use `show _ ≫ spMap _ ≫ l = _`.

Rewrite using `[← Category.assoc, GlobalTheory.UPel.HT.EtaleLie.fst_spMap_epsScaleR, hl₁]`. Use `show (spMap _ ≫ l) ≫ ψ.left = _`. Rewrite using `[Category.assoc, hl₂]`. Take `⟨w, hw, hvw⟩` from `o.lie R' β x hx u hu`. Use `⟨fun i => w i ≫ ψ, fun i a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show _ ≫ (w i).left ≫ ψ.left = _`. Rewrite using `[← Category.assoc, (hw i a).1]`. Establish `e : ((1 : Over.mk x ⟶ o.A) ≫ ψ).left = (1 : Over.mk x ⟶ B).left` using `congrArg Over.Hom.left (MonObj.one_comp ψ)`. Conclude with `e`. Use `show ((w i ≫ ψ) ≫ act'.act _).left = spMap _ ≫ (w i).left ≫ ψ.left`.

Rewrite using `[Category.assoc, ← hact, ← Category.assoc, Over.comp_left, (hw i a).2, Category.assoc]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← GlobalTheory.LieEtale.ofFn_prod_comp ψ w, ← hvw]`. Conclude with `hl₂.symm`. Introduce `κ _ _ x β hx i`.

Conclude with `(GlobalTheory.LieEtale.lieMult_iff_of_etale (𝓞 D.F) Y o.A B ψ (o.act.toF D) (act'.toF D) inferInstance hEt (fun a => hact _) κ x (β.comp (b.t i)) D.m).mp (o.lieRank κ x β hx i)`.
-/
theorem lie_of_isQuasiInv : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ B, IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ B), (∀ i, ∀ a : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O a) (β (b.t i a)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq act' hact
  obtain ⟨e, rfl⟩ := hc
  have hcY : IsUnit (((p ^ e : ℕ) : ℕ) : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_pow, map_natCast] at this
    rw [Nat.cast_pow]
    exact this
  obtain ⟨-, hEt, -⟩ := isFinite_etale_surjective_of_isQuasiInv Y o.A B (p ^ e) ψ ψ' o.ab hB hcY hq
  haveI : IsMonHom ψ := hq.1
  haveI : Etale ψ.left := hEt
  refine ⟨?_, ?_⟩
  · intro R' _ β x hx v hv
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := GlobalTheory.UPel.HT.EtaleLie.existsUnique_dual_lift ψ x v.left hv.1
    let u : epsPtR x ⟶ o.A := Over.homMk l (by
      show l ≫ o.A.hom = _
      rw [← Over.w ψ, ← Category.assoc, hl₂]; exact Over.w v)
    have hu : IsTanScal o.act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) u := by
      refine ⟨hl₁, ?_⟩
      have hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ (spMap (epsScaleR (β b.ρ)) ≫ v.left) =
          (1 : Over.mk x ⟶ B).left := by
        rw [← Category.assoc, GlobalTheory.UPel.HT.EtaleLie.fst_spMap_epsScaleR, hv.1]
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O D.ω)
      refine (GlobalTheory.UPel.HT.EtaleLie.existsUnique_dual_lift ψ x _ hh).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · show _ ≫ l ≫ (o.act.act _).left = _
        rw [← Category.assoc, hl₁]
        have e : ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O D.ω)).left =
            (1 : Over.mk x ⟶ o.A).left :=
          congrArg Over.Hom.left (MonObj.one_comp _)
        exact e
      · show (l ≫ (o.act.act _).left) ≫ ψ.left = _
        rw [Category.assoc, ← Over.comp_left, hact, Over.comp_left, ← Category.assoc, hl₂, ← hv.2]
        rfl
      · show _ ≫ spMap _ ≫ l = _
        rw [← Category.assoc, GlobalTheory.UPel.HT.EtaleLie.fst_spMap_epsScaleR, hl₁]
      · show (spMap _ ≫ l) ≫ ψ.left = _
        rw [Category.assoc, hl₂]
    obtain ⟨w, hw, hvw⟩ := o.lie R' β x hx u hu
    refine ⟨fun i => w i ≫ ψ, fun i a => ⟨?_, ?_⟩, ?_⟩
    · show _ ≫ (w i).left ≫ ψ.left = _
      rw [← Category.assoc, (hw i a).1]
      have e : ((1 : Over.mk x ⟶ o.A) ≫ ψ).left = (1 : Over.mk x ⟶ B).left :=
        congrArg Over.Hom.left (MonObj.one_comp ψ)
      exact e
    · show ((w i ≫ ψ) ≫ act'.act _).left = spMap _ ≫ (w i).left ≫ ψ.left
      rw [Category.assoc, ← hact, ← Category.assoc, Over.comp_left, (hw i a).2, Category.assoc]
    · apply Over.OverMorphism.ext
      rw [← GlobalTheory.LieEtale.ofFn_prod_comp ψ w, ← hvw]
      exact hl₂.symm
  · intro κ _ _ x β hx i
    exact (GlobalTheory.LieEtale.lieMult_iff_of_etale (𝓞 D.F) Y o.A B ψ (o.act.toF D) (act'.toF D) inferInstance hEt
      (fun a => hact _) κ x (β.comp (b.t i)) D.m).mp (o.lieRank κ x β hx i)

end GlobalTheory.UPel.HT.ES

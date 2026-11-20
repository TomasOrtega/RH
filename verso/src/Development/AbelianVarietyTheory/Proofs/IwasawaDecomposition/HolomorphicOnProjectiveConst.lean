import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtFJQOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CxPts

namespace GlobalTheory.ConstFn

variable {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ}

/- English proof (translation)
Establish `h : ⊤ ≤ y.1 ⁻¹ᵁ (⊤ : X.Opens)` using `le_rfl`. Use `show valR y.1 ⊤ a = _`. Rewrite using `[valR, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem ev_top_eq (a : Γ(X, ⊤)) (y : CxPts p σ) :
    ev p σ ⊤ a y = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (y.1.appTop.hom a) := by
  have h : ⊤ ≤ y.1 ⁻¹ᵁ (⊤ : X.Opens) := le_rfl
  show valR y.1 ⊤ a = _
  rw [valR, dif_pos h]
  rfl

/- English proof (translation)
Establish `hZ : IsIntegral (pullback p (spMap σ))` using `GeometricallyIntegral.geometrically_isIntegral (f := p) (spMap σ) _ _ (.of_hasPullback _ _)`. Set `fs` to `pullback.fst p (spMap σ)`. Set `sn` to `pullback.snd p (spMap σ)`. Set `e : ℂ →+* Γ(pullback p (spMap σ), ⊤)` to `sn.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom`. Use `letI : Algebra ℂ Γ(pullback p (spMap σ), ⊤) := e.toAlgebra`.

Establish `hcomp : (algebraMap ℂ Γ(pullback p (spMap σ), ⊤)).comp ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom) = fs.appTop.hom.comp p.appTop.hom`. Establish `h : fs ≫ p = sn ≫ spMap σ` using `pullback.condition`. Use extensionality with `c`. Establish `h'` using `congrArg (fun m : pullback p (spMap σ) ⟶ Sp F => m.appTop.hom c) h`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h'`.

Simplify using `only [RingHom.comp_apply]`. Use `Eq.trans ?_ h'.symm` and prove the remaining obligations. Use `show sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _`. Simplify using the standard rewrite rules. Establish `hint : IsIntegral ℂ (fs.appTop.hom a)`.

Take `⟨P, hP, h0⟩` from `isIntegral_appTop_of_universallyClosed p a`. Use `⟨P.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom), hP.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, h0, map_zero]`. Take `⟨r, hr⟩` from `(IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := integralClosure ℂ Γ(pullback p (spMap σ), ⊤))).2 ⟨_, hint⟩`. Establish `hr' : e r = fs.appTop.hom a` using `congrArg Subtype.val hr`.

Use `⟨r, fun y => ?_⟩` and prove the remaining obligations. Set `z : Sp ℂ ⟶ pullback p (spMap σ)` to `pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp])`. Establish `h1 : z ≫ fs = y.1` using `pullback.lift_fst _ _ _`. Establish `h2 : z ≫ sn = 𝟙 _` using `pullback.lift_snd _ _ _`. Establish `h3 : y.1.appTop.hom a = z.appTop.hom (fs.appTop.hom a)`.

Rewrite using `[← h1, Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression. Establish `h4 : z.appTop.hom (sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r`. Establish `e₂ : (z ≫ sn).appTop = sn.appTop ≫ z.appTop` using `Scheme.Hom.comp_appTop _ _`. Rewrite `e₂` using `[h2]`.

Establish `e₃` using `congrArg (fun m => m.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) e₂`. Conclude with `Eq.trans e₃.symm (by simp)`. Rewrite using `[ev_top_eq, h3, ← hr']`. Use `show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (z.appTop.hom (sn.appTop.hom _)) = r`. Rewrite using `[h4]`.

Simplify using the standard rewrite rules.
-/
theorem exists_ev_eq [UniversallyClosed p] [GeometricallyIntegral p] (a : Γ(X, ⊤)) :
    ∃ b : ℂ, ∀ y : CxPts p σ, ev p σ ⊤ a y = b := by
  have hZ : IsIntegral (pullback p (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := p) (spMap σ) _ _ (.of_hasPullback _ _)
  let fs := pullback.fst p (spMap σ)
  let sn := pullback.snd p (spMap σ)
  let e : ℂ →+* Γ(pullback p (spMap σ), ⊤) :=
    sn.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  letI : Algebra ℂ Γ(pullback p (spMap σ), ⊤) := e.toAlgebra
  have hcomp : (algebraMap ℂ Γ(pullback p (spMap σ), ⊤)).comp
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom) =
      fs.appTop.hom.comp p.appTop.hom := by
    have h : fs ≫ p = sn ≫ spMap σ := pullback.condition
    ext c
    have h' := congrArg (fun m : pullback p (spMap σ) ⟶ Sp F => m.appTop.hom c) h
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h'
    simp only [RingHom.comp_apply]
    refine Eq.trans ?_ h'.symm
    show sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _
    simp
  have hint : IsIntegral ℂ (fs.appTop.hom a) := by
    obtain ⟨P, hP, h0⟩ := isIntegral_appTop_of_universallyClosed p a
    refine ⟨P.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨r, hr⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)
    (K := integralClosure ℂ Γ(pullback p (spMap σ), ⊤))).2 ⟨_, hint⟩
  have hr' : e r = fs.appTop.hom a := congrArg Subtype.val hr
  refine ⟨r, fun y => ?_⟩
  let z : Sp ℂ ⟶ pullback p (spMap σ) :=
    pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp])
  have h1 : z ≫ fs = y.1 := pullback.lift_fst _ _ _
  have h2 : z ≫ sn = 𝟙 _ := pullback.lift_snd _ _ _
  have h3 : y.1.appTop.hom a = z.appTop.hom (fs.appTop.hom a) := by
    rw [← h1, Scheme.Hom.comp_appTop]; rfl
  have h4 : z.appTop.hom (sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r := by
    have e₂ : (z ≫ sn).appTop = sn.appTop ≫ z.appTop := Scheme.Hom.comp_appTop _ _
    rw [h2] at e₂
    have e₃ := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) e₂
    exact Eq.trans e₃.symm (by simp)
  rw [ev_top_eq, h3, ← hr']
  show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (z.appTop.hom (sn.appTop.hom _)) = r
  rw [h4]
  simp

end GlobalTheory.ConstFn

/- English proof (translation)
Introduce `F _ Y σ R q hq`. Establish `hB` using `LB.isLB_triv Y.X`. Establish `hs : (fun _ => q : (LB.triv Y.X).ι → CxPts Y.str σ → ℂ) ∈ R.holSec (LB.triv Y.X)`. Use `⟨⟨fun i j y hi _ => ?_, fun i y h => (h mem_ptsIn_top).elim⟩, fun i => hq.mono (Set.subset_univ _)⟩` and prove the remaining obligations. Consider the cases of `i`.

Consider the cases of `j`. Rewrite using `[gv_self hB hi, one_mul]`. Take `⟨x, hx⟩` from `(AnRead.bijective_valC Y.isProjOver R hB).2 ⟨_, hs⟩`. Set `M : Submodule ℂ ((LB.triv Y.X).ι → CxPts Y.str σ → ℂ)` to `{ carrier := {s | ∃ b : ℂ, ∀ i z, s i z = b} zero_mem' := ⟨0, fun _ _ => rfl⟩ add_mem' := fun {s t} ⟨b, hb⟩ ⟨c, hc⟩ => ⟨b + c, fun i z => by simp [hb, hc]⟩ smul_mem' := fun c s ⟨b, hb⟩ => ⟨c * b, fun i z => by simp [hb]⟩ }`. Take `⟨b, hb⟩ : SecC.val x ∈ M` from `SecC.val_mem_of (fun s => by`.

Take `⟨b, hb⟩` from `GlobalTheory.ConstFn.exists_ev_eq (p := Y.str) (σ := σ) (s.f PUnit.unit)`. Conclude with `⟨b, fun i z => by cases i; exact hb z⟩) x`. Use `⟨b, fun z => ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg Subtype.val hx`. Rewrite `e` using `[AnRead.coe_valC]`.

Use `hb PUnit.unit z` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem GlobalTheory.ConstFn.holoOn_univ_const : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim)
    (q : CxPts Y.str σ → ℂ), R.HoloOn Set.univ q → ∃ b : ℂ, ∀ z, q z = b := by
  intro F _ Y σ R q hq
  have hB := LB.isLB_triv Y.X
  have hs : (fun _ => q : (LB.triv Y.X).ι → CxPts Y.str σ → ℂ) ∈ R.holSec (LB.triv Y.X) := by
    refine ⟨⟨fun i j y hi _ => ?_, fun i y h => (h mem_ptsIn_top).elim⟩, fun i => hq.mono (Set.subset_univ _)⟩
    cases i; cases j
    rw [gv_self hB hi, one_mul]
  obtain ⟨x, hx⟩ := (AnRead.bijective_valC Y.isProjOver R hB).2 ⟨_, hs⟩
  let M : Submodule ℂ ((LB.triv Y.X).ι → CxPts Y.str σ → ℂ) :=
    { carrier := {s | ∃ b : ℂ, ∀ i z, s i z = b}
      zero_mem' := ⟨0, fun _ _ => rfl⟩
      add_mem' := fun {s t} ⟨b, hb⟩ ⟨c, hc⟩ => ⟨b + c, fun i z => by simp [hb, hc]⟩
      smul_mem' := fun c s ⟨b, hb⟩ => ⟨c * b, fun i z => by simp [hb]⟩ }
  obtain ⟨b, hb⟩ : SecC.val x ∈ M := SecC.val_mem_of (fun s => by
    obtain ⟨b, hb⟩ := GlobalTheory.ConstFn.exists_ev_eq (p := Y.str) (σ := σ) (s.f PUnit.unit)
    exact ⟨b, fun i z => by cases i; exact hb z⟩) x
  refine ⟨b, fun z => ?_⟩
  have e := congrArg Subtype.val hx
  rw [AnRead.coe_valC] at e
  have := hb PUnit.unit z
  rw [e] at this
  exact this

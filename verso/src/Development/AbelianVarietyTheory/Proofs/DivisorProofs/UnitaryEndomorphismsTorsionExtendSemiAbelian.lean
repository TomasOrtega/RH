import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSemiAbelianEndoTorsionExtend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupOfPointEqAlongModelHom
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GFib

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo cf C X wi Y U₀ EE FinalForm q hO _ hq z hTH`. Establish `hU : (U₀ : Set Y.Z).Nonempty` using `hO.ne`. Establish `hr : Set.range Y.pt ⊆ Set.range U₀.ι`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `Y.top_le_preimage_pt hU (x := w) trivial`. Set `x : Sp X.Ω₁ ⟶ U₀.toScheme` to `IsOpenImmersion.lift U₀.ι Y.pt hr`. Establish `hx : x ≫ U₀.ι = Y.pt` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hxu : x ≫ FinalForm.u₀ = spMap X.S.R.val.toRingHom` using `FinalForm.u₀_gen x hx`. Establish `hwx : wi.α ≫ X.ρ.P.A.hom = (wi.G.hom ≫ x) ≫ FinalForm.u₀`.

Rewrite using `[Category.assoc, hxu]`. Conclude with `wi.hα.1.w`. Set `ν : wi.G.left ⟶ pullback X.ρ.P.A.hom FinalForm.u₀` to `pullback.lift wi.α (wi.G.hom ≫ x) hwx`. Establish `hν₁ : ν ≫ pullback.fst _ _ = wi.α` using `pullback.lift_fst _ _ _`. Establish `hν₂ : ν ≫ pullback.snd _ _ = wi.G.hom ≫ x` using `pullback.lift_snd _ _ _`.

Set `ψ : wi.G.left ⟶ FinalForm.G.left` to `ν ≫ FinalForm.φ`. Establish `hQ` using `isGrpPullback_pullback X.ρ.P.A FinalForm.u₀`. Establish `gα : IsGrpPullback wi.G X.ρ.P.A (x ≫ FinalForm.u₀) (ν ≫ pullback.fst X.ρ.P.A.hom FinalForm.u₀)` using `wi.hα.congr hxu.symm hν₁.symm`. Establish `gν : IsGrpPullback wi.G ((Over.pullback FinalForm.u₀).obj X.ρ.P.A) x ν` using `hQ.cancel gα hν₂`. Establish `gW : IsGrpPullback wi.G FinalForm.G Y.pt ψ` using `(gν.comp FinalForm.cart).congr hx rfl`.

Establish `hxu' : ∀ (x₀ : Sp X.Ω₁ ⟶ U₀.toScheme), x₀ ≫ U₀.ι = Y.pt → x₀ = x` using `fun x₀ h₀ => (cancel_mono U₀.ι).1 (h₀.trans hx.symm)`. Set `P` to `(Over.pullback Y.pt).obj FinalForm.G`. Establish `gA` using `isGrpPullback_pullback FinalForm.G Y.pt`. Set `k : P.left ⟶ wi.G.left` to `gW.1.lift (pullback.fst FinalForm.G.hom Y.pt) P.hom pullback.condition`. Establish `hk₁ : k ≫ ψ = pullback.fst FinalForm.G.hom Y.pt` using `gW.1.lift_fst _ _ _`.

Establish `hk₂ : k ≫ wi.G.hom = P.hom` using `gW.1.lift_snd _ _ _`. Establish `gk : IsGrpPullback P wi.G (𝟙 _) k` using `gW.cancel (gA.congr (Category.id_comp _).symm hk₁.symm) (by rw [hk₂, Category.comp_id])`. Use `haveI : IsIso k := gk.1.isIso_fst_of_isIso`. Establish `hE : ∀ a : 𝓞 E, ∃ F : FinalForm.G ⟶ FinalForm.G, IsMonHom F ∧ ∀ e₁ : wi.G ⟶ wi.G, e₁.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e₁.left ≫ ψ = ψ ≫ F.left`. Introduce `a`.

Take `⟨e₀, he₀, pa⟩` from `GlobalTheory.SymBaseChange.exists_endo wi.hβ (Xo.univ.t.act.act a)`. Establish `he₀l : e₀.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left`. Use `congrArg (fun z => z.left) (pa (𝟙 _))` as an intermediate fact. Simplify `this` using `[pushPt]`. Use `haveI := he₀`.

Take `⟨w', hw', pw⟩` from `GlobalTheory.SymBaseChange.exists_endo gk e₀`. Establish `hw'l : w'.left ≫ k = k ≫ e₀.left`. Use `congrArg (fun z => z.left) (pw (𝟙 _))` as an intermediate fact. Simplify `this` using `[pushPt]`. Take `⟨F, ⟨hF, hFw⟩, -⟩` from `FinalForm.endo w' hw'`.

Establish `hF' : w'.left ≫ pullback.fst FinalForm.G.hom Y.pt = pullback.fst FinalForm.G.hom Y.pt ≫ F.left`. Rewrite using `[← hFw]`. Simplify using `only [Over.pullback_map_left]`. Conclude with `pullback.lift_fst _ _ _`. Use `⟨F, hF, fun e₁ he₁ => ?_⟩` and prove the remaining obligations.

Establish `h10 : e₁ = e₀` using `GlobalTheory.TorusPart.hom_ext_of_pullback wi.hβ (he₁.trans he₀l.symm)`. Substitute `h10` using the available equality. Establish `e1 : k ≫ e₁.left ≫ ψ = w'.left ≫ k ≫ ψ` using `by rw [← Category.assoc, ← hw'l, Category.assoc]`. Rewrite using `[← cancel_epi k, e1, hk₁, hF', ← hk₁, Category.assoc]`. Use `choose f hf using hE`.

Establish `hT : ∀ t : X.S.TT X.M z, ∃ g : Over.mk Y.pt ⟶ FinalForm.G, g ^ (X.S.r * X.S.N) = 1 ∧ (∀ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.G.hom = 𝟙 _ → w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt (t : X.S.Gam)).left → w ≫ ψ = g.left) ∧ ∀ w, q.base w = z → ExtNear g w`. Introduce `t`. Use `set b : X.S.Gam := (t : X.S.Gam) with hbdef`. Establish `hb : (spMap X.S.R.val.toRingHom ≫ (X.ρ.pt b).left) ≫ X.ρ.P.A.hom = 𝟙 _ ≫ spMap X.S.R.val.toRingHom`. Rewrite using `[Category.assoc, Over.w (X.ρ.pt b)]`.

Simplify using the standard rewrite rules. Set `w₀` to `wi.hα.1.lift _ _ hb`. Establish `hw₁ : w₀ ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt b).left` using `wi.hα.1.lift_fst _ _ _`. Establish `hw₂ : w₀ ≫ wi.G.hom = 𝟙 _` using `wi.hα.1.lift_snd _ _ _`. Set `sec0 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G` to `Over.homMk w₀ hw₂`.

Set `V : Over.mk Y.pt ⟶ Over.mk (𝟙 (Sp X.Ω₁) ≫ Y.pt)` to `Over.homMk (𝟙 _) (by simp)`. Set `gγ : Over.mk Y.pt ⟶ FinalForm.G` to `V ≫ pushPt gW.1.w sec0`. Establish `hgl : gγ.left = w₀ ≫ ψ` using `by simp [gγ, V, pushPt, sec0]`. Use `⟨gγ, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : X.ρ.pt 0 = 1`.

Use `X.ρ.pt_add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`. Establish `hpt : ∀ n : ℕ, (X.ρ.pt b) ^ n = X.ρ.pt (n • b)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp [h0]`. Consider the case `succ k ih => rw [pow_succ, ih, ← X.ρ.pt_add, succ_nsmul]`. Establish `hrN : (X.S.r * X.S.N) • b = 0`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Set `U : Over.mk (𝟙 (Sp X.Ω₁) ≫ spMap X.S.R.val.toRingHom) ⟶ baseOver (Sp X.S.R)` to `Over.homMk (spMap X.S.R.val.toRingHom) (by simp)`. Establish `hs : pushPt wi.hα.1.w sec0 = U ≫ X.ρ.pt b`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `[pushPt, sec0, U, hw₁]`.

Establish `hsec : sec0 ^ (X.S.r * X.S.N) = 1`. Apply `GlobalTheory.SymBaseChange.pushPt_injective wi.hα` to reduce the goal to its premises. Establish `e1 : pushPt wi.hα.1.w (sec0 ^ (X.S.r * X.S.N)) = (pushPt wi.hα.1.w sec0) ^ (X.S.r * X.S.N)` using `map_pow (pushHom wi.hα _) sec0 _`. Establish `e2 : pushPt wi.hα.1.w (1 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G) = 1` using `map_one (pushHom wi.hα _)`. Establish `e3 : (U ≫ X.ρ.pt b) ^ (X.S.r * X.S.N) = U ≫ (X.ρ.pt b) ^ (X.S.r * X.S.N)` using `(map_pow (preHom U) (X.ρ.pt b) _).symm`.

Establish `e4 : U ≫ (1 : baseOver (Sp X.S.R) ⟶ X.ρ.P.A) = 1` using `map_one (preHom U)`. Rewrite using `[e1, e2, hs, e3, hpt, hrN, h0, e4]`. Establish `f1 : gγ ^ (X.S.r * X.S.N) = V ≫ (pushPt gW.1.w sec0) ^ (X.S.r * X.S.N)` using `map_pow (preHom V) _ _`. Establish `f2 : (pushPt gW.1.w sec0) ^ (X.S.r * X.S.N) = pushPt gW.1.w (sec0 ^ (X.S.r * X.S.N))` using `(map_pow (pushHom gW _) sec0 _).symm`. Establish `f3 : pushPt gW.1.w (1 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G) = 1` using `map_one (pushHom gW _)`.

Establish `f4 : V ≫ (1 : Over.mk (𝟙 (Sp X.Ω₁) ≫ Y.pt) ⟶ FinalForm.G) = 1` using `map_one (preHom V)`. Rewrite using `[f1, f2, hsec, f3, f4]`. Introduce `w h1 h2`. Establish `: w = w₀` using `wi.hα.1.hom_ext (by rw [h2, hw₁]) (by rw [hw₂]; exact h1)`. Rewrite using `[this, hgl]`.

Introduce `w hw`. Establish `hb' : b ∈ X.S.HH Y w`. Rewrite using `[GlobalTheory.Poinc.HHFibre.HH_eq_of_hom X.o₁ X.Ω₁ X.S X.M Y q hq X.hasDiv w]`. Establish `e : q w = z` using `hw`. Rewrite using `[e]`.

Conclude with `hTH t.2`. Take `⟨W, h, hzW, hh, hx'⟩` from `FinalForm.sec w b hb'`. Use `⟨W, h, hzW, hh, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hgl, hx' y (w₀ ≫ ν) hy ?_ ?_]`. Simplify using `only [ψ, Category.assoc]`.

Use `gW.1.w` as an intermediate fact. Simplify using `only [ψ] at this`. Rewrite using `[Category.assoc, ← Category.assoc ν, this, ← Category.assoc, hw₂, Category.id_comp]`. Rewrite using `[Category.assoc, hν₁, hw₁]`. Use `choose gγ hg using hT`.

Use `⟨f, gγ, fun a => ⟨(hf a).1, ?_⟩, fun t => ⟨(hg t).1, ?_, (hg t).2.2⟩⟩` and prove the remaining obligations. Introduce `x₀ h₀ hw e₀ he`. Establish `h'` using `hxu' x₀ h₀`. Substitute `h'` using the available equality. Conclude with `(hf a).2 e₀ he`.

Introduce `x₀ h₀ hw w h1 h2`. Establish `h'` using `hxu' x₀ h₀`. Substitute `h'` using the available equality. Conclude with `(hg t).2.1 w h1 h2`.
-/
theorem endo_torsion_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (FinalForm : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → Y.pt ≫ q = X.M.pt → ∀ z : X.M.Z, X.S.TT X.M z ≤ X.S.HH X.M z → ∃ (f : 𝓞 E → (FinalForm.G ⟶ FinalForm.G)) (gγ : X.S.TT X.M z → (Over.mk Y.pt ⟶ FinalForm.G)), GlobalTheory.UPoinc.GFib.IsEndoExt X wi FinalForm f ∧ GlobalTheory.UPoinc.GFib.IsTorsExt X wi FinalForm q z gγ := by
  intro E _ _ _ H Dw l Xo cf C X wi Y U₀ EE FinalForm q hO _ hq z hTH
  have hU : (U₀ : Set Y.Z).Nonempty := hO.ne
  have hr : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Y.top_le_preimage_pt hU (x := w) trivial
  let x : Sp X.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hr
  have hx : x ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x ≫ FinalForm.u₀ = spMap X.S.R.val.toRingHom := FinalForm.u₀_gen x hx
  have hwx : wi.α ≫ X.ρ.P.A.hom = (wi.G.hom ≫ x) ≫ FinalForm.u₀ := by
    rw [Category.assoc, hxu]; exact wi.hα.1.w
  let ν : wi.G.left ⟶ pullback X.ρ.P.A.hom FinalForm.u₀ := pullback.lift wi.α (wi.G.hom ≫ x) hwx
  have hν₁ : ν ≫ pullback.fst _ _ = wi.α := pullback.lift_fst _ _ _
  have hν₂ : ν ≫ pullback.snd _ _ = wi.G.hom ≫ x := pullback.lift_snd _ _ _
  let ψ : wi.G.left ⟶ FinalForm.G.left := ν ≫ FinalForm.φ
  have hQ := isGrpPullback_pullback X.ρ.P.A FinalForm.u₀
  have gα : IsGrpPullback wi.G X.ρ.P.A (x ≫ FinalForm.u₀) (ν ≫ pullback.fst X.ρ.P.A.hom FinalForm.u₀) :=
    wi.hα.congr hxu.symm hν₁.symm
  have gν : IsGrpPullback wi.G ((Over.pullback FinalForm.u₀).obj X.ρ.P.A) x ν := hQ.cancel gα hν₂
  have gW : IsGrpPullback wi.G FinalForm.G Y.pt ψ := (gν.comp FinalForm.cart).congr hx rfl

  have hxu' : ∀ (x₀ : Sp X.Ω₁ ⟶ U₀.toScheme), x₀ ≫ U₀.ι = Y.pt → x₀ = x := fun x₀ h₀ =>
    (cancel_mono U₀.ι).1 (h₀.trans hx.symm)

  let P := (Over.pullback Y.pt).obj FinalForm.G
  have gA := isGrpPullback_pullback FinalForm.G Y.pt
  let k : P.left ⟶ wi.G.left := gW.1.lift (pullback.fst FinalForm.G.hom Y.pt) P.hom pullback.condition
  have hk₁ : k ≫ ψ = pullback.fst FinalForm.G.hom Y.pt := gW.1.lift_fst _ _ _
  have hk₂ : k ≫ wi.G.hom = P.hom := gW.1.lift_snd _ _ _
  have gk : IsGrpPullback P wi.G (𝟙 _) k :=
    gW.cancel (gA.congr (Category.id_comp _).symm hk₁.symm) (by rw [hk₂, Category.comp_id])
  haveI : IsIso k := gk.1.isIso_fst_of_isIso

  have hE : ∀ a : 𝓞 E, ∃ F : FinalForm.G ⟶ FinalForm.G, IsMonHom F ∧ ∀ e₁ : wi.G ⟶ wi.G,
      e₁.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e₁.left ≫ ψ = ψ ≫ F.left := by
    intro a
    obtain ⟨e₀, he₀, pa⟩ := GlobalTheory.SymBaseChange.exists_endo wi.hβ (Xo.univ.t.act.act a)
    have he₀l : e₀.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left := by
      have := congrArg (fun z => z.left) (pa (𝟙 _))
      simpa [pushPt] using this
    haveI := he₀
    obtain ⟨w', hw', pw⟩ := GlobalTheory.SymBaseChange.exists_endo gk e₀
    have hw'l : w'.left ≫ k = k ≫ e₀.left := by
      have := congrArg (fun z => z.left) (pw (𝟙 _))
      simpa [pushPt] using this
    obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
    have hF' : w'.left ≫ pullback.fst FinalForm.G.hom Y.pt = pullback.fst FinalForm.G.hom Y.pt ≫ F.left := by
      rw [← hFw]
      simp only [Over.pullback_map_left]
      exact pullback.lift_fst _ _ _
    refine ⟨F, hF, fun e₁ he₁ => ?_⟩
    have h10 : e₁ = e₀ := GlobalTheory.TorusPart.hom_ext_of_pullback wi.hβ (he₁.trans he₀l.symm)
    subst h10
    have e1 : k ≫ e₁.left ≫ ψ = w'.left ≫ k ≫ ψ := by rw [← Category.assoc, ← hw'l, Category.assoc]
    rw [← cancel_epi k, e1, hk₁, hF', ← hk₁, Category.assoc]
  choose f hf using hE
  have hT : ∀ t : X.S.TT X.M z, ∃ g : Over.mk Y.pt ⟶ FinalForm.G, g ^ (X.S.r * X.S.N) = 1 ∧
      (∀ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.G.hom = 𝟙 _ →
        w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt (t : X.S.Gam)).left → w ≫ ψ = g.left) ∧
      ∀ w, q.base w = z → ExtNear g w := by
    intro t
    set b : X.S.Gam := (t : X.S.Gam) with hbdef
    have hb : (spMap X.S.R.val.toRingHom ≫ (X.ρ.pt b).left) ≫ X.ρ.P.A.hom = 𝟙 _ ≫ spMap X.S.R.val.toRingHom := by
      rw [Category.assoc, Over.w (X.ρ.pt b)]; simp
    let w₀ := wi.hα.1.lift _ _ hb
    have hw₁ : w₀ ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt b).left := wi.hα.1.lift_fst _ _ _
    have hw₂ : w₀ ≫ wi.G.hom = 𝟙 _ := wi.hα.1.lift_snd _ _ _
    let sec0 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G := Over.homMk w₀ hw₂
    let V : Over.mk Y.pt ⟶ Over.mk (𝟙 (Sp X.Ω₁) ≫ Y.pt) := Over.homMk (𝟙 _) (by simp)
    let gγ : Over.mk Y.pt ⟶ FinalForm.G := V ≫ pushPt gW.1.w sec0
    have hgl : gγ.left = w₀ ≫ ψ := by simp [gγ, V, pushPt, sec0]
    refine ⟨gγ, ?_, ?_, ?_⟩
    · have h0 : X.ρ.pt 0 = 1 := by
        have := X.ρ.pt_add 0 0
        rw [add_zero] at this
        exact mul_eq_left.1 this.symm
      have hpt : ∀ n : ℕ, (X.ρ.pt b) ^ n = X.ρ.pt (n • b) := by
        intro n
        induction n with
        | zero => simp [h0]
        | succ k ih => rw [pow_succ, ih, ← X.ρ.pt_add, succ_nsmul]
      have hrN : (X.S.r * X.S.N) • b = 0 := by
        funext i
        simp
      let U : Over.mk (𝟙 (Sp X.Ω₁) ≫ spMap X.S.R.val.toRingHom) ⟶ baseOver (Sp X.S.R) :=
        Over.homMk (spMap X.S.R.val.toRingHom) (by simp)
      have hs : pushPt wi.hα.1.w sec0 = U ≫ X.ρ.pt b := by
        apply Over.OverMorphism.ext
        simp [pushPt, sec0, U, hw₁]
      have hsec : sec0 ^ (X.S.r * X.S.N) = 1 := by
        apply GlobalTheory.SymBaseChange.pushPt_injective wi.hα
        have e1 : pushPt wi.hα.1.w (sec0 ^ (X.S.r * X.S.N)) = (pushPt wi.hα.1.w sec0) ^ (X.S.r * X.S.N) :=
          map_pow (pushHom wi.hα _) sec0 _
        have e2 : pushPt wi.hα.1.w (1 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G) = 1 :=
          map_one (pushHom wi.hα _)
        have e3 : (U ≫ X.ρ.pt b) ^ (X.S.r * X.S.N) = U ≫ (X.ρ.pt b) ^ (X.S.r * X.S.N) :=
          (map_pow (preHom U) (X.ρ.pt b) _).symm
        have e4 : U ≫ (1 : baseOver (Sp X.S.R) ⟶ X.ρ.P.A) = 1 := map_one (preHom U)
        rw [e1, e2, hs, e3, hpt, hrN, h0, e4]
      have f1 : gγ ^ (X.S.r * X.S.N) = V ≫ (pushPt gW.1.w sec0) ^ (X.S.r * X.S.N) :=
        map_pow (preHom V) _ _
      have f2 : (pushPt gW.1.w sec0) ^ (X.S.r * X.S.N) = pushPt gW.1.w (sec0 ^ (X.S.r * X.S.N)) :=
        (map_pow (pushHom gW _) sec0 _).symm
      have f3 : pushPt gW.1.w (1 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G) = 1 :=
        map_one (pushHom gW _)
      have f4 : V ≫ (1 : Over.mk (𝟙 (Sp X.Ω₁) ≫ Y.pt) ⟶ FinalForm.G) = 1 := map_one (preHom V)
      rw [f1, f2, hsec, f3, f4]
    · intro w h1 h2
      have : w = w₀ := wi.hα.1.hom_ext (by rw [h2, hw₁]) (by rw [hw₂]; exact h1)
      rw [this, hgl]
    · intro w hw
      have hb' : b ∈ X.S.HH Y w := by
        rw [GlobalTheory.Poinc.HHFibre.HH_eq_of_hom X.o₁ X.Ω₁ X.S X.M Y q hq X.hasDiv w]
        have e : q w = z := hw
        rw [e]
        exact hTH t.2
      obtain ⟨W, h, hzW, hh, hx'⟩ := FinalForm.sec w b hb'
      refine ⟨W, h, hzW, hh, fun y hy => ?_⟩
      rw [hgl, hx' y (w₀ ≫ ν) hy ?_ ?_]
      · simp only [ψ, Category.assoc]
      · have := gW.1.w
        simp only [ψ] at this
        rw [Category.assoc, ← Category.assoc ν, this, ← Category.assoc, hw₂, Category.id_comp]
      · rw [Category.assoc, hν₁, hw₁]
  choose gγ hg using hT
  refine ⟨f, gγ, fun a => ⟨(hf a).1, ?_⟩, fun t => ⟨(hg t).1, ?_, (hg t).2.2⟩⟩
  · intro x₀ h₀ hw e₀ he
    have h' := hxu' x₀ h₀
    subst h'
    exact (hf a).2 e₀ he
  · intro x₀ h₀ hw w h1 h2
    have h' := hxu' x₀ h₀
    subst h'
    exact (hg t).2.1 w h1 h2

end GlobalTheory.UPoinc.GFib

import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuUnitsPf
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.H2CurveOrder.LeafKumMuInjPf

def ShfSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (y : Sec F U),
  (Loc U fun V g => Sec.res g y = 0) → y = 0

/- English proof (translation)
Introduce `R _ F U y h`. Take `⟨S, hS, hP⟩` from `h`. Set `e₁ : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U)` to `ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)`. Use `Presheaf.IsSheaf.hom_ext F.property ⟨S, hS⟩ e₁ 0 (fun I => by` as an intermediate fact. Use `ext`.

Simplify using `[e₁]`. Conclude with `hP _ _ I.hf)`. Establish `h1` using `congrArg (fun f => f.hom 1) this`. Simplify `h1` using `[e₁]`.
-/
theorem shfSep : ShfSep := by
  intro R _ F U y h
  obtain ⟨S, hS, hP⟩ := h
  let e₁ : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have := Presheaf.IsSheaf.hom_ext F.property ⟨S, hS⟩ e₁ 0 (fun I => by
    ext
    simp [e₁]
    exact hP _ _ I.hf)
  have h1 := congrArg (fun f => f.hom 1) this
  simpa [e₁] using h1

def TwLocGen : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (y : Sec (tw q 1) U),
  Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen 1 ζ

def GmSep : Prop := ∀ (V : Scheme.{0}) (u : (Γ(V, ⊤))ˣ),
  (ofRings.sec unitsF V ⟨Additive.ofMul u⟩ : Sec Gm V) = 0 → u = 1

def CycPow : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] (ζ : Prim q A),
  ∃ u : Aˣ, (u : A) = ζ.1 ∧ ∀ c : ℕ, u ^ c = 1 → q ∣ c ∨ Subsingleton A

def EmptySec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (V : Scheme.{0}), Subsingleton Γ(V, ⊤) →
  ∀ y : Sec F V, y = 0

def KerGen : Prop := ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm),
  LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf.Gen q κ → ∀ (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (c : ℕ),
    Sec.map κ (U := V) (c • twGen 1 ζ) = 0 → (c • twGen 1 ζ : Sec (tw q 1) V) = 0

/- English proof (translation)
Introduce `q _ κ hg V ζ c h`. Take `⟨u, hu, hc⟩` from `hA q _ ζ`. Set `t : Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V` to `twGen 1 ζ`. Establish `h2 : (κ.hom.app (op V)).hom (c • t) = 0` using `h`. Rewrite `h2` using `[map_nsmul]`.

Establish `hgt : (κ.hom.app (op V)).hom t = _` using `hg V ζ u hu`. Rewrite `h2` using `[hgt]`. Establish `h3 : (ofRings.sec unitsF V ⟨Additive.ofMul (u ^ c)⟩ : Sec Gm V) = 0`. Establish `e : (ofRings.sec unitsF V ⟨Additive.ofMul (u ^ c)⟩ : Sec Gm V) = c • ofRings.sec unitsF V ⟨Additive.ofMul u⟩`. Unfold `ofRings.sec`.

Apply the tactic sequence `have ex : (⟨Additive.ofMul (u ^ c)⟩ : ↑((Scheme.Γ ⋙ unitsF).obj (op V))) = c • (⟨Additive.ofMul u⟩ : ↑((Scheme.Γ ⋙ unitsF).obj (op V))) := by first | rfl | (apply ULift.ext; simp [ofMul_pow]) | (apply ULift.ext; rfl)`. Use `erw [ex]`. Conclude with `map_nsmul _ _ _`. Rewrite using `[e]`. Conclude with `h2`.

Break down `hc c (hG V _ h3) with ⟨k, rfl⟩ | hs` into its components or cases. Rewrite using `[mul_comm, mul_nsmul]`. Establish `: ∀ x : Sec (tw q 1) V, q • x = 0` using `fun x => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]`. Establish `: ((q : ℕ) : ULift.{1} (ZMod q)) = 0` using `ULift.ext _ _ (by simp)`.

Rewrite using `[this, zero_smul]`. Conclude with `this _`. Conclude with `hE _ _ V hs _`.
-/
theorem kerGen_of (hG : GmSep) (hA : CycPow) (hE : EmptySec) : KerGen := by
  intro q _ κ hg V ζ c h
  obtain ⟨u, hu, hc⟩ := hA q _ ζ
  let t : Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V := twGen 1 ζ
  have h2 : (κ.hom.app (op V)).hom (c • t) = 0 := h
  rw [map_nsmul] at h2
  have hgt : (κ.hom.app (op V)).hom t = _ := hg V ζ u hu
  rw [hgt] at h2
  have h3 : (ofRings.sec unitsF V ⟨Additive.ofMul (u ^ c)⟩ : Sec Gm V) = 0 := by
    have e : (ofRings.sec unitsF V ⟨Additive.ofMul (u ^ c)⟩ : Sec Gm V) = c • ofRings.sec unitsF V ⟨Additive.ofMul u⟩ := by
      unfold ofRings.sec
      have ex : (⟨Additive.ofMul (u ^ c)⟩ : ↑((Scheme.Γ ⋙ unitsF).obj (op V))) =
          c • (⟨Additive.ofMul u⟩ : ↑((Scheme.Γ ⋙ unitsF).obj (op V))) := by
        first | rfl | (apply ULift.ext; simp [ofMul_pow]) | (apply ULift.ext; rfl)
      erw [ex]
      exact map_nsmul _ _ _
    rw [e]
    exact h2
  rcases hc c (hG V _ h3) with ⟨k, rfl⟩ | hs
  · rw [mul_comm, mul_nsmul]
    have : ∀ x : Sec (tw q 1) V, q • x = 0 := fun x => by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
      have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext _ _ (by simp)
      rw [this, zero_smul]
    exact this _
  · exact hE _ _ V hs _

/- English proof (translation)
Establish `hS` using `shfSep`. Establish `hK` using `kerGen_of hG hA hE`. Introduce `q _ B _ _ κ hg U _`. Use `(injective_iff_map_eq_zero (κ.hom.app (op U)).hom).2 fun y hy => ?_` and prove the remaining obligations. Apply `hS _ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U y` to reduce the goal to its premises.

Take `⟨S, hSc, hP⟩` from `hL q U y`. Use `⟨S, hSc, fun V g hg' => ?_⟩` and prove the remaining obligations. Break down `hP V g hg' with h | ⟨ζ, c, h⟩` into its components or cases. Conclude with `h`. Establish `hn : Sec.map κ (U` using `V) (Sec.res g y) = 0 := by`.

Use `congrArg (fun f => f.hom y) (κ.hom.naturality g.op)` as an intermediate fact. Simplify using `only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this`. Express the relevant statement in the definitionally equal form `(κ.hom.app (op V)).hom (((restr (Int.castRingHom (ZMod q))).obj (tw q 1)).obj.map g.op |>.hom y) = 0`. Rewrite using `[this]`. Express the relevant statement in the definitionally equal form `(Gm.obj.map g.op).hom ((κ.hom.app (op U)).hom y) = 0`.

Rewrite using `[hy, map_zero]`. Express the relevant statement in the definitionally equal form `Sec.res (F := tw q 1) g y = 0`. Express the relevant statement in the definitionally equal form `Sec.map κ (U := V) (Sec.res (F := tw q 1) g y) = 0 at hn`. Rewrite `hn`, the goal using `[h]`. Conclude with `hK q κ hg V ζ c hn`.
-/
theorem LeafKumMuInj_of (hL : TwLocGen) (hG : GmSep) (hA : CycPow) (hE : EmptySec) :
    LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf.LeafKumMuInj := by
  have hS := shfSep
  have hK := kerGen_of hG hA hE
  intro q _ B _ _ κ hg U _
  refine (injective_iff_map_eq_zero (κ.hom.app (op U)).hom).2 fun y hy => ?_
  apply hS _ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U y
  obtain ⟨S, hSc, hP⟩ := hL q U y
  refine ⟨S, hSc, fun V g hg' => ?_⟩
  rcases hP V g hg' with h | ⟨ζ, c, h⟩
  · exact h
  · have hn : Sec.map κ (U := V) (Sec.res g y) = 0 := by
      have := congrArg (fun f => f.hom y) (κ.hom.naturality g.op)
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
      change (κ.hom.app (op V)).hom (((restr (Int.castRingHom (ZMod q))).obj (tw q 1)).obj.map g.op |>.hom y) = 0
      rw [this]
      change (Gm.obj.map g.op).hom ((κ.hom.app (op U)).hom y) = 0
      rw [hy, map_zero]
    change Sec.res (F := tw q 1) g y = 0
    change Sec.map κ (U := V) (Sec.res (F := tw q 1) g y) = 0 at hn
    rw [h] at hn ⊢
    exact hK q κ hg V ζ c hn

end LateralTheory.E.H2CurveOrder.LeafKumMuInjPf

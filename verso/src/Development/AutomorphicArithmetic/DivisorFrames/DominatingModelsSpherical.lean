import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartExtensionHolds
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

/- English proof (translation)
Establish `: X.IsSeparated` using `⟨by rw [← terminal.comp_from s]; infer_instance⟩`. Establish `: IsDominant (spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (((RingHom.injective_iff_ker_eq_bot _).1 (Formalism.MainNotions.DIV.Cons.intO C).subtype_injective).le.trans bot_le)⟩`. Conclude with `ext_of_isDominant _ h`.
-/
private theorem ext_uniq {X : Scheme.{0}} {O : Type} [CommRing O] (s : X ⟶ Sp O) [IsProper s] {C : Type}
    [NontriviallyNormedField C] [IsUltrametricDist C] (x y : Sp ↥(Formalism.MainNotions.DIV.Cons.intO C) ⟶ X)
    (h : spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype ≫ y = spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype ≫ x) : y = x := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  have : IsDominant (spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (Formalism.MainNotions.DIV.Cons.intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

/- English proof (translation)
Use `GlobalTheory.LocM.Cht.isFractionRing_ball C` as an intermediate fact. Establish `hE : ValuativeCriterion.Existence s` using `(UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) : (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) s).1`. Set `S : ValuativeCommSq s` to `{ R := ↥(Formalism.MainNotions.DIV.Cons.intO C) K := C i₁ := w i₂ := spMap a commSq := ⟨hs⟩ }`. Take `⟨⟨l⟩⟩` from `hE S`. Conclude with `⟨l.l, l.fac_left, l.fac_right⟩`.
-/
private theorem ext_ex {X : Scheme.{0}} {O : Type} [CommRing O] (s : X ⟶ Sp O) [IsProper s] {C : Type}
    [NontriviallyNormedField C] [IsUltrametricDist C] (a : O →+* ↥(Formalism.MainNotions.DIV.Cons.intO C)) (w : Sp C ⟶ X)
    (hs : w ≫ s = spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype ≫ spMap a) :
    ∃ z : Sp ↥(Formalism.MainNotions.DIV.Cons.intO C) ⟶ X, spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype ≫ z = w ∧ z ≫ s = spMap a := by
  have := GlobalTheory.LocM.Cht.isFractionRing_ball C
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) s).1
  let S : ValuativeCommSq s :=
    { R := ↥(Formalism.MainNotions.DIV.Cons.intO C)
      K := C
      i₁ := w
      i₂ := spMap a
      commSq := ⟨hs⟩ }
  obtain ⟨⟨l⟩⟩ := hE S
  exact ⟨l.l, l.fac_left, l.fac_right⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O₁ O₂ _ _ β₁ β₂ Z₁ Z₂ b hb hD p C P u₁ u₂ ht hT k st`. Take `⟨f, t, m₁, m₂, hf, hj, hφ⟩` from `hD`. Establish `pr₁ : IsProper Z₁.s` using `projProper _ _ _ Z₁.proj`. Establish `pr₂ : IsProper Z₂.s` using `projProper _ _ _ Z₂.proj`. Establish `w : Z₁.j ≫ Z₁.s = (pullback.snd _ _ ≫ spMap β₂) ≫ spMap b`.

Rewrite using `[ModelRelProbe.j_over, Category.assoc, ModelRelProbe.spMap_comp, hb]`. Set `a : Xo.XF c ⟶ pullback Z₁.s (spMap b)` to `pullback.lift _ _ w`. Establish `a1 : a ≫ pullback.fst _ _ = Z₁.j` using `pullback.lift_fst _ _ _`. Establish `a2 : a ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap β₂` using `pullback.lift_snd _ _ _`. Establish `a3 : a ≫ f = Z₂.j` using `hj a a1`.

Take `⟨x', hx', -⟩` from `ext_ex (pullback.snd Z₁.s (spMap b)) P.alg (P.y ≫ a) (by`. Rewrite using `[Category.assoc, a2, ← Category.assoc, P.y_over, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, P.compat])`. Establish `e₁ : P.y ≫ Z₁.j = spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ x' ≫ pullback.fst _ _`. Rewrite using `[← Category.assoc, hx', Category.assoc, a1]`. Establish `e₂ : P.y ≫ Z₂.j = spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ x' ≫ f`.

Rewrite using `[← Category.assoc, hx', Category.assoc, a3]`. Establish `c₁ : IsPullback m₁.φ t.G.hom Z₁.t.G.hom (pullback.fst _ _)` using `m₁.cart.1`. Establish `c₂ : IsPullback m₂.φ t.G.hom Z₂.t.G.hom f` using `m₂.cart.1`. Establish `c₃ : IsPullback Z₁.m.φ Z₁.oF.t.G.hom Z₁.t.G.hom Z₁.j` using `Z₁.m.cart.1`. Establish `key : ∀ σ i, ∃ v : Sp (DualNumber ↥C.S) ⟶ t.G.left, IsTanAtG t (spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ x') v ∧ v ≫ m₁.φ = u₁ σ i ∧ v ≫ m₂.φ = u₂ σ i`.

Introduce `σ i`. Take `⟨w₁, w₂, h₁, h₂, h₃, h₄, h₅⟩` from `hT σ i`. Establish `hx : (spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ x') ≫ f = P.y ≫ Z₂.j` using `by rw [Category.assoc, e₂]`. Take `⟨v, hv⟩` from `(GlobalTheory.LieMet.pushE m₂ _ hx).surjective (GlobalTheory.LieMet.tanOf (ht σ i))`. Establish `hv' : (PullbackSections.tv v).left ≫ m₂.φ = u₂ σ i` using `congrArg (fun z => (PullbackSections.tv z).left) hv`.

Establish `tv` using `GlobalTheory.LieMet.isTan_tv v`. Establish `ww : u₁ σ i ≫ Z₁.t.G.hom = (spMap (algebraMap ↥C.S (DualNumber ↥C.S)) ≫ spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ x') ≫ pullback.fst _ _`. Rewrite using `[← h₄, Category.assoc, c₃.w, ← Category.assoc, h₁, Category.assoc, e₁]`. Simplify using `only [Category.assoc]`. Establish `l₁` using `c₁.lift_fst _ _ ww`.

Establish `l₂` using `c₁.lift_snd _ _ ww`. Establish `l₃ : c₁.lift _ _ ww ≫ m₂.φ = u₂ σ i` using `(hφ _ (c₁.lift _ _ ww) w₁ w₂ (l₁.trans h₄.symm) h₃ (h₁.trans h₂.symm)).trans h₅`. Establish `e : c₁.lift _ _ ww = (PullbackSections.tv v).left` using `c₂.hom_ext (l₃.trans hv'.symm) (l₂.trans tv.1.symm)`. Conclude with `⟨_, tv, e ▸ l₁, hv'⟩`. Use `choose u hu hu₁ hu₂ using key`.

Establish `q₁` using `Pull.lnStep_push (Dw := Dw) (p := p) m₁ k x' (fun y hy => ext_uniq Z₁.s _ y hy) (u := u) hu st`. Establish `q₂` using `Pull.lnStep_push (Dw := Dw) (p := p) m₂ k x' (fun y hy => ext_uniq Z₂.s _ y hy) (u := u) hu st`. Establish `f₁ : (fun τ i => u τ i ≫ m₁.φ) = u₁` using `funext fun τ => funext fun i => hu₁ τ i`. Establish `f₂ : (fun τ i => u τ i ≫ m₂.φ) = u₂` using `funext fun τ => funext fun i => hu₂ τ i`. Rewrite `q₁` using `[f₁, ← e₁]`.

Rewrite `q₂` using `[f₂, ← e₂]`. Conclude with `q₁.symm.trans q₂`.
-/
theorem UpperTheory.dominating_models_spherical :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O₁ O₂ : Type) [CommRing O₁] [CommRing O₂] (β₁ : O₁ →+* c.F) (β₂ : O₂ →+* c.F) (Z₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β₁) (Z₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β₂) (b : O₁ →+* O₂), β₂.comp b = β₁ → Dominates Z₁ Z₂ b → ∀ (p : ℕ) (C : Formalism.MainNotions.DIV.Cons.SCF p) (P : PointsOfFlagModel.PtC Z₂ C) (u₁ : Vecs Dw Z₁.t ↥C.S) (u₂ : Vecs Dw Z₂.t ↥C.S), (∀ σ i, IsTanAtG Z₂.t (P.y ≫ Z₂.j) (u₂ σ i)) → (∀ σ i, Transp Z₁ Z₂ P.y (u₁ σ i) (u₂ σ i)) → ∀ (k : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ), lnStep Z₁.t (P.y ≫ Z₁.j) u₁ p k st = lnStep Z₂.t (P.y ≫ Z₂.j) u₂ p k st := by
  intro E _ _ _ H Dw l Xo c O₁ O₂ _ _ β₁ β₂ Z₁ Z₂ b hb hD p C P u₁ u₂ ht hT k st
  obtain ⟨f, t, m₁, m₂, hf, hj, hφ⟩ := hD
  have pr₁ : IsProper Z₁.s := projProper _ _ _ Z₁.proj
  have pr₂ : IsProper Z₂.s := projProper _ _ _ Z₂.proj
  have w : Z₁.j ≫ Z₁.s = (pullback.snd _ _ ≫ spMap β₂) ≫ spMap b := by
    rw [ModelRelProbe.j_over, Category.assoc, ModelRelProbe.spMap_comp, hb]
  let a : Xo.XF c ⟶ pullback Z₁.s (spMap b) := pullback.lift _ _ w
  have a1 : a ≫ pullback.fst _ _ = Z₁.j := pullback.lift_fst _ _ _
  have a2 : a ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap β₂ := pullback.lift_snd _ _ _
  have a3 : a ≫ f = Z₂.j := hj a a1
  obtain ⟨x', hx', -⟩ := ext_ex (pullback.snd Z₁.s (spMap b)) P.alg (P.y ≫ a) (by
    rw [Category.assoc, a2, ← Category.assoc, P.y_over, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, P.compat])
  have e₁ : P.y ≫ Z₁.j = spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ x' ≫ pullback.fst _ _ := by
    rw [← Category.assoc, hx', Category.assoc, a1]
  have e₂ : P.y ≫ Z₂.j = spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ x' ≫ f := by
    rw [← Category.assoc, hx', Category.assoc, a3]
  have c₁ : IsPullback m₁.φ t.G.hom Z₁.t.G.hom (pullback.fst _ _) := m₁.cart.1
  have c₂ : IsPullback m₂.φ t.G.hom Z₂.t.G.hom f := m₂.cart.1
  have c₃ : IsPullback Z₁.m.φ Z₁.oF.t.G.hom Z₁.t.G.hom Z₁.j := Z₁.m.cart.1
  have key : ∀ σ i, ∃ v : Sp (DualNumber ↥C.S) ⟶ t.G.left,
      IsTanAtG t (spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ x') v ∧ v ≫ m₁.φ = u₁ σ i ∧ v ≫ m₂.φ = u₂ σ i := by
    intro σ i
    obtain ⟨w₁, w₂, h₁, h₂, h₃, h₄, h₅⟩ := hT σ i
    have hx : (spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ x') ≫ f = P.y ≫ Z₂.j := by rw [Category.assoc, e₂]
    obtain ⟨v, hv⟩ := (GlobalTheory.LieMet.pushE m₂ _ hx).surjective (GlobalTheory.LieMet.tanOf (ht σ i))
    have hv' : (PullbackSections.tv v).left ≫ m₂.φ = u₂ σ i := congrArg (fun z => (PullbackSections.tv z).left) hv
    have tv := GlobalTheory.LieMet.isTan_tv v
    have ww : u₁ σ i ≫ Z₁.t.G.hom = (spMap (algebraMap ↥C.S (DualNumber ↥C.S)) ≫
        spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ x') ≫ pullback.fst _ _ := by
      rw [← h₄, Category.assoc, c₃.w, ← Category.assoc, h₁, Category.assoc, e₁]
      simp only [Category.assoc]
    have l₁ := c₁.lift_fst _ _ ww
    have l₂ := c₁.lift_snd _ _ ww
    have l₃ : c₁.lift _ _ ww ≫ m₂.φ = u₂ σ i :=
      (hφ _ (c₁.lift _ _ ww) w₁ w₂ (l₁.trans h₄.symm) h₃ (h₁.trans h₂.symm)).trans h₅
    have e : c₁.lift _ _ ww = (PullbackSections.tv v).left := c₂.hom_ext (l₃.trans hv'.symm) (l₂.trans tv.1.symm)
    exact ⟨_, tv, e ▸ l₁, hv'⟩
  choose u hu hu₁ hu₂ using key
  have q₁ := Pull.lnStep_push (Dw := Dw) (p := p) m₁ k x' (fun y hy => ext_uniq Z₁.s _ y hy) (u := u) hu st
  have q₂ := Pull.lnStep_push (Dw := Dw) (p := p) m₂ k x' (fun y hy => ext_uniq Z₂.s _ y hy) (u := u) hu st
  have f₁ : (fun τ i => u τ i ≫ m₁.φ) = u₁ := funext fun τ => funext fun i => hu₁ τ i
  have f₂ : (fun τ i => u τ i ≫ m₂.φ) = u₂ := funext fun τ => funext fun i => hu₂ τ i
  rw [f₁, ← e₁] at q₁
  rw [f₂, ← e₂] at q₂
  exact q₁.symm.trans q₂

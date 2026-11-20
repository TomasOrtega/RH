import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

/- English proof (translation)
Conclude with `Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)`.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨hE, -⟩ : ValuativeCriterion.Existence s ∧ QuasiCompact s := by`. Establish `: (ValuativeCriterion.Existence ⊓ @QuasiCompact) s`. Rewrite using `[← UniversallyClosed.eq_valuativeCriterion]`. Use `infer_instance`. Conclude with `this`.

Take `⟨⟨l⟩⟩` from `hE ⟨R, FractionRing R, y, r, ⟨h⟩⟩`. Conclude with `⟨l.l, l.fac_left, l.fac_right⟩`.
-/
theorem val_exists {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] {X S : Scheme.{0}} (s : X ⟶ S) [IsProper s]
    (y : Sp (FractionRing R) ⟶ X) (r : Sp R ⟶ S) (h : y ≫ s = Out.jK R ≫ r) :
    ∃ x : Sp R ⟶ X, Out.jK R ≫ x = y ∧ x ≫ s = r := by
  obtain ⟨hE, -⟩ : ValuativeCriterion.Existence s ∧ QuasiCompact s := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact this
  obtain ⟨⟨l⟩⟩ := hE ⟨R, FractionRing R, y, r, ⟨h⟩⟩
  exact ⟨l.l, l.fac_left, l.fac_right⟩

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨hU, -⟩ : ValuativeCriterion.Uniqueness s ∧ QuasiSeparated s := by`. Establish `: (ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated) s`. Rewrite using `[← IsSeparated.eq_valuativeCriterion]`. Use `infer_instance`. Conclude with `this`.

Establish `hsq : CommSq (Out.jK R ≫ x) (Out.jK R) s (x ≫ s)` using `⟨Category.assoc _ _ _⟩`. Establish `hs` using `hU ⟨R, FractionRing R, Out.jK R ≫ x, x ≫ s, hsq⟩`. Conclude with `congrArg CommSq.LiftStruct.l (@Subsingleton.elim _ hs ⟨x, rfl, rfl⟩ ⟨x', h.symm, h'.symm⟩)`.
-/
theorem val_unique {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] {X S : Scheme.{0}} (s : X ⟶ S) [IsSeparated s]
    (x x' : Sp R ⟶ X) (h : Out.jK R ≫ x = Out.jK R ≫ x') (h' : x ≫ s = x' ≫ s) : x = x' := by
  obtain ⟨hU, -⟩ : ValuativeCriterion.Uniqueness s ∧ QuasiSeparated s := by
    have : (ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated) s := by
      rw [← IsSeparated.eq_valuativeCriterion]; infer_instance
    exact this
  have hsq : CommSq (Out.jK R ≫ x) (Out.jK R) s (x ≫ s) := ⟨Category.assoc _ _ _⟩
  have hs := hU ⟨R, FractionRing R, Out.jK R ≫ x, x ≫ s, hsq⟩
  exact congrArg CommSq.LiftStruct.l (@Subsingleton.elim _ hs ⟨x, rfl, rfl⟩ ⟨x', h.symm, h'.symm⟩)

/- English proof (translation)
Establish `key : ∀ (K : Type) [Field K] (t : Sp K ⟶ S'), IsProper (pullback.snd G'.hom t) ↔ IsProper (pullback.snd G.hom (t ≫ f))`. Introduce `K _ t`. Establish `hp` using `(IsPullback.of_hasPullback G'.hom t).paste_horiz h`. Establish `e : pullback.snd G'.hom t = hp.isoPullback.hom ≫ pullback.snd G.hom (t ≫ f)` using `hp.isoPullback_hom_snd.symm`. Rewrite using `[e]`.

Prove the components needed by the constructor for the conclusion. Introduce `hpr`. Rewrite using `[← Iso.inv_hom_id_assoc hp.isoPullback (pullback.snd G.hom (t ≫ f))]`. Use `infer_instance`. Introduce `hpr infer_instance`.

Prove the components needed by the constructor for the conclusion. Introduce `hfx`. Establish `hfx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), f x ∈ Set.range t → IsProper (pullback.snd G.hom t)` using `hfx`. Introduce `K _ _ t hxt`. Take `⟨p, hp⟩` from `hxt`.

Conclude with `(key K t).2 (hfx' K (t ≫ f) ⟨p, congrArg (fun y => f y) hp⟩)`. Introduce `hx`. Establish `hx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S'), x ∈ Set.range t → IsProper (pullback.snd G'.hom t)` using `hx`. Set `κ` to `AlgebraicClosure (S'.residueField x)`. Set `t : Sp κ ⟶ S'` to `Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ)) ≫ S'.fromSpecResidueField x`.

Establish `hxt : x ∈ Set.range t`. Establish `hr` using `Scheme.range_fromSpecResidueField (X := S') x`. Use `⟨IsLocalRing.closedPoint κ, ?_⟩` and prove the remaining obligations. Establish `hm : (S'.fromSpecResidueField x).base ((Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ))).base (IsLocalRing.closedPoint κ)) ∈ ({x} : Set S')` using `hr ▸ ⟨_, rfl⟩`. Conclude with `hm`.

Establish `hp` using `(key κ t).1 (hx' κ t hxt)`. Take `⟨p, hp'⟩` from `hxt`. Conclude with `hA S G hG κ (t ≫ f) hp ⟨p, congrArg (fun y => f y) hp'⟩`.
-/
theorem abLocus_pullback (hA : AbLocusOneSt) {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G]
    (hG : IsSemiAbelian G) {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f) (x : S') :
    f x ∈ abLocus G ↔ x ∈ abLocus G' := by
  have key : ∀ (K : Type) [Field K] (t : Sp K ⟶ S'),
      IsProper (pullback.snd G'.hom t) ↔ IsProper (pullback.snd G.hom (t ≫ f)) := by
    intro K _ t
    have hp := (IsPullback.of_hasPullback G'.hom t).paste_horiz h
    have e : pullback.snd G'.hom t = hp.isoPullback.hom ≫ pullback.snd G.hom (t ≫ f) :=
      hp.isoPullback_hom_snd.symm
    rw [e]
    constructor
    · intro hpr
      rw [← Iso.inv_hom_id_assoc hp.isoPullback (pullback.snd G.hom (t ≫ f))]
      infer_instance
    · intro hpr
      infer_instance
  constructor
  · intro hfx
    have hfx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), f x ∈ Set.range t →
        IsProper (pullback.snd G.hom t) := hfx
    intro K _ _ t hxt
    obtain ⟨p, hp⟩ := hxt
    exact (key K t).2 (hfx' K (t ≫ f) ⟨p, congrArg (fun y => f y) hp⟩)
  · intro hx
    have hx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S'), x ∈ Set.range t →
        IsProper (pullback.snd G'.hom t) := hx
    let κ := AlgebraicClosure (S'.residueField x)
    let t : Sp κ ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ)) ≫
      S'.fromSpecResidueField x
    have hxt : x ∈ Set.range t := by
      have hr := Scheme.range_fromSpecResidueField (X := S') x
      refine ⟨IsLocalRing.closedPoint κ, ?_⟩
      have hm : (S'.fromSpecResidueField x).base
          ((Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ))).base
            (IsLocalRing.closedPoint κ)) ∈ ({x} : Set S') := hr ▸ ⟨_, rfl⟩
      exact hm
    have hp := (key κ t).1 (hx' κ t hxt)
    obtain ⟨p, hp'⟩ := hxt
    exact hA S G hG κ (t ≫ f) hp ⟨p, congrArg (fun y => f y) hp'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

/- English proof (translation)
Rewrite using `[Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]`.
-/
theorem Model.j_s {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

/- English proof (translation)
Use `⟨fun h => hc T g gg g₂ h h₀ h₁, fun h2 => ?_⟩` and prove the remaining obligations. Establish `w1 : (gg ≫ Yg.m.φ) ≫ Yg.t.G.hom = (g ≫ t₁.G.hom) ≫ pullback.fst Yg.s (spMap b)`. Establish `e1` using `Yg.m.cart.1.w`. Establish `e2 : aF ≫ pullback.fst Yg.s (spMap b) = Yg.jQ ≫ pullback.fst _ _` using `haF`. Simplify using `only [SABMap.φ, Category.assoc] at e1 ⊢`.

Rewrite using `[e1, reassoc_of% hb, e2]`. Set `k` to `m₁.cart.1.lift (gg ≫ Yg.m.φ) (g ≫ t₁.G.hom) w1`. Establish `hk1 : k ≫ m₁.φ = gg ≫ Yg.m.φ` using `m₁.cart.1.lift_fst _ _ _`. Establish `hk2 : k ≫ t₁.G.hom = g ≫ t₁.G.hom` using `m₁.cart.1.lift_snd _ _ _`. Establish `hk3 : k ≫ m₂.φ = g₂ ≫ Y.m.φ` using `hc T k gg g₂ hk1 h₀ h₁`.

Establish `hkg : k = g` using `m₂.cart.1.hom_ext (by rw [hk3, h2]) hk2`. Rewrite using `[← hkg]`. Conclude with `hk1`.
-/
theorem dom_iff {O₀ O : Type} [CommRing O₀] [CommRing O] {β₀ : O₀ →+* c.F} {β : O →+* c.F} {b : O₀ →+* O}
    {Yg : Model Xo c β₀} {Y : Model Xo c β} {f : pullback Yg.s (spMap b) ⟶ Y.X} {t₁ : SAB H (pullback Yg.s (spMap b))}
    (m₁ : SABMap t₁ Yg.t (pullback.fst _ _)) (m₂ : SABMap t₁ Y.t f)
    (hc : ∀ (T : Scheme.{0}) (g : T ⟶ t₁.G.left) (g₁ : T ⟶ Yg.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Yg.m.φ → g₁ ≫ Yg.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ →
      g₁ ≫ Yg.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ m₂.φ = g₂ ≫ Y.m.φ)
    (aF : Xo.XF c ⟶ pullback Yg.s (spMap b)) (haF : aF ≫ pullback.fst _ _ = Yg.j) {T : Scheme.{0}}
    (g : T ⟶ t₁.G.left) (gg : T ⟶ Yg.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left)
    (h₀ : gg ≫ Yg.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ) (h₁ : gg ≫ Yg.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom)
    (hb : g ≫ t₁.G.hom = gg ≫ Yg.oF.t.G.hom ≫ aF) : g ≫ m₁.φ = gg ≫ Yg.m.φ ↔ g ≫ m₂.φ = g₂ ≫ Y.m.φ := by
  refine ⟨fun h => hc T g gg g₂ h h₀ h₁, fun h2 => ?_⟩
  have w1 : (gg ≫ Yg.m.φ) ≫ Yg.t.G.hom = (g ≫ t₁.G.hom) ≫ pullback.fst Yg.s (spMap b) := by
    have e1 := Yg.m.cart.1.w
    have e2 : aF ≫ pullback.fst Yg.s (spMap b) = Yg.jQ ≫ pullback.fst _ _ := haF
    simp only [SABMap.φ, Category.assoc] at e1 ⊢
    rw [e1, reassoc_of% hb, e2]
  let k := m₁.cart.1.lift (gg ≫ Yg.m.φ) (g ≫ t₁.G.hom) w1
  have hk1 : k ≫ m₁.φ = gg ≫ Yg.m.φ := m₁.cart.1.lift_fst _ _ _
  have hk2 : k ≫ t₁.G.hom = g ≫ t₁.G.hom := m₁.cart.1.lift_snd _ _ _
  have hk3 : k ≫ m₂.φ = g₂ ≫ Y.m.φ := hc T k gg g₂ hk1 h₀ h₁
  have hkg : k = g := m₂.cart.1.hom_ext (by rw [hk3, h2]) hk2
  rw [← hkg]
  exact hk1

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c k _ bF a O₀ O O' _ _ _ β₀ β β' b b' Yg Y Y' hb hb' hmono hD hD' χ W y hχ hy hys`. Take `⟨f, t₁, m₁, m₂, hf, hj, hc⟩` from `hD`. Take `⟨f', t₁', m₁', m₂', hf', hj', hc'⟩` from `hD'`. Use `hP _ _ _ Yg.proj` as an intermediate fact. Use `hP _ _ _ Y.proj` as an intermediate fact.

Establish `e₀ : spMap β₀ = spMap β ≫ spMap b` using `by rw [← hb, spMap_comp]`. Establish `e₀' : spMap β₀ = spMap β' ≫ spMap b'` using `by rw [← hb', spMap_comp]`. Take `⟨χg, hg₁, hg₂⟩` from `val_exists Yg.s (y ≫ Yg.j) (spMap (PowerSeries.C (R := k)) ≫ spMap bF ≫ spMap β₀) (by rw [Category.assoc, Yg.j_s, ← Category.assoc, hys]; simp only [Category.assoc])`. Establish `mk : ∀ {O : Type} [CommRing O] (β : O →+* c.F) (b : O₀ →+* O), spMap β₀ = spMap β ≫ spMap b → ∃ (χ₁ : Sp (PowerSeries k) ⟶ pullback Yg.s (spMap b)) (aF : Xo.XF c ⟶ pullback Yg.s (spMap b)), χ₁ ≫ pullback.fst _ _ = χg ∧ χ₁ ≫ pullback.snd _ _ = spMap (PowerSeries.C (R` using `k)) ≫ spMap (bF.comp β) ∧ aF ≫ pullback.fst _ _ = Yg.j ∧ Out.jK (PowerSeries k) ≫ χ₁ = y ≫ aF := by`. Introduce `O _ β b e`.

Use `⟨pullback.lift χg (spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β)) (by rw [hg₂, e, spMap_comp]; simp only [Category.assoc]), pullback.lift Yg.j (pullback.snd _ _ ≫ spMap β) (by rw [Yg.j_s, e, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, pullback.lift_fs …` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, hg₁]`. Rewrite using `[Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc y, hys, spMap_comp]`. Simplify using `only [Category.assoc]`.

Take `⟨χ₁, aF, h1, h2, h3, h4⟩` from `mk β b e₀`. Take `⟨χ₁', aF', h1', h2', h3', h4'⟩` from `mk β' b' e₀'`. Establish `hχ₁ : χ = χ₁ ≫ f` using `val_unique Y.s _ _ (by rw [← hy, ← Category.assoc, h4, Category.assoc, hj aF h3]) (by rw [hχ, Category.assoc, hf, h2])`. Substitute `hχ₁` using the available equality. Take `⟨n₁, hn₁⟩` from `hX E H _ _ _ _ _ _ _ _ m₂ W.m`.

Take `⟨ng, hng⟩` from `hC E H _ _ _ _ _ _ _ _ m₁ n₁`. Establish `cancel : ∀ (p : Sp (PowerSeries k) ⟶ Yg.X) (_ : p = χ₁' ≫ pullback.fst _ _) (n : SABMap W.t Yg.t p), ∃ m' : SABMap W.t t₁' χ₁', n.φ = m'.φ ≫ m₁'.φ`. Introduce `p hp n`. Substitute `hp` using the available equality. Conclude with `hX E H _ _ _ _ _ _ _ _ m₁' n`.

Take `⟨n₁', hn₁'⟩` from `cancel _ (h1.trans h1'.symm) ng`. Take `⟨m', hm'⟩` from `hC E H _ _ _ _ _ _ _ _ m₂' n₁'`. Establish `hy' : y ≫ Y'.j = Out.jK (PowerSeries k) ≫ χ₁' ≫ f'`. Rewrite using `[← Category.assoc, h4', Category.assoc, hj' aF' h3']`. Establish `tr : ∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left) (τ : T ⟶ Sp (FractionRing (PowerSeries k))), g ≫ W.t.G.hom = τ ≫ Out.jK (PowerSeries k) → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = …`.

Introduce `T g g₁ g₂ τ hg hg₁ k₀ k₁`. Establish `w : (g₁ ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom = (g₁ ≫ Y.oF.t.G.hom) ≫ pullback.fst _ _`. Rewrite using `[Category.assoc, Y.m0.toSABMap.cart.1.w, Category.assoc]`. Establish `u₀` using `Yg.m0.toSABMap.cart.1.lift_fst _ _ w`. Establish `u₁` using `Yg.m0.toSABMap.cart.1.lift_snd _ _ w`.

Establish `A` using `dom_iff m₁ m₂ hc aF h3 (g ≫ n₁.φ) _ g₁ u₀ u₁ (by`. Rewrite using `[Category.assoc, n₁.cart.1.w, ← Category.assoc, hg, Category.assoc, h4, ← Category.assoc _ Yg.oF.t.G.hom aF, u₁, hg₁, Category.assoc])`. Establish `B` using `dom_iff m₁' m₂' hc' aF' h3' (g ≫ n₁'.φ) _ g₂ (u₀.trans k₀) (u₁.trans k₁) (by`. Rewrite using `[Category.assoc, n₁'.cart.1.w, ← Category.assoc, hg, Category.assoc, h4', ← Category.assoc _ Yg.oF.t.G.hom aF', u₁, hg₁, Category.assoc])`. Rewrite using `[hn₁, hm', ← Category.assoc, ← Category.assoc, ← A, ← B, Category.assoc, Category.assoc, ← hng, ← hn₁']`.

Establish `: Mono Y'.j`. Use `Y'.jQ_open` as an intermediate fact. Use `hmono` as an intermediate fact. Unfold `Model.j`. Use `infer_instance`.

Take `⟨s1, s2, s3, s4, s5, s6⟩` from `W.spec`. Use `⟨χ₁' ≫ f', ⟨W.t, m', W.P, W.φ, W.he, W.w, W.e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu => ⟨(s6 F uF ha hu).1, fun yF hyF n p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩, ?_, hy', fun x => ?_, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun T g g' g₁ g₂ τ hgg hg hg₁ h k₀ k₁ => ?_⟩` and prove the remaining obligations. Establish `hyF' : yF = Out.jFK (R` using `PowerSeries k) F ≫ y := by`. Rewrite using `[← cancel_mono Y'.j, hyF, Category.assoc, hy']`. Establish `base : (x.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK (PowerSeries k))) ≫ W.t.G.hom = Out.jFK (R` using `PowerSeries k) F ≫ Out.jK (PowerSeries k) := by`.

Establish `a₁ : W.P.U.gen.inv.left ≫ pullback.snd W.t.G.hom (Out.jK (PowerSeries k)) = W.P.A.A.hom` using `Over.w W.P.U.gen.inv`. Establish `a₂ : x.left ≫ W.P.A.A.hom = Out.jFK (R` using `PowerSeries k) F := Over.w x`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd _ _), a₁, ← Category.assoc, a₂]`. Establish `go : ∀ (σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), σY.left ≫ Y.m0.toSABMap.φ = σ.left ≫ Y'.m0.toSABMap.φ → x.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK (PowerSeries k)) ≫ W.m.φ = yF ≫ σY.left ≫ Y.m.φ`. Introduce `σY hσY`.

Establish `b₁ : σY.left ≫ Y.oF.t.G.hom = 𝟙 _` using `Over.w σY`. Establish `b₂ : σ.left ≫ Y'.oF.t.G.hom = 𝟙 _` using `Over.w σ`. Use `(tr _ _ (yF ≫ σY.left) (yF ≫ σ.left) _ base (by rw [Category.assoc, b₁, hyF']; exact Category.comp_id _) (by rw [Category.assoc, hσY, Category.assoc]) (by rw [Category.assoc, b₁, Category.assoc, b₂])).2 (by simpa only [Category.assoc] using e4)` as an intermediate fact. Simplify `this` using `only [Category.assoc]`. Establish `hyY : yF ≫ Y.j = Out.jFK (R` using `PowerSeries k) F ≫ Out.jK (PowerSeries k) ≫ χ₁ ≫ f := by`.

Rewrite using `[hyF', Category.assoc, hy]`. Break down `hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩` into its components or cases. Conclude with `(s6 F uF ha hu).2 yF hyY n p₀ (Y.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3 (go _ ((Y.m0.etaA v).trans (Y'.m0.etaA v).symm))`. Conclude with `(s6 F uF ha hu).2 yF hyY n p₀ (Y.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3 (go _ ((Y.m0.eta v).trans (Y'.m0.eta v).symm))`. Rewrite using `[Category.assoc, hf', h2']`.

Establish `q₁` using `abLocus_pullback hA Y'.t.semi m'.cart.1 x`. Establish `q₂` using `abLocus_pullback hA Y.t.semi W.m.cart.1 x`. Conclude with `q₁.trans q₂.symm`. Establish `hgg' : (show T ⟶ W.t.G.left from g') = g` using `eq_of_heq hgg`. Establish `q` using `(tr T g g₁ g₂ τ hg hg₁ k₀ k₁).1 h`.

Rewrite `q` using `[← hgg']`. Conclude with `q`.
-/
theorem oneArc (hC : SABCompSt) (hX : SABCancelSt) (hA : AbLocusOneSt) (hP : ProjProperSt) : OneArcSt := by
  intro E _ _ _ H D l Xo c k _ bF a O₀ O O' _ _ _ β₀ β β' b b' Yg Y Y' hb hb' hmono hD hD' χ W y hχ hy hys
  obtain ⟨f, t₁, m₁, m₂, hf, hj, hc⟩ := hD
  obtain ⟨f', t₁', m₁', m₂', hf', hj', hc'⟩ := hD'
  have := hP _ _ _ Yg.proj
  have := hP _ _ _ Y.proj
  have e₀ : spMap β₀ = spMap β ≫ spMap b := by rw [← hb, spMap_comp]
  have e₀' : spMap β₀ = spMap β' ≫ spMap b' := by rw [← hb', spMap_comp]
  obtain ⟨χg, hg₁, hg₂⟩ := val_exists Yg.s (y ≫ Yg.j) (spMap (PowerSeries.C (R := k)) ≫ spMap bF ≫ spMap β₀)
    (by rw [Category.assoc, Yg.j_s, ← Category.assoc, hys]; simp only [Category.assoc])
  have mk : ∀ {O : Type} [CommRing O] (β : O →+* c.F) (b : O₀ →+* O), spMap β₀ = spMap β ≫ spMap b →
      ∃ (χ₁ : Sp (PowerSeries k) ⟶ pullback Yg.s (spMap b)) (aF : Xo.XF c ⟶ pullback Yg.s (spMap b)),
        χ₁ ≫ pullback.fst _ _ = χg ∧ χ₁ ≫ pullback.snd _ _ = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β) ∧
        aF ≫ pullback.fst _ _ = Yg.j ∧ Out.jK (PowerSeries k) ≫ χ₁ = y ≫ aF := by
    intro O _ β b e
    refine ⟨pullback.lift χg (spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β))
        (by rw [hg₂, e, spMap_comp]; simp only [Category.assoc]),
      pullback.lift Yg.j (pullback.snd _ _ ≫ spMap β) (by rw [Yg.j_s, e, Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, hg₁]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc y, hys, spMap_comp]
      simp only [Category.assoc]
  obtain ⟨χ₁, aF, h1, h2, h3, h4⟩ := mk β b e₀
  obtain ⟨χ₁', aF', h1', h2', h3', h4'⟩ := mk β' b' e₀'
  have hχ₁ : χ = χ₁ ≫ f := val_unique Y.s _ _
    (by rw [← hy, ← Category.assoc, h4, Category.assoc, hj aF h3]) (by rw [hχ, Category.assoc, hf, h2])
  subst hχ₁
  obtain ⟨n₁, hn₁⟩ := hX E H _ _ _ _ _ _ _ _ m₂ W.m
  obtain ⟨ng, hng⟩ := hC E H _ _ _ _ _ _ _ _ m₁ n₁
  have cancel : ∀ (p : Sp (PowerSeries k) ⟶ Yg.X) (_ : p = χ₁' ≫ pullback.fst _ _) (n : SABMap W.t Yg.t p),
      ∃ m' : SABMap W.t t₁' χ₁', n.φ = m'.φ ≫ m₁'.φ := by
    intro p hp n; subst hp; exact hX E H _ _ _ _ _ _ _ _ m₁' n
  obtain ⟨n₁', hn₁'⟩ := cancel _ (h1.trans h1'.symm) ng
  obtain ⟨m', hm'⟩ := hC E H _ _ _ _ _ _ _ _ m₂' n₁'
  have hy' : y ≫ Y'.j = Out.jK (PowerSeries k) ≫ χ₁' ≫ f' := by
    rw [← Category.assoc, h4', Category.assoc, hj' aF' h3']

  have tr : ∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left)
      (τ : T ⟶ Sp (FractionRing (PowerSeries k))), g ≫ W.t.G.hom = τ ≫ Out.jK (PowerSeries k) →
      g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ →
      g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → (g ≫ W.m.φ = g₁ ≫ Y.m.φ ↔ g ≫ m'.φ = g₂ ≫ Y'.m.φ) := by
    intro T g g₁ g₂ τ hg hg₁ k₀ k₁
    have w : (g₁ ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom = (g₁ ≫ Y.oF.t.G.hom) ≫ pullback.fst _ _ := by
      rw [Category.assoc, Y.m0.toSABMap.cart.1.w, Category.assoc]
    have u₀ := Yg.m0.toSABMap.cart.1.lift_fst _ _ w
    have u₁ := Yg.m0.toSABMap.cart.1.lift_snd _ _ w
    have A := dom_iff m₁ m₂ hc aF h3 (g ≫ n₁.φ) _ g₁ u₀ u₁ (by
      rw [Category.assoc, n₁.cart.1.w, ← Category.assoc, hg, Category.assoc, h4, ← Category.assoc _ Yg.oF.t.G.hom aF, u₁,
        hg₁, Category.assoc])
    have B := dom_iff m₁' m₂' hc' aF' h3' (g ≫ n₁'.φ) _ g₂ (u₀.trans k₀) (u₁.trans k₁) (by
      rw [Category.assoc, n₁'.cart.1.w, ← Category.assoc, hg, Category.assoc, h4', ← Category.assoc _ Yg.oF.t.G.hom aF', u₁,
        hg₁, Category.assoc])
    rw [hn₁, hm', ← Category.assoc, ← Category.assoc, ← A, ← B, Category.assoc, Category.assoc, ← hng, ← hn₁']
  have : Mono Y'.j := by
    have := Y'.jQ_open
    have := hmono
    unfold Model.j; infer_instance
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  refine ⟨χ₁' ≫ f', ⟨W.t, m', W.P, W.φ, W.he, W.w, W.e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu =>
    ⟨(s6 F uF ha hu).1, fun yF hyF n p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩, ?_, hy', fun x => ?_, rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl, fun T g g' g₁ g₂ τ hgg hg hg₁ h k₀ k₁ => ?_⟩
  · have hyF' : yF = Out.jFK (R := PowerSeries k) F ≫ y := by
      rw [← cancel_mono Y'.j, hyF, Category.assoc, hy']
    have base : (x.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK (PowerSeries k))) ≫ W.t.G.hom =
        Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k) := by
      have a₁ : W.P.U.gen.inv.left ≫ pullback.snd W.t.G.hom (Out.jK (PowerSeries k)) = W.P.A.A.hom :=
        Over.w W.P.U.gen.inv
      have a₂ : x.left ≫ W.P.A.A.hom = Out.jFK (R := PowerSeries k) F := Over.w x
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd _ _), a₁,
        ← Category.assoc, a₂]
    have go : ∀ (σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), σY.left ≫ Y.m0.toSABMap.φ = σ.left ≫ Y'.m0.toSABMap.φ →
        x.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK (PowerSeries k)) ≫ W.m.φ =
          yF ≫ σY.left ≫ Y.m.φ := by
      intro σY hσY
      have b₁ : σY.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σY
      have b₂ : σ.left ≫ Y'.oF.t.G.hom = 𝟙 _ := Over.w σ
      have := (tr _ _ (yF ≫ σY.left) (yF ≫ σ.left) _ base (by rw [Category.assoc, b₁, hyF']; exact Category.comp_id _)
        (by rw [Category.assoc, hσY, Category.assoc]) (by rw [Category.assoc, b₁, Category.assoc, b₂])).2
        (by simpa only [Category.assoc] using e4)
      simpa only [Category.assoc] using this
    have hyY : yF ≫ Y.j = Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k) ≫ χ₁ ≫ f := by
      rw [hyF', Category.assoc, hy]
    rcases hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩
    · exact (s6 F uF ha hu).2 yF hyY n p₀ (Y.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Y.m0.etaA v).trans (Y'.m0.etaA v).symm))
    · exact (s6 F uF ha hu).2 yF hyY n p₀ (Y.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Y.m0.eta v).trans (Y'.m0.eta v).symm))
  · rw [Category.assoc, hf', h2']
  · have q₁ := abLocus_pullback hA Y'.t.semi m'.cart.1 x
    have q₂ := abLocus_pullback hA Y.t.semi W.m.cart.1 x
    exact q₁.trans q₂.symm
  · have hgg' : (show T ⟶ W.t.G.left from g') = g := eq_of_heq hgg
    have q := (tr T g g₁ g₂ τ hg hg₁ k₀ k₁).1 h
    rw [← hgg'] at q
    exact q

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

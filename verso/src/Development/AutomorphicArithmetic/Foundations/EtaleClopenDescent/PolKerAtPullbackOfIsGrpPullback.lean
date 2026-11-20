import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace UpperTheory.Cb.PairEqualityCriteria

/- English proof (translation)
Establish `hw : b ≫ (G ⊗ G).hom = a ≫ (G ⊗ G).hom`. Simplify using `only [← Over.w (fst G G), ← Category.assoc, h₁]`. Set `a' : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G` to `Over.homMk a`. Set `b' : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G` to `Over.homMk b hw`. Establish `e : a' = b'`.

Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify `h₁` using `[a', b']`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify `h₂` using `[a', b']`.

Conclude with `congrArg (fun u => u.left) e`.
-/
private theorem eq_of_fst_snd {S : Scheme.{0}} {G : Over S} {Z : Scheme.{0}} {a b : Z ⟶ (G ⊗ G).left}
    (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left) (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := by
  have hw : b ≫ (G ⊗ G).hom = a ≫ (G ⊗ G).hom := by
    simp only [← Over.w (fst G G), ← Category.assoc, h₁]
  let a' : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk a
  let b' : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk b hw
  have e : a' = b' := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      simpa [a', b'] using h₁
    · apply Over.OverMorphism.ext
      simpa [a', b'] using h₂
  exact congrArg (fun u => u.left) e

/- English proof (translation)
Set `e : Over.mk (W.hom ≫ f) ⟶ G` to `Over.homMk ((1 : W ⟶ G').left ≫ φ) (by`. Simplify using `only [Over.mk_hom]`. Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, Over.w])`. Establish `he : e * e = e`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[h.2 W 1 1 e e rfl rfl, _root_.mul_one]`. Both sides reduce to the same expression. Establish `he1 : e = 1` using `mul_eq_left.mp he`. Rewrite using `[← he1]`. Both sides reduce to the same expression.
-/
private theorem one_push {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (W : Over S') :
    (1 : Over.mk (W.hom ≫ f) ⟶ G).left = (1 : W ⟶ G').left ≫ φ := by
  let e : Over.mk (W.hom ≫ f) ⟶ G :=
    Over.homMk ((1 : W ⟶ G').left ≫ φ) (by
      simp only [Over.mk_hom]
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have he : e * e = e := by
    apply Over.OverMorphism.ext
    rw [h.2 W 1 1 e e rfl rfl, _root_.mul_one]
    rfl
  have he1 : e = 1 := mul_eq_left.mp he
  rw [← he1]
  rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, pow_zero]`. Conclude with `one_push h W`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, pow_succ]`. Conclude with `h.2 W _ _ _ _ ih hx`.
-/
private theorem pow_push {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {W : Over S'} (x : W ⟶ G')
    (x₀ : Over.mk (W.hom ≫ f) ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) :
    (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact one_push h W
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 W _ _ _ _ ih hx

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `e`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `h.1.hom_ext` to reduce the goal to its premises. Rewrite using `[← pow_push h x x₀ hx n, e, one_push h W]`.

Rewrite using `[Over.w, Over.w]`. Introduce `e`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[pow_push h x x₀ hx n, e, one_push h W]`.
-/
private theorem pow_one_iff {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {W : Over S'} (x : W ⟶ G')
    (x₀ : Over.mk (W.hom ≫ f) ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) :
    x₀ ^ n = 1 ↔ x ^ n = 1 := by
  constructor
  · intro e
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← pow_push h x x₀ hx n, e, one_push h W]
    · rw [Over.w, Over.w]
  · intro e
    apply Over.OverMorphism.ext
    rw [pow_push h x x₀ hx n, e, one_push h W]

/- English proof (translation)
Establish `lf : ∀ {Z : Scheme.{0}} {P Q Q' : Over Z} (a : P ⟶ Q) (b : P ⟶ Q'), (lift a b).left ≫ (fst Q Q').left = a.left`. Introduce `Z P Q Q' a b`. Rewrite using `[← Over.comp_left, lift_fst]`. Establish `ls : ∀ {Z : Scheme.{0}} {P Q Q' : Over Z} (a : P ⟶ Q) (b : P ⟶ Q'), (lift a b).left ≫ (snd Q Q').left = b.left`. Introduce `Z P Q Q' a b`.

Rewrite using `[← Over.comp_left, lift_snd]`. Establish `lfr : ∀ {Z : Scheme.{0}} {P Q Q' : Over Z} (a : P ⟶ Q) (b : P ⟶ Q') {V : Scheme.{0}} (k : Q.left ⟶ V), (lift a b).left ≫ (fst Q Q').left ≫ k = a.left ≫ k`. Introduce `Z P Q Q' a b V k`. Rewrite using `[← Category.assoc, lf]`. Establish `lsr : ∀ {Z : Scheme.{0}} {P Q Q' : Over Z} (a : P ⟶ Q) (b : P ⟶ Q') {V : Scheme.{0}} (k : Q'.left ⟶ V), (lift a b).left ≫ (snd Q Q').left ≫ k = b.left ≫ k`.

Introduce `Z P Q Q' a b V k`. Rewrite using `[← Category.assoc, ls]`. Choose the witnesses or unpack the hypotheses as in `⟨κ, hκ1, hκ2⟩ : ∃ κ : (B₁ ⊗ T₁).left ⟶ (B ⊗ Over.mk (T₁.hom ≫ t)).left, κ ≫ (fst B (Over.mk (T₁.hom ≫ t))).left = (fst B₁ T₁).left ≫ θ ∧ κ ≫ (snd B (Over.mk (T₁.hom ≫ t))).left = (snd B₁ T₁).left := by`. Set `u : Over.mk ((B₁ ⊗ T₁).hom ≫ t) ⟶ B` to `Over.homMk ((fst B₁ T₁).left ≫ θ) (by`. Simplify using `only [Over.mk_hom]`.

Rewrite using `[Category.assoc, hc.w, ← Category.assoc, Over.w])`. Set `v : Over.mk ((B₁ ⊗ T₁).hom ≫ t) ⟶ Over.mk (T₁.hom ≫ t)` to `Over.homMk (snd B₁ T₁).left (by`. Simplify using `only [Over.mk_hom]`. Rewrite using `[← Category.assoc, Over.w])`. Conclude with `⟨(lift u v).left, lf u v, ls u v⟩`.

Establish `hw : (fst B (Over.mk (T₁.hom ≫ t))).left ≫ B.hom = ((snd B (Over.mk (T₁.hom ≫ t))).left ≫ T₁.hom) ≫ t`. Rewrite using `[Over.w, Category.assoc]`. Conclude with `(Over.w (snd B (Over.mk (T₁.hom ≫ t)))).symm`. Choose the witnesses or unpack the hypotheses as in `⟨lm, hl1, hl2⟩ : ∃ lm : (B ⊗ Over.mk (T₁.hom ≫ t)).left ⟶ (B₁ ⊗ T₁).left, lm ≫ (fst B₁ T₁).left ≫ θ = (fst B (Over.mk (T₁.hom ≫ t))).left ∧ lm ≫ (snd B₁ T₁).left = (snd B (Over.mk (T₁.hom ≫ t))).left := by`. Set `u : Over.mk ((snd B (Over.mk (T₁.hom ≫ t))).left ≫ T₁.hom) ⟶ B₁` to `Over.homMk (hc.lift _ _ hw) (by`.

Simplify using `only [Over.mk_hom]`. Conclude with `hc.lift_snd _ _ hw)`. Set `v : Over.mk ((snd B (Over.mk (T₁.hom ≫ t))).left ≫ T₁.hom) ⟶ T₁` to `Over.homMk (snd B (Over.mk (T₁.hom ≫ t))).left rfl`. Use `⟨(lift u v).left, ?_, ls u v⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, lf u v]`.

Conclude with `hc.lift_fst _ _ hw`. Establish `E1 : (lift (fst B₁ T₁ ≫ ψ₁') (snd B₁ T₁ ≫ x₁ ≫ ψ₁')).left ≫ m.φ₂ = κ ≫ (lift (fst B (Over.mk (T₁.hom ≫ t)) ≫ ψ') (snd B (Over.mk (T₁.hom ≫ t)) ≫ x ≫ ψ')).left`. Apply `eq_of_fst_snd (G := o.A)` to reduce the goal to its premises. Simplify using `only [Category.assoc, m.sq.1, lfr, lf, Over.comp_left, hψ, reassoc_of% hκ1]`. Simplify using `only [Category.assoc, m.sq.2, lsr, ls, Over.comp_left, hx, hψ, reassoc_of% hκ2]`.

Establish `E2 : lm ≫ (lift (fst B₁ T₁ ≫ ψ₁') (snd B₁ T₁ ≫ x₁ ≫ ψ₁')).left ≫ m.φ₂ = (lift (fst B (Over.mk (T₁.hom ≫ t)) ≫ ψ') (snd B (Over.mk (T₁.hom ≫ t)) ≫ x ≫ ψ')).left`. Apply `eq_of_fst_snd (G := o.A)` to reduce the goal to its premises. Simplify using `only [Category.assoc, m.sq.1, lfr, lf, Over.comp_left, ← hψ, reassoc_of% hl1]`. Simplify using `only [Category.assoc, m.sq.2, lsr, ls, Over.comp_left, hx, hψ, reassoc_of% hl2]`. Establish `hL₁ : (o₁.P.pull (lift (fst B₁ T₁ ≫ ψ₁') (snd B₁ T₁ ≫ x₁ ≫ ψ₁')).left).IsLB` using `LB.isLB_linComb o₁.isLB _ _`.

Establish `hL : (o.P.pull (lift (fst B (Over.mk (T₁.hom ≫ t)) ≫ ψ') (snd B (Over.mk (T₁.hom ≫ t)) ≫ x ≫ ψ')).left).IsLB` using `LB.isLB_linComb o.isLB _ _`. Establish `hP' : (o.P.pull m.φ₂).IsLB` using `LB.isLB_linComb o.isLB _ _`. Establish `c₁` using `GlobalTheory.CechPic.cls_pull o₁.isLB _ hL₁`. Rewrite `c₁` using `[(GlobalTheory.CechPic.cls_eq_iff o₁.isLB hP').mpr m.pol, GlobalTheory.CechPic.cls_pull o.isLB _ hP', ← GlobalTheory.CechPic.pull_comp]`. Establish `c` using `GlobalTheory.CechPic.cls_pull o.isLB _ hL`.

Rewrite using `[show PullPolTriv o₁ ψ₁' x₁ ↔ _ from (GlobalTheory.CechPic.cls_eq_zero_iff hL₁).symm, show PullPolTriv o ψ' x ↔ _ from (GlobalTheory.CechPic.cls_eq_zero_iff hL).symm, c₁, c]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Rewrite using `[← E2, GlobalTheory.CechPic.pull_comp, h0, map_zero]`. Introduce `h0`.

Rewrite using `[E1, GlobalTheory.CechPic.pull_comp, h0, map_zero]`.
-/
private theorem triv_iff {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {T Y : Scheme.{0}} {s₁ : T ⟶ Sp R} {s : Y ⟶ Sp R} {t : T ⟶ Y} {o₁ : Obj b N s₁} {o : Obj b N s}
    (m : ObjMap o₁ o t) {B₁ : Over T} {B : Over Y} {θ : B₁.left ⟶ B.left}
    (hc : IsPullback θ B₁.hom B.hom t) {ψ₁' : B₁ ⟶ o₁.A} {ψ' : B ⟶ o.A}
    (hψ : θ ≫ ψ'.left = ψ₁'.left ≫ m.φ) (T₁ : Over T) (x₁ : T₁ ⟶ B₁)
    (x : Over.mk (T₁.hom ≫ t) ⟶ B) (hx : x.left = x₁.left ≫ θ) :
    PullPolTriv o₁ ψ₁' x₁ ↔ PullPolTriv o ψ' x := by
  have lf : ∀ {Z : Scheme.{0}} {P Q Q' : Over Z} (a : P ⟶ Q) (b : P ⟶ Q'),
      (lift a b).left ≫ (fst Q Q').left = a.left := by
    intro Z P Q Q' a b
    rw [← Over.comp_left, lift_fst]
  have ls : ∀ {Z : Scheme.{0}} {P Q Q' : Over Z} (a : P ⟶ Q) (b : P ⟶ Q'),
      (lift a b).left ≫ (snd Q Q').left = b.left := by
    intro Z P Q Q' a b
    rw [← Over.comp_left, lift_snd]
  have lfr : ∀ {Z : Scheme.{0}} {P Q Q' : Over Z} (a : P ⟶ Q) (b : P ⟶ Q') {V : Scheme.{0}} (k : Q.left ⟶ V),
      (lift a b).left ≫ (fst Q Q').left ≫ k = a.left ≫ k := by
    intro Z P Q Q' a b V k
    rw [← Category.assoc, lf]
  have lsr : ∀ {Z : Scheme.{0}} {P Q Q' : Over Z} (a : P ⟶ Q) (b : P ⟶ Q') {V : Scheme.{0}} (k : Q'.left ⟶ V),
      (lift a b).left ≫ (snd Q Q').left ≫ k = b.left ≫ k := by
    intro Z P Q Q' a b V k
    rw [← Category.assoc, ls]
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ : (B₁ ⊗ T₁).left ⟶ (B ⊗ Over.mk (T₁.hom ≫ t)).left,
      κ ≫ (fst B (Over.mk (T₁.hom ≫ t))).left = (fst B₁ T₁).left ≫ θ ∧
      κ ≫ (snd B (Over.mk (T₁.hom ≫ t))).left = (snd B₁ T₁).left := by
    let u : Over.mk ((B₁ ⊗ T₁).hom ≫ t) ⟶ B := Over.homMk ((fst B₁ T₁).left ≫ θ) (by
      simp only [Over.mk_hom]
      rw [Category.assoc, hc.w, ← Category.assoc, Over.w])
    let v : Over.mk ((B₁ ⊗ T₁).hom ≫ t) ⟶ Over.mk (T₁.hom ≫ t) := Over.homMk (snd B₁ T₁).left (by
      simp only [Over.mk_hom]
      rw [← Category.assoc, Over.w])
    exact ⟨(lift u v).left, lf u v, ls u v⟩
  have hw : (fst B (Over.mk (T₁.hom ≫ t))).left ≫ B.hom =
      ((snd B (Over.mk (T₁.hom ≫ t))).left ≫ T₁.hom) ≫ t := by
    rw [Over.w, Category.assoc]
    exact (Over.w (snd B (Over.mk (T₁.hom ≫ t)))).symm
  obtain ⟨lm, hl1, hl2⟩ : ∃ lm : (B ⊗ Over.mk (T₁.hom ≫ t)).left ⟶ (B₁ ⊗ T₁).left,
      lm ≫ (fst B₁ T₁).left ≫ θ = (fst B (Over.mk (T₁.hom ≫ t))).left ∧
      lm ≫ (snd B₁ T₁).left = (snd B (Over.mk (T₁.hom ≫ t))).left := by
    let u : Over.mk ((snd B (Over.mk (T₁.hom ≫ t))).left ≫ T₁.hom) ⟶ B₁ :=
      Over.homMk (hc.lift _ _ hw) (by
        simp only [Over.mk_hom]
        exact hc.lift_snd _ _ hw)
    let v : Over.mk ((snd B (Over.mk (T₁.hom ≫ t))).left ≫ T₁.hom) ⟶ T₁ :=
      Over.homMk (snd B (Over.mk (T₁.hom ≫ t))).left rfl
    refine ⟨(lift u v).left, ?_, ls u v⟩
    rw [← Category.assoc, lf u v]
    exact hc.lift_fst _ _ hw
  have E1 : (lift (fst B₁ T₁ ≫ ψ₁') (snd B₁ T₁ ≫ x₁ ≫ ψ₁')).left ≫ m.φ₂ =
      κ ≫ (lift (fst B (Over.mk (T₁.hom ≫ t)) ≫ ψ') (snd B (Over.mk (T₁.hom ≫ t)) ≫ x ≫ ψ')).left := by
    apply eq_of_fst_snd (G := o.A)
    · simp only [Category.assoc, m.sq.1, lfr, lf, Over.comp_left, hψ, reassoc_of% hκ1]
    · simp only [Category.assoc, m.sq.2, lsr, ls, Over.comp_left, hx, hψ, reassoc_of% hκ2]
  have E2 : lm ≫ (lift (fst B₁ T₁ ≫ ψ₁') (snd B₁ T₁ ≫ x₁ ≫ ψ₁')).left ≫ m.φ₂ =
      (lift (fst B (Over.mk (T₁.hom ≫ t)) ≫ ψ') (snd B (Over.mk (T₁.hom ≫ t)) ≫ x ≫ ψ')).left := by
    apply eq_of_fst_snd (G := o.A)
    · simp only [Category.assoc, m.sq.1, lfr, lf, Over.comp_left, ← hψ, reassoc_of% hl1]
    · simp only [Category.assoc, m.sq.2, lsr, ls, Over.comp_left, hx, hψ, reassoc_of% hl2]
  have hL₁ : (o₁.P.pull (lift (fst B₁ T₁ ≫ ψ₁') (snd B₁ T₁ ≫ x₁ ≫ ψ₁')).left).IsLB :=
    LB.isLB_linComb o₁.isLB _ _
  have hL : (o.P.pull (lift (fst B (Over.mk (T₁.hom ≫ t)) ≫ ψ')
      (snd B (Over.mk (T₁.hom ≫ t)) ≫ x ≫ ψ')).left).IsLB :=
    LB.isLB_linComb o.isLB _ _
  have hP' : (o.P.pull m.φ₂).IsLB := LB.isLB_linComb o.isLB _ _
  have c₁ := GlobalTheory.CechPic.cls_pull o₁.isLB _ hL₁
  rw [(GlobalTheory.CechPic.cls_eq_iff o₁.isLB hP').mpr m.pol, GlobalTheory.CechPic.cls_pull o.isLB _ hP',
    ← GlobalTheory.CechPic.pull_comp] at c₁
  have c := GlobalTheory.CechPic.cls_pull o.isLB _ hL
  rw [show PullPolTriv o₁ ψ₁' x₁ ↔ _ from (GlobalTheory.CechPic.cls_eq_zero_iff hL₁).symm,
    show PullPolTriv o ψ' x ↔ _ from (GlobalTheory.CechPic.cls_eq_zero_iff hL).symm, c₁, c]
  constructor
  · intro h0
    rw [← E2, GlobalTheory.CechPic.pull_comp, h0, map_zero]
  · intro h0
    rw [E1, GlobalTheory.CechPic.pull_comp, h0, map_zero]

end UpperTheory.Cb.PairEqualityCriteria

/- English proof (translation)
Introduce `p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁' ψ' c h hψ`. Prove the components needed by the constructor for the conclusion. Introduce `H T₁ σ hσ x₁ hx₁`. Set `x : Over.mk (T₁.hom ≫ t) ⟶ B` to `Over.homMk (x₁.left ≫ θ) (by`. Simplify using `only [Over.mk_hom]`.

Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, Over.w])`. Establish `hx : x.left = x₁.left ≫ θ` using `rfl`. Establish `key` using `H (Over.mk (T₁.hom ≫ t)) T₁.hom rfl x ((UpperTheory.Cb.PairEqualityCriteria.pow_one_iff h x₁ x hx _).mpr hx₁)`. Rewrite `key` using `[← UpperTheory.Cb.PairEqualityCriteria.triv_iff m h.1 hψ T₁ x₁ x hx, UpperTheory.Cb.PairEqualityCriteria.pow_one_iff h x₁ x hx]`. Conclude with `key`.

Introduce and unpack `H ⟨Tl, ⟨⟨⟩⟩, Th⟩ σ hσ x hx`. Express the relevant statement in the definitionally equal form `Tl ⟶ T at σ`. Use `replace hσ : σ ≫ t = Th := hσ`. Use `revert Th`. Introduce `Th x hx hσ`.

Substitute `hσ` using the available equality. Set `x₁ : Over.mk σ ⟶ B₁` to `Over.homMk (h.1.lift x.left σ (Over.w x)) (h.1.lift_snd _ _ _)`. Establish `hx' : x.left = x₁.left ≫ θ` using `(h.1.lift_fst _ _ _).symm`. Establish `key` using `H (Over.mk σ) σ (Category.comp_id σ) x₁ ((UpperTheory.Cb.PairEqualityCriteria.pow_one_iff h x₁ x hx' _).mp hx)`. Rewrite `key` using `[UpperTheory.Cb.PairEqualityCriteria.triv_iff m h.1 hψ (Over.mk σ) x₁ x hx', ← UpperTheory.Cb.PairEqualityCriteria.pow_one_iff h x₁ x hx']`.

Conclude with `key`.
-/
theorem UpperTheory.Cb.polKerAt_pullback_of_isGrpPullback :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁' : B₁ ⟶ o₁.A) (ψ' : B ⟶ o.A) (c : ℕ), IsGrpPullback B₁ B t θ → θ ≫ ψ'.left = ψ₁'.left ≫ m.φ → (PolKerAt o ψ' c t ↔ PolKerAt o₁ ψ₁' c (𝟙 T)) := by
  intro p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁' ψ' c h hψ
  constructor
  · intro H T₁ σ hσ x₁ hx₁
    let x : Over.mk (T₁.hom ≫ t) ⟶ B := Over.homMk (x₁.left ≫ θ) (by
      simp only [Over.mk_hom]
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    have hx : x.left = x₁.left ≫ θ := rfl
    have key := H (Over.mk (T₁.hom ≫ t)) T₁.hom rfl x
      ((UpperTheory.Cb.PairEqualityCriteria.pow_one_iff h x₁ x hx _).mpr hx₁)
    rw [← UpperTheory.Cb.PairEqualityCriteria.triv_iff m h.1 hψ T₁ x₁ x hx,
      UpperTheory.Cb.PairEqualityCriteria.pow_one_iff h x₁ x hx] at key
    exact key
  · rintro H ⟨Tl, ⟨⟨⟩⟩, Th⟩ σ hσ x hx
    change Tl ⟶ T at σ
    replace hσ : σ ≫ t = Th := hσ
    revert Th
    intro Th x hx hσ
    subst hσ
    let x₁ : Over.mk σ ⟶ B₁ := Over.homMk (h.1.lift x.left σ (Over.w x)) (h.1.lift_snd _ _ _)
    have hx' : x.left = x₁.left ≫ θ := (h.1.lift_fst _ _ _).symm
    have key := H (Over.mk σ) σ (Category.comp_id σ) x₁
      ((UpperTheory.Cb.PairEqualityCriteria.pow_one_iff h x₁ x hx' _).mp hx)
    rw [UpperTheory.Cb.PairEqualityCriteria.triv_iff m h.1 hψ (Over.mk σ) x₁ x hx',
      ← UpperTheory.Cb.PairEqualityCriteria.pow_one_iff h x₁ x hx'] at key
    exact key

import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientPointModuli
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSections

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePointLaw

open GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

/- English proof (translation)
Establish `hL : Out.Laws` using `abelianSchemeLaws_all.1`. Establish `hfacts` using `obj_isAbelianScheme_dim_rigidified_sym`. Take `⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩` from `h₁`. Take `⟨hom₂, lin₂, sur₂, ker₂, weil₂, lev₂⟩` from `h₂`. Take `⟨hab, hdim, -, -⟩` from `hfacts E H D l B b _ s o`.

Take `⟨hab₁, hdim₁, -, -⟩` from `hfacts E H D l B b _ s o₁`. Take `⟨hab₂, hdim₂, -, -⟩` from `hfacts E H D l B b _ s o₂`. Set `P` to `polOf o.t o.proper o.ample o.ktriv hdim`. Set `P₁` to `polOf o₁.t o₁.proper o₁.ample o₁.ktriv hdim₁`. Set `P₂` to `polOf o₂.t o₂.proper o₂.ample o₂.ktriv hdim₂`.

Use `o₁.proper` as an intermediate fact. Use `o₂.proper` as an intermediate fact. Take `⟨α, hα⟩` from `exists_fac hab.smooth ψ₁ ψ₂ fun x hx => (ker₂ x).2 ((ker₁ x).1 hx)`. Establish `homα : IsMonHom α` using `hL.rigidity _ _ _ hab₁ hab₂ α (by`. Rewrite using `[← IsMonHom.one_hom ψ₁, Category.assoc, hα, IsMonHom.one_hom])`.

Establish `: Epi ψ₁.left` using `Flat.epi_of_flat_of_surjective _`. Establish `: Epi ψ₁` using `Over.epi_of_epi_left ψ₁`. Establish `linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a` using `fun a => by`. Rewrite using `[← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]`. Set `ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G)` to `MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁`.

Establish `hlam : LBIso (abelian₂ o₁.t.G (lbPow o₁.t.PP.L 1)) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left))` using `lam_iso_of_weil_pairings hL k P₁ P₂ α p 1 homα hp inferInstance fun n x y c hn hc hx hy h => by`. Establish `lift` using `exists_torsion_lift ρ sur₁ (fun x hx => hC x ((ker₁ x).1 hx)) hn (hc.pow_right 2)`. Take `⟨x₀, tx, ex⟩` from `lift x hx`. Take `⟨y₀, ty, ey⟩` from `lift y hy`. Take `rfl : x₀ ≫ ψ₁ = x` from `ex`.

Take `rfl : y₀ ≫ ψ₁ = y` from `ey`. Take `⟨c₀, hc₀, -⟩` from `(hL.weil _ P n _).1 x₀ y₀ tx ty`. Take `⟨c₀, rfl⟩` from `(unitOn_bijective k).2 c₀`. Establish `e : c = c₀ ^ p ^ 2` using `(unitOn_bijective k).1 (((hL.weil _ P₁ n _).1 _ _ hx hy).unique h (weil₁ n x₀ y₀ c₀ hc hc₀))`. Establish `w` using `weil₂ n x₀ y₀ c₀ hc hc₀`.

Rewrite `w` using `[← hα, ← Category.assoc, ← Category.assoc, ← e]`. Rewrite using `[pow_one]`. Conclude with `w`. Establish `hiso` using `iso_of_lam o₁.t o₂.t α linα hlam`. Use `mono_of_kTriv α o₁.t.PP.isLB o₂.t.PP.isLB hiso o₁.ktriv` as an intermediate fact.

Establish `: IsIso α` using `isIso_of_mono α hab₂.smooth fun y => by`. Take `⟨x, rfl⟩` from `sur₂ y`. Conclude with `⟨x ≫ ψ₁, by rw [Category.assoc, hα]⟩`. Establish `: IsMonHom (asIso α).hom` using `homα`. Take `⟨p₀, hp₀⟩` from `exists_inv_mod hp hpM`.

Use `⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl act := fun a => congrArg (fun q => q.left) (linα a) lin := isPullCubical_of_iso hL.globalFns hab₁ α _ _ hiso eta := fun a => ?_, etaA := fun a => ?_ }, congrArg (fun q => q.left) hα⟩` and prove the remaining obligations. Rewrite using `[Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]`. Both sides reduce to the same expression. Rewrite using `[Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]`. Both sides reduce to the same expression.
-/
theorem exists_objMap_comp {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}
    [IsAlgClosed k] [CharZero k]
    {o o₁ o₂ : Obj D l b s} {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ l.M') {C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)}
    (hC : ∀ x ∈ C, x ^ p ^ 2 = 1) {ψ₁ : o.t.G ⟶ o₁.t.G} {ψ₂ : o.t.G ⟶ o₂.t.G} (h₁ : IsHeckeIsog o o₁ p C ψ₁)
    [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left] (h₂ : IsHeckeIsog o o₂ p C ψ₂) :
    ∃ m : ObjMap o₁ o₂ (𝟙 _), ψ₁.left ≫ m.toSABMap.φ = ψ₂.left := by
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hfacts := obj_isAbelianScheme_dim_rigidified_sym
  obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁
  obtain ⟨hom₂, lin₂, sur₂, ker₂, weil₂, lev₂⟩ := h₂
  obtain ⟨hab, hdim, -, -⟩ := hfacts E H D l B b _ s o
  obtain ⟨hab₁, hdim₁, -, -⟩ := hfacts E H D l B b _ s o₁
  obtain ⟨hab₂, hdim₂, -, -⟩ := hfacts E H D l B b _ s o₂
  let P := polOf o.t o.proper o.ample o.ktriv hdim
  let P₁ := polOf o₁.t o₁.proper o₁.ample o₁.ktriv hdim₁
  let P₂ := polOf o₂.t o₂.proper o₂.ample o₂.ktriv hdim₂
  have := o₁.proper
  have := o₂.proper
  obtain ⟨α, hα⟩ := exists_fac hab.smooth ψ₁ ψ₂ fun x hx => (ker₂ x).2 ((ker₁ x).1 hx)
  have homα : IsMonHom α := hL.rigidity _ _ _ hab₁ hab₂ α (by
    rw [← IsMonHom.one_hom ψ₁, Category.assoc, hα, IsMonHom.one_hom])
  have : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₁ := Over.epi_of_epi_left ψ₁
  have linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a => by
    rw [← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]
  let ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
    MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
  have hlam : LBIso (abelian₂ o₁.t.G (lbPow o₁.t.PP.L 1)) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left)) :=
    lam_iso_of_weil_pairings hL k P₁ P₂ α p 1 homα hp inferInstance fun n x y c hn hc hx hy h => by
      have lift := exists_torsion_lift ρ sur₁ (fun x hx => hC x ((ker₁ x).1 hx)) hn (hc.pow_right 2)
      obtain ⟨x₀, tx, ex⟩ := lift x hx
      obtain ⟨y₀, ty, ey⟩ := lift y hy
      obtain rfl : x₀ ≫ ψ₁ = x := ex
      obtain rfl : y₀ ≫ ψ₁ = y := ey
      obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P n _).1 x₀ y₀ tx ty
      obtain ⟨c₀, rfl⟩ := (unitOn_bijective k).2 c₀
      have e : c = c₀ ^ p ^ 2 := (unitOn_bijective k).1
        (((hL.weil _ P₁ n _).1 _ _ hx hy).unique h (weil₁ n x₀ y₀ c₀ hc hc₀))
      have w := weil₂ n x₀ y₀ c₀ hc hc₀
      rw [← hα, ← Category.assoc, ← Category.assoc, ← e] at w
      rw [pow_one]
      exact w
  have hiso := iso_of_lam o₁.t o₂.t α linα hlam
  have := mono_of_kTriv α o₁.t.PP.isLB o₂.t.PP.isLB hiso o₁.ktriv
  have : IsIso α := isIso_of_mono α hab₂.smooth fun y => by
    obtain ⟨x, rfl⟩ := sur₂ y
    exact ⟨x ≫ ψ₁, by rw [Category.assoc, hα]⟩
  have : IsMonHom (asIso α).hom := homα
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  refine ⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl
            act := fun a => congrArg (fun q => q.left) (linα a)
            lin := isPullCubical_of_iso hL.globalFns hab₁ α _ _ hiso
            eta := fun a => ?_, etaA := fun a => ?_ }, congrArg (fun q => q.left) hα⟩
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]; rfl
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]; rfl

/- English proof (translation)
Take `⟨ρ, hρ⟩` from `exists_ptsEquiv m.cart (𝟙_ (Over (Sp k))) y (Category.id_comp _)`. Establish `key : ∀ (T : Over (Sp k)) (y' : T.left ⟶ X) (_ : T.hom ≫ y = y') (n : ℤ) (x x' : T ⟶ o.t.G) (x₀ x₀' : Over.mk y' ⟶ u.t.G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ m.cm.F → x₀'.left = x'.left ≫ m.cm.F → (Out.WeilIs o.t.G o.t.PP.L n x x' c ↔ Out.WeilIs u.t.G u.t.PP.L n x₀ x₀' c)`. Introduce `T y' e`. Substitute `e` using the available equality. Take `⟨w, hw, -⟩` from `m.lin`.

Conclude with `fun n x x' x₀ x₀' c => weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart ⟨w, hw⟩ T n x x' x₀ x₀' c`. Establish `tu : (toUnit (Over.mk y)).left = y` using `by simp`. Use `⟨ρ, m.cart.1.isoPullback, m.cart.1.isoPullback_hom_fst, m.cart.1.isoPullback_hom_snd, fun x => ?_, fun a x => Over.OverMorphism.ext ?_, fun n x x' c => key _ y (Category.id_comp _) n x x' _ _ _ (hρ x) (hρ x'), fun a => Over.OverMorphism.ext ?_, fun a => Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[fibPt, pullback.lift_fst, hρ, Category.assoc, m.cart.1.isoPullback_hom_fst]`.

Rewrite using `[fibPt, pullback.lift_snd, Category.assoc, m.cart.1.isoPullback_hom_snd]`. Conclude with `(Over.w x).symm`. Rewrite using `[hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]`. Rewrite using `[hρ, Over.comp_left, tu]`. Conclude with `m.eta a`.

Rewrite using `[hρ, Over.comp_left, tu]`. Conclude with `m.etaA a`.
-/
theorem exists_transfer_fst
    {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} (u : Obj D l b sX) {k : Type} [Field k]
    {s : Sp k ⟶ Sp B} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) :
    ∃ (ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) ≃* (Over.mk y ⟶ u.t.G)) (e : o.t.G.left ≅ pullback u.t.G.hom y),
      e.hom ≫ pullback.fst _ _ = m.toSABMap.φ ∧
      e.hom ≫ pullback.snd _ _ = o.t.G.hom ∧ (∀ x, fibPt _ (ρ x) = x.left ≫ e.hom) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (𝟙_ (Over (Sp k))) y (Category.id_comp _)
  have key : ∀ (T : Over (Sp k)) (y' : T.left ⟶ X) (_ : T.hom ≫ y = y') (n : ℤ) (x x' : T ⟶ o.t.G)
      (x₀ x₀' : Over.mk y' ⟶ u.t.G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ m.cm.F → x₀'.left = x'.left ≫ m.cm.F →
      (Out.WeilIs o.t.G o.t.PP.L n x x' c ↔ Out.WeilIs u.t.G u.t.PP.L n x₀ x₀' c) := by
    intro T y' e
    subst e
    obtain ⟨w, hw, -⟩ := m.lin
    exact fun n x x' x₀ x₀' c => weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart
      ⟨w, hw⟩ T n x x' x₀ x₀' c
  have tu : (toUnit (Over.mk y)).left = y := by simp
  refine ⟨ρ, m.cart.1.isoPullback, m.cart.1.isoPullback_hom_fst, m.cart.1.isoPullback_hom_snd, fun x => ?_,
    fun a x => Over.OverMorphism.ext ?_,
    fun n x x' c => key _ y (Category.id_comp _) n x x' _ _ _ (hρ x) (hρ x'), fun a => Over.OverMorphism.ext ?_,
    fun a => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ, Category.assoc, m.cart.1.isoPullback_hom_fst]
    · rw [fibPt, pullback.lift_snd, Category.assoc, m.cart.1.isoPullback_hom_snd]
      exact (Over.w x).symm
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, tu]; exact m.eta a
  · rw [hρ, Over.comp_left, tu]; exact m.etaA a

/- English proof (translation)
Establish `hL : Out.Laws` using `abelianSchemeLaws_all.1`. Establish `hComp` using `ObjMaps.id_comp_cancel`. Take `⟨c₁, c₂, c₃, c₄, c₅, -⟩` from `hC`. Establish `: CharZero k` using `charZero_of_injective_ringHom (Spec.preimage (y ≫ Xo.s)).hom.injective`. Establish `pull : ∀ y' : Sp k ⟶ Xo.X, y' ≫ Xo.s = y ≫ Xo.s → ∃ o : Obj D l (baseKA l) (y ≫ Xo.s), Nonempty (ObjMap o Xo.univ y')` using `fun y' h => obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y' rfl rfl (by rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ`.

Take `⟨o, ⟨m⟩⟩` from `pull y rfl`. Take `⟨ρ, e, -, e₁, e₂, e₃, e₄, e₅, e₆⟩` from `exists_transfer_fst Xo.univ m`. Set `C' : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)` to `C.comap ρ.toMonoidHom`. Establish `mem : ∀ x, x ∈ C' ↔ ρ x ∈ C` using `fun _ => Iff.rfl`. Take `⟨hC', o₁, ψ₁, h₁, hfin, het, hsur⟩` from `exists_isHeckeIsog hL obj_isAbelianScheme_dim_rigidified_sym (exists_tateIso_heckeQuotient SimAlg.sim_group) (exists_heckeQuotient_triple_of_laws hL) (weilIs_along_hom hL.globalFns) LieEtale.lieMult_iff_of_etale o 𝔓 p h𝔓 hco hp hp𝔓 hpM C' (fun x hx a => (mem _).2 (by rw [e₃]; exa …`.

Use `(e₄ ((p : ℤ) ^ 2) x x' 1).2 ((congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) (ρ x) (ρ x')) unitOn_one).mpr (c₄ _ hx _ hx'))` as an intermediate fact. Rewrite using `[Nat.cast_pow]`. Conclude with `(congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) x x') unitOn_one).mp this)`. Use the proof step `((Nat.card_congr (ρ.toEquiv.subtypeEquiv mem)).trans c₅)`. Take `⟨y₁, ⟨hy₁, ⟨m₁⟩⟩, huniq⟩` from `Xo.rep _ (y ≫ Xo.s) inferInstance o₁`.

Take `⟨ρ₁, f, f₀, f₁, f₂, f₃, f₄, f₅, f₆⟩` from `exists_transfer_fst Xo.univ m₁`. Establish `h₁'` using `h₁`. Take `⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩` from `h₁'`. Set `σ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G)` to `MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁`. Set `ψp` to `ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)`.

Establish `hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ ψ₁)` using `fun x => congrArg (fun z => ρ₁ (z ≫ ψ₁)) (ρ.symm_apply_apply x)`. Use `⟨y₁, e.inv ≫ ψ₁.left ≫ f.hom, ψp, ⟨hy₁, ?_, fun x => ?_, fun a x => ?_, fun z => ?_, Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩, inferInstance, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, f₁, Over.w, Iso.inv_comp_eq, e₁]`. Take `⟨x, rfl⟩` from `ρ.surjective x`. Rewrite using `[hψ, e₂, f₂, Category.assoc, Iso.hom_inv_id_assoc, Over.comp_left, Category.assoc]`.

Take `⟨x, rfl⟩` from `ρ.surjective x`. Rewrite using `[← e₃, hψ, hψ, ← f₃, Category.assoc, lin₁, Category.assoc]`. Take `⟨z, rfl⟩` from `ρ₁.surjective z`. Take `⟨x, rfl⟩` from `sur₁ z`. Conclude with `⟨ρ x, hψ x⟩`.

Take `⟨x, rfl⟩` from `ρ.surjective x`. Rewrite using `[MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, ker₁, mem]`. Take `⟨x, rfl⟩` from `ρ.surjective x`. Take `⟨x', rfl⟩` from `ρ.surjective x'`. Rewrite using `[hψ, hψ]`.

Conclude with `(f₄ _ _ _ _).1 (weil₁ n x x' c hn ((e₄ _ _ _ _).2 h))`. Rewrite using `[← e₅, ← e₆, hψ, hψ, (lev₁ p' hp' a).1, (lev₁ p' hp' a).2, f₅, f₆]`. Conclude with `⟨rfl, rfl⟩`. Introduce and unpack `y₂ ψ ψq ⟨hy₂, g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩`. Take `⟨o₂, ⟨m₂⟩⟩` from `pull y₂ hy₂`.

Take `⟨ρ₂, r, r₀, r₁, r₂, r₃, r₄, r₅, r₆⟩` from `exists_transfer_fst Xo.univ m₂`. Set `ψ₂ : o.t.G ⟶ o₂.t.G` to `Over.homMk (e.hom ≫ ψ ≫ r.inv) (by`. Rewrite using `[← r₁, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, g₁, e₁])`. Establish `hψ : ∀ x, ρ₂ (x ≫ ψ₂) = ψq (ρ x)` using `fun x => fibPt_injective _ (by`. Rewrite using `[r₂, ← g₂, e₂]`.

Use `show (x.left ≫ e.hom ≫ ψ ≫ r.inv) ≫ r.hom = _`. Simplify using `only [Category.assoc, Iso.inv_hom_id, Category.comp_id])`. Establish `hab` using `isAbelianScheme_of_proper o.t o.proper`. Establish `hab₂` using `isAbelianScheme_of_proper o₂.t o₂.proper`. Use `o₂.proper` as an intermediate fact.

Establish `one : ∀ (G : Over (Sp k)) [GrpObj G], (1 : 𝟙_ (Over (Sp k)) ⟶ G) = η[G]` using `fun G _ => by`. Rewrite using `[Hom.one_def]`. Simplify using the standard rewrite rules. Establish `h₂ : IsHeckeIsog o o₂ p C' ψ₂`. Use `⟨hL.rigidity _ _ _ hab hab₂ ψ₂ ?_, fun a => hom_ext_pts hab.smooth fun x => ρ₂.injective ?_, fun z => ?_, fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ⟨ρ₂.injective ?_, ρ₂.injective ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← one, ← one]`. Conclude with `ρ₂.injective (by rw [hψ, map_one, map_one, map_one])`. Rewrite using `[← Category.assoc, ← Category.assoc, hψ, r₃, hψ, e₃, g₃]`. Take `⟨x, hx⟩` from `g₄ (ρ₂ z)`. Take `⟨x, rfl⟩` from `ρ.surjective x`.

Conclude with `⟨x, ρ₂.injective ((hψ x).trans hx)⟩`. Rewrite using `[mem, ← g₅, MonoidHom.mem_ker, ← hψ, map_eq_one_iff _ ρ₂.injective]`. Use `(r₄ _ _ _ _).2 ?_` and prove the remaining obligations. Rewrite using `[hψ, hψ]`. Conclude with `g₆ n _ _ c hn ((e₄ _ _ _ _).1 h)`.

Rewrite using `[hψ, e₅, r₅]`. Conclude with `(g₇ p' hp' a).1`. Rewrite using `[hψ, e₆, r₆]`. Conclude with `(g₇ p' hp' a).2`. Take `⟨m', hm'⟩` from `exists_objMap_comp hp hpM hC' h₁ h₂`.

Take `⟨m'', hm''⟩` from `((hComp E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y₂ (𝟙 _) m₂).1 m'`. Establish `hy : 𝟙 _ ≫ y₂ = y₁` using `huniq _ ⟨by rw [Category.id_comp, hy₂], ⟨m''⟩⟩`. Use `⟨(Category.id_comp _).symm.trans hy, ?_⟩` and prove the remaining obligations. Establish `hφ : m''.toSABMap.φ = m₁.toSABMap.φ` using `by clear_value ψp σ`. Substitute `hy` using the available equality.

Conclude with `objMap_unique_of_field hL.serre m'' m₁`. Rewrite using `[Category.assoc, Category.assoc, f₀, ← hφ, hm'', reassoc_of% hm', ← r₀]`. Use `show _ = e.inv ≫ (e.hom ≫ ψ ≫ r.inv) ≫ _`. Simplify using `only [Category.assoc, Iso.inv_hom_id_assoc]`.
-/
theorem exists_etale_isHkIsog (Xo : Moduli D l) {𝔓 : Ideal (𝓞 E)} {p i : ℕ} (h𝔓 : 𝔓.IsMaximal)
    (hco : 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (hp : p.Prime) (hp𝔓 : (p : 𝓞 E) ∈ 𝔓) (hpM : ¬ p ∣ l.M')
    {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (hC : Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C) :
    ∃ (y₁ : Sp k ⟶ Xo.X) (ψ₁ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁)
      (f₁ : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G)),
      IsHkIsog p y y₁ C ψ₁ f₁ ∧ IsFinite ψ₁ ∧ Etale ψ₁ ∧ Surjective ψ₁ ∧
      ∀ y₂ ψ₂ f₂, IsHkIsog p y y₂ C ψ₂ f₂ → y₂ = y₁ ∧ ψ₂ ≫ pullback.fst _ _ = ψ₁ ≫ pullback.fst _ _ := by
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hComp := ObjMaps.id_comp_cancel
  obtain ⟨c₁, c₂, c₃, c₄, c₅, -⟩ := hC
  have : CharZero k := charZero_of_injective_ringHom (Spec.preimage (y ≫ Xo.s)).hom.injective
  have pull : ∀ y' : Sp k ⟶ Xo.X, y' ≫ Xo.s = y ≫ Xo.s →
      ∃ o : Obj D l (baseKA l) (y ≫ Xo.s), Nonempty (ObjMap o Xo.univ y') := fun y' h =>
    obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y' rfl rfl
      (by rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  obtain ⟨o, ⟨m⟩⟩ := pull y rfl
  obtain ⟨ρ, e, -, e₁, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_fst Xo.univ m
  let C' : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G) := C.comap ρ.toMonoidHom
  have mem : ∀ x, x ∈ C' ↔ ρ x ∈ C := fun _ => Iff.rfl
  obtain ⟨hC', o₁, ψ₁, h₁, hfin, het, hsur⟩ := exists_isHeckeIsog hL obj_isAbelianScheme_dim_rigidified_sym
    (exists_tateIso_heckeQuotient SimAlg.sim_group) (exists_heckeQuotient_triple_of_laws hL)
    (weilIs_along_hom hL.globalFns) LieEtale.lieMult_iff_of_etale o 𝔓 p h𝔓 hco hp
    hp𝔓 hpM C' (fun x hx a => (mem _).2 (by rw [e₃]; exact c₁ _ hx a))
    (fun J hJ x hx => c₂ J hJ fun a ha => (e₃ a x).symm.trans (by rw [hx a ha, map_one]))
    (fun x hx a ha => ρ.injective ((e₃ a x).trans ((c₃ hx a ha).trans (map_one ρ).symm)))
    (fun x hx x' hx' => by
      have := (e₄ ((p : ℤ) ^ 2) x x' 1).2
        ((congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) (ρ x) (ρ x')) unitOn_one).mpr (c₄ _ hx _ hx'))
      rw [Nat.cast_pow]
      exact (congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) x x') unitOn_one).mp this)
    ((Nat.card_congr (ρ.toEquiv.subtypeEquiv mem)).trans c₅)
  obtain ⟨y₁, ⟨hy₁, ⟨m₁⟩⟩, huniq⟩ := Xo.rep _ (y ≫ Xo.s) inferInstance o₁
  obtain ⟨ρ₁, f, f₀, f₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_fst Xo.univ m₁
  have h₁' := h₁
  obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁'
  let σ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
    MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
  let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
  have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ ψ₁) := fun x => congrArg (fun z => ρ₁ (z ≫ ψ₁)) (ρ.symm_apply_apply x)
  refine ⟨y₁, e.inv ≫ ψ₁.left ≫ f.hom, ψp, ⟨hy₁, ?_, fun x => ?_, fun a x => ?_, fun z => ?_,
    Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩, inferInstance, inferInstance,
    inferInstance, ?_⟩
  · rw [Category.assoc, Category.assoc, f₁, Over.w, Iso.inv_comp_eq, e₁]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [hψ, e₂, f₂, Category.assoc, Iso.hom_inv_id_assoc, Over.comp_left, Category.assoc]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [← e₃, hψ, hψ, ← f₃, Category.assoc, lin₁, Category.assoc]
  · obtain ⟨z, rfl⟩ := ρ₁.surjective z
    obtain ⟨x, rfl⟩ := sur₁ z
    exact ⟨ρ x, hψ x⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, ker₁, mem]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    obtain ⟨x', rfl⟩ := ρ.surjective x'
    rw [hψ, hψ]
    exact (f₄ _ _ _ _).1 (weil₁ n x x' c hn ((e₄ _ _ _ _).2 h))
  · rw [← e₅, ← e₆, hψ, hψ, (lev₁ p' hp' a).1, (lev₁ p' hp' a).2, f₅, f₆]
    exact ⟨rfl, rfl⟩
  · rintro y₂ ψ ψq ⟨hy₂, g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩
    obtain ⟨o₂, ⟨m₂⟩⟩ := pull y₂ hy₂
    obtain ⟨ρ₂, r, r₀, r₁, r₂, r₃, r₄, r₅, r₆⟩ := exists_transfer_fst Xo.univ m₂
    let ψ₂ : o.t.G ⟶ o₂.t.G := Over.homMk (e.hom ≫ ψ ≫ r.inv) (by
      rw [← r₁, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, g₁, e₁])
    have hψ : ∀ x, ρ₂ (x ≫ ψ₂) = ψq (ρ x) := fun x => fibPt_injective _ (by
      rw [r₂, ← g₂, e₂]
      show (x.left ≫ e.hom ≫ ψ ≫ r.inv) ≫ r.hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have hab := isAbelianScheme_of_proper o.t o.proper
    have hab₂ := isAbelianScheme_of_proper o₂.t o₂.proper
    have := o₂.proper
    have one : ∀ (G : Over (Sp k)) [GrpObj G], (1 : 𝟙_ (Over (Sp k)) ⟶ G) = η[G] := fun G _ => by
      rw [Hom.one_def]; simp
    have h₂ : IsHeckeIsog o o₂ p C' ψ₂ := by
      refine ⟨hL.rigidity _ _ _ hab hab₂ ψ₂ ?_, fun a => hom_ext_pts hab.smooth fun x => ρ₂.injective ?_,
        fun z => ?_, fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ⟨ρ₂.injective ?_, ρ₂.injective ?_⟩⟩
      · rw [← one, ← one]
        exact ρ₂.injective (by rw [hψ, map_one, map_one, map_one])
      · rw [← Category.assoc, ← Category.assoc, hψ, r₃, hψ, e₃, g₃]
      · obtain ⟨x, hx⟩ := g₄ (ρ₂ z)
        obtain ⟨x, rfl⟩ := ρ.surjective x
        exact ⟨x, ρ₂.injective ((hψ x).trans hx)⟩
      · rw [mem, ← g₅, MonoidHom.mem_ker, ← hψ, map_eq_one_iff _ ρ₂.injective]
      · refine (r₄ _ _ _ _).2 ?_
        rw [hψ, hψ]
        exact g₆ n _ _ c hn ((e₄ _ _ _ _).1 h)
      · rw [hψ, e₅, r₅]; exact (g₇ p' hp' a).1
      · rw [hψ, e₆, r₆]; exact (g₇ p' hp' a).2
    obtain ⟨m', hm'⟩ := exists_objMap_comp hp hpM hC' h₁ h₂
    obtain ⟨m'', hm''⟩ := ((hComp E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y₂ (𝟙 _) m₂).1 m'
    have hy : 𝟙 _ ≫ y₂ = y₁ := huniq _ ⟨by rw [Category.id_comp, hy₂], ⟨m''⟩⟩
    refine ⟨(Category.id_comp _).symm.trans hy, ?_⟩
    have hφ : m''.toSABMap.φ = m₁.toSABMap.φ := by
      clear_value ψp σ
      subst hy
      exact objMap_unique_of_field hL.serre m'' m₁
    rw [Category.assoc, Category.assoc, f₀, ← hφ, hm'', reassoc_of% hm', ← r₀]
    show _ = e.inv ≫ (e.hom ≫ ψ ≫ r.inv) ≫ _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/- English proof (translation)
Take `⟨y₀, ψ₀, f₀, h₀, a, b, c, hu⟩` from `exists_etale_isHkIsog Xo h𝔓 hco hp hp𝔓 hpM y C hC`. Take `⟨rfl, -⟩` from `hu _ _ _ h₁`. Establish `key : ∀ ψ₂ f₂, IsHkIsog p y y₁ C ψ₂ f₂ → ψ₂ = ψ₀` using `fun ψ₂ f₂ h₂ => pullback.hom_ext (hu _ _ _ h₂).2 (h₂.2.1.trans h₀.2.1.symm)`. Take `rfl` from `key _ _ h₁`. Conclude with `⟨⟨a, b, c⟩, fun _ _ _ h => (hu _ _ _ h).1, key⟩`.
-/
theorem isHkIsog_etale_unique (Xo : Moduli D l) {𝔓 : Ideal (𝓞 E)} {p i : ℕ} (h𝔓 : 𝔓.IsMaximal)
    (hco : 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (hp : p.Prime) (hp𝔓 : (p : 𝓞 E) ∈ 𝔓) (hpM : ¬ p ∣ l.M')
    {k : Type} [Field k] [IsAlgClosed k] {y y₁ : Sp k ⟶ Xo.X} {C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)}
    (hC : Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C)
    {ψ₁ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁}
    {f₁ : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G)} (h₁ : IsHkIsog p y y₁ C ψ₁ f₁) :
    (IsFinite ψ₁ ∧ Etale ψ₁ ∧ Surjective ψ₁) ∧
      (∀ y₂ ψ₂ f₂, IsHkIsog p y y₂ C ψ₂ f₂ → y₂ = y₁) ∧ ∀ ψ₂ f₂, IsHkIsog p y y₁ C ψ₂ f₂ → ψ₂ = ψ₁ := by
  obtain ⟨y₀, ψ₀, f₀, h₀, a, b, c, hu⟩ := exists_etale_isHkIsog Xo h𝔓 hco hp hp𝔓 hpM y C hC
  obtain ⟨rfl, -⟩ := hu _ _ _ h₁
  have key : ∀ ψ₂ f₂, IsHkIsog p y y₁ C ψ₂ f₂ → ψ₂ = ψ₀ := fun ψ₂ f₂ h₂ =>
    pullback.hom_ext (hu _ _ _ h₂).2 (h₂.2.1.trans h₀.2.1.symm)
  obtain rfl := key _ _ h₁
  exact ⟨⟨a, b, c⟩, fun _ _ _ h => (hu _ _ _ h).1, key⟩

end GlobalTheory.HeckePointLaw

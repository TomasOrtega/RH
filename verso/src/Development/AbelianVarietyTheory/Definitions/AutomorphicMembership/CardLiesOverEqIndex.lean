import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SimilitudesCorrespond
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm (IsOver PullsBack lowerCoeff levelMapF endF relGroup trivAt)

namespace GlobalTheory.ShFam.Pad

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l l₂ : Level H}

def CxPt (Xo : Moduli Dw l) (c : Coeff l) : Type :=
  {y : Sp ℂ ⟶ Xo.XF c // y ≫ pullback.snd _ _ = spMap c.F.val.toRingHom}

def LiesOver (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂}
    (y₂ : CxPt Xo₂ c₂) (y : CxPt Xo c) : Prop :=
  ∃ π : Xo₂.X ⟶ Xo.X, IsOver h Xo Xo₂ π ∧ PullsBack Xo Xo₂ π ∧
    y₂.1 ≫ pullback.fst _ _ ≫ π = y.1 ≫ pullback.fst _ _

open Classical in

def levDeg (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) : ℕ :=
  if k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n then Nat.find k else 1

/- English proof (translation)
Unfold `levDeg`. Use `split_ifs with k`. Conclude with `(Nat.find_spec k).1`. Conclude with `one_pos`.
-/
theorem levDeg_pos (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) :
    0 < levDeg h Xo c Xo₂ c₂ := by
  classical
  unfold levDeg
  split_ifs with k
  · exact (Nat.find_spec k).1
  · exact one_pos

/- English proof (translation)
Establish `hne : Nonempty {x : Sp k ⟶ X // x ≫ π = y}`. Establish `: CompactSpace ↥(pullback π y)` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd π y)`. Take `⟨p, -⟩` from `(pullback.snd π y).surjective (default : PrimeSpectrum k)`. Take `⟨q, -, hq⟩` from `isClosed_univ.exists_closed_singleton (X := ↥(pullback π y)) ⟨p, trivial⟩`. Use `⟨pointOfClosedPoint (pullback.snd π y) q hq ≫ pullback.fst π y, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]`. Establish `hfin : Finite {x : Sp k ⟶ X // x ≫ π = y}`. Establish `hf` using `(pullback.snd π y).finite_preimage_singleton (IsLocalRing.closedPoint k)`. Use `hf.to_subtype` as an intermediate fact. Set `s : {x : Sp k ⟶ X // x ≫ π = y} → (Sp k ⟶ pullback π y)` to `fun x => pullback.lift x.1 (𝟙 _) (x.2.trans (Category.id_comp _).symm)`.

Use `Finite.of_injective (β := (pullback.snd π y) ⁻¹' {IsLocalRing.closedPoint k}) (fun x => ⟨s x (IsLocalRing.closedPoint k), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩) fun a b e => ?_` and prove the remaining obligations. Establish `e' : s a = s b` using `ext_of_apply_closedPoint_eq (pullback.snd π y) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (congrArg Subtype.val e)`. Conclude with `Subtype.ext ((pullback.lift_fst _ _ _).symm.trans ((congrArg (· ≫ pullback.fst π y) e').trans (pullback.lift_fst _ _ _)))`. Conclude with `Nat.card_pos`.
-/
theorem card_lifts_pos {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] [Surjective π]
    (y : Sp k ⟶ Y) : 0 < Nat.card {x : Sp k ⟶ X // x ≫ π = y} := by
  have hne : Nonempty {x : Sp k ⟶ X // x ≫ π = y} := by
    have : CompactSpace ↥(pullback π y) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd π y)
    obtain ⟨p, -⟩ := (pullback.snd π y).surjective (default : PrimeSpectrum k)
    obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback π y)) ⟨p, trivial⟩
    refine ⟨pointOfClosedPoint (pullback.snd π y) q hq ≫ pullback.fst π y, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  have hfin : Finite {x : Sp k ⟶ X // x ≫ π = y} := by
    have hf := (pullback.snd π y).finite_preimage_singleton (IsLocalRing.closedPoint k)
    have := hf.to_subtype
    let s : {x : Sp k ⟶ X // x ≫ π = y} → (Sp k ⟶ pullback π y) := fun x =>
      pullback.lift x.1 (𝟙 _) (x.2.trans (Category.id_comp _).symm)
    refine Finite.of_injective (β := (pullback.snd π y) ⁻¹' {IsLocalRing.closedPoint k})
      (fun x => ⟨s x (IsLocalRing.closedPoint k), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩) fun a b e => ?_
    have e' : s a = s b := ext_of_apply_closedPoint_eq (pullback.snd π y) (pullback.lift_snd _ _ _)
      (pullback.lift_snd _ _ _) (congrArg Subtype.val e)
    exact Subtype.ext ((pullback.lift_fst _ _ _).symm.trans ((congrArg (· ≫ pullback.fst π y) e').trans
      (pullback.lift_fst _ _ _)))
  exact Nat.card_pos

/- English proof (translation)
Take `⟨π, hπ, hpb, huniq, ρ, hρ, hone, hmul, -, hρπ, hcov⟩` from `(GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 l l₂ h Xo Xo₂`. Take `⟨k₁, -, k₃, k₄⟩` from `hcov c₂`. Establish `w : (y.1 ≫ pullback.fst _ _) ≫ Xo.s = spMap c₂.F.val.toRingHom ≫ spMap (IntermediateField.inclusion (lowerCoeff h c₂).le).toRingHom`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.

Set `y' : Sp ℂ ⟶ Xo.XF (lowerCoeff h c₂)` to `pullback.lift _ _ w`. Establish `hf : levelMapF h hπ c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π` using `pullback.lift_fst _ _ _`. Establish `hs` using `GlobalTheory.LevelCompare.levelMapF_snd h hπ c₂`. Set `e : {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ≃ {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'}` to `{ toFun := fun a => ⟨a.1.1, by`. Take `⟨π', a₁, a₂, a₃⟩` from `a.2`.

Take `rfl` from `huniq π' a₁ a₂`. Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hf, a₃]`. Conclude with `(pullback.lift_fst _ _ _).symm`. Rewrite using `[Category.assoc, hs]`.

Conclude with `a.1.2.trans (pullback.lift_snd _ _ _).symm⟩`. Use `invFun := fun x => ⟨⟨x.1, (congrArg (x.1 ≫ ·) hs.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.snd _ _) x.2).trans (pullback.lift_snd _ _ _)))⟩, π, hπ, hpb, by`. Express the relevant statement in the definitionally equal form `x.1 ≫ _ = _`. Rewrite using `[← hf, ← Category.assoc, x.2]`. Conclude with `pullback.lift_fst _ _ _⟩`.

Use `left_inv := fun _ => rfl`. Use `right_inv := fun _ => rfl }`. Establish `hpos` using `card_lifts_pos (levelMapF h hπ c₂) y'`. Rewrite using `[Nat.card_congr e]`. Use `⟨hpos, ?_⟩` and prove the remaining obligations.

Take `⟨⟨x, hx⟩⟩` from `(Nat.card_pos_iff.1 hpos).1`. Establish `hF : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (ρ g).hom` using `fun g => pullback.lift_fst _ _ _`. Establish `hS : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.snd _ _ = pullback.snd _ _` using `fun g => pullback.lift_snd _ _ _`. Establish `hm : ∀ g g', endF (ρ (g * g')).hom (hρ _) c₂ = endF (ρ g).hom (hρ g) c₂ ≫ endF (ρ g').hom (hρ g') c₂` using `fun g g' => pullback.hom_ext (by rw [hF, Category.assoc, hF, ← Category.assoc, hF, hmul, Category.assoc]; rfl) (by rw [hS, Category.assoc, hS, hS])`. Establish `h1 : endF (ρ 1).hom (hρ _) c₂ = 𝟙 _` using `pullback.hom_ext (by rw [hF, hone, Category.id_comp]; exact Category.comp_id _) (by rw [hS, Category.id_comp])`.

Set `f : relGroup Dw l l₂ → {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'}` to `fun g => ⟨x ≫ endF (ρ g).hom (hρ g) c₂, by`. Rewrite using `[← hx, Category.assoc]`. Use `congr 1`. Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hf, ← Category.assoc, hF, Category.assoc, hρπ]`.

Rewrite using `[Category.assoc, hs]`. Conclude with `hS g⟩`. Establish `hsurj : Function.Surjective f` using `fun a => by`. Take `⟨g, hg⟩` from `(k₄ ℂ x).1 a.1 (a.2.trans hx.symm)`. Conclude with `⟨g, Subtype.ext hg⟩`.

Establish `hker : Setoid.ker f = QuotientGroup.rightRel ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂))`. Use extensionality with `g g'`. Rewrite using `[QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, ← (k₄ ℂ x).2, Setoid.ker_def, Subtype.ext_iff, hm]`. Express the relevant statement in the definitionally equal form `x ≫ _ = x ≫ _ ↔ _`. Prove the components needed by the constructor for the conclusion.

Introduce `a`. Rewrite using `[← Category.assoc, ← a, Category.assoc, ← hm, mul_inv_cancel, h1, Category.comp_id]`. Introduce `a`. Use `congrArg (· ≫ endF (ρ g).hom (hρ g) c₂) a` as an intermediate fact. Simplify using `only [Category.assoc] at this`.

Rewrite `this` using `[← hm, inv_mul_cancel, h1, Category.comp_id]`. Conclude with `this.symm`. Rewrite using `[← Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hsurj), hker, Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]`. Both sides reduce to the same expression.
-/
theorem card_liesOver_eq_index (hpq : 1 ≤ Dw.p + Dw.q) (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l}
    (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) (y : CxPt Xo c) :
    0 < Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ∧
      Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂)).index := by
  obtain ⟨π, hπ, hpb, huniq, ρ, hρ, hone, hmul, -, hρπ, hcov⟩ :=
    (GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 l l₂ h Xo Xo₂
  obtain ⟨k₁, -, k₃, k₄⟩ := hcov c₂
  have w : (y.1 ≫ pullback.fst _ _) ≫ Xo.s =
      spMap c₂.F.val.toRingHom ≫ spMap (IntermediateField.inclusion (lowerCoeff h c₂).le).toRingHom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  let y' : Sp ℂ ⟶ Xo.XF (lowerCoeff h c₂) := pullback.lift _ _ w
  have hf : levelMapF h hπ c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π := pullback.lift_fst _ _ _
  have hs := GlobalTheory.LevelCompare.levelMapF_snd h hπ c₂
  let e : {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ≃ {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'} :=
    { toFun := fun a => ⟨a.1.1, by
        obtain ⟨π', a₁, a₂, a₃⟩ := a.2
        obtain rfl := huniq π' a₁ a₂
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, hf, a₃]; exact (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, hs]; exact a.1.2.trans (pullback.lift_snd _ _ _).symm⟩
      invFun := fun x => ⟨⟨x.1, (congrArg (x.1 ≫ ·) hs.symm).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ pullback.snd _ _) x.2).trans (pullback.lift_snd _ _ _)))⟩, π, hπ, hpb, by
        change x.1 ≫ _ = _
        rw [← hf, ← Category.assoc, x.2]; exact pullback.lift_fst _ _ _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hpos := card_lifts_pos (levelMapF h hπ c₂) y'
  rw [Nat.card_congr e]
  refine ⟨hpos, ?_⟩
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  have hF : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (ρ g).hom := fun g =>
    pullback.lift_fst _ _ _
  have hS : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.snd _ _ = pullback.snd _ _ := fun g => pullback.lift_snd _ _ _
  have hm : ∀ g g', endF (ρ (g * g')).hom (hρ _) c₂ = endF (ρ g).hom (hρ g) c₂ ≫ endF (ρ g').hom (hρ g') c₂ :=
    fun g g' => pullback.hom_ext (by rw [hF, Category.assoc, hF, ← Category.assoc, hF, hmul, Category.assoc]; rfl)
      (by rw [hS, Category.assoc, hS, hS])
  have h1 : endF (ρ 1).hom (hρ _) c₂ = 𝟙 _ :=
    pullback.hom_ext (by rw [hF, hone, Category.id_comp]; exact Category.comp_id _) (by rw [hS, Category.id_comp])
  let f : relGroup Dw l l₂ → {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'} := fun g =>
    ⟨x ≫ endF (ρ g).hom (hρ g) c₂, by
      rw [← hx, Category.assoc]
      congr 1
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hf, ← Category.assoc, hF, Category.assoc, hρπ]
      · rw [Category.assoc, hs]; exact hS g⟩
  have hsurj : Function.Surjective f := fun a => by
    obtain ⟨g, hg⟩ := (k₄ ℂ x).1 a.1 (a.2.trans hx.symm)
    exact ⟨g, Subtype.ext hg⟩
  have hker : Setoid.ker f = QuotientGroup.rightRel ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂)) := by
    ext g g'
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, ← (k₄ ℂ x).2, Setoid.ker_def, Subtype.ext_iff, hm]
    change x ≫ _ = x ≫ _ ↔ _
    constructor
    · intro a
      rw [← Category.assoc, ← a, Category.assoc, ← hm, mul_inv_cancel, h1, Category.comp_id]
    · intro a
      have := congrArg (· ≫ endF (ρ g).hom (hρ g) c₂) a
      simp only [Category.assoc] at this
      rw [← hm, inv_mul_cancel, h1, Category.comp_id] at this
      exact this.symm
  rw [← Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hsurj), hker,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]
  rfl

/- English proof (translation)
Establish `k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n` using `⟨_, (card_liesOver_eq_index hpq h Xo₂ c₂ y).1, fun y' => (card_liesOver_eq_index hpq h Xo₂ c₂ y').2.trans (card_liesOver_eq_index hpq h Xo₂ c₂ y).2.symm⟩`. Rewrite using `[levDeg, dif_pos k]`. Conclude with `(Nat.find_spec k).2 y`.
-/
theorem card_liesOver (hpq : 1 ≤ Dw.p + Dw.q) (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l}
    (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) (y : CxPt Xo c) :
    Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = levDeg h Xo c Xo₂ c₂ := by
  classical
  have k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n :=
    ⟨_, (card_liesOver_eq_index hpq h Xo₂ c₂ y).1, fun y' =>
      (card_liesOver_eq_index hpq h Xo₂ c₂ y').2.trans (card_liesOver_eq_index hpq h Xo₂ c₂ y).2.symm⟩
  rw [levDeg, dif_pos k]
  exact (Nat.find_spec k).2 y

end GlobalTheory.ShFam.Pad

import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ToricData

variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ) (F : Type) [Field F] [Algebra (FractionRing K) F]

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => MonoidHom.ext fun χ => h χ.toAdd, fun h _ => h ▸ rfl⟩`.
-/
theorem hom_eq_iff {F : Type} [Field F] {t t' : Multiplicative X →* Fˣ} :
    (∀ χ : X, t (Multiplicative.ofAdd χ) = t' (Multiplicative.ofAdd χ)) ↔ t = t' :=
  ⟨fun h => MonoidHom.ext fun χ => h χ.toAdd, fun h _ => h ▸ rfl⟩

/- English proof (translation)
The claim follows from `(and_iff_right rfl).trans ((forall_congr' fun (χ : X) => (corr_iff_eq (pt_isConst q F t χ) ((isConst_oneGen _).of_eq unitOn_one.symm)).trans unitOn_inj).trans (hom_eq_iff (t' := 1)))`.
-/
theorem isZero_pt (t) : (pt q F t).IsZero ↔ t = 1 :=
  (and_iff_right rfl).trans ((forall_congr' fun (χ : X) =>
    (corr_iff_eq (pt_isConst q F t χ) ((isConst_oneGen _).of_eq unitOn_one.symm)).trans unitOn_inj).trans
    (hom_eq_iff (t' := 1)))

/- English proof (translation)
The claim follows from `(and_iff_right (toUnit_unique _ _)).trans ((forall_congr' fun (χ : X) => (corr_iff_eq ((isConst_mulGen (pt_isConst q F t'' χ) (cubAt_isConst q F _ _ _)).of_eq (_root_.mul_one _)) ((isConst_mulGen (pt_isConst q F t χ) (pt_isConst q F t' χ)).of_eq (unitOn_mul _ _).symm)).trans unit …`.
-/
theorem isAdd_pt (t t' t'') : (pt q F t).IsAdd (pt q F t') (pt q F t'') ↔ t'' = t * t' :=
  (and_iff_right (toUnit_unique _ _)).trans ((forall_congr' fun (χ : X) =>
    (corr_iff_eq
      ((isConst_mulGen (pt_isConst q F t'' χ) (cubAt_isConst q F _ _ _)).of_eq (_root_.mul_one _))
      ((isConst_mulGen (pt_isConst q F t χ) (pt_isConst q F t' χ)).of_eq (unitOn_mul _ _).symm)).trans
      unitOn_inj).trans (hom_eq_iff (t' := t * t')))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨gs, h0, hs, hl⟩ choose u hu using fun i => (pt_bijective q F).2 (gs i)`. Establish `key : ∀ i : Fin (n + 1), u i = t ^ (i : ℕ)`. Introduce `i`. Proceed by induction on `i using Fin.induction with`.

Consider the case `zero`. Rewrite `h0` using `[← hu]`. Conclude with `((isZero_pt q F _).1 h0).trans (pow_zero t).symm`. Consider the case `succ i ih`. Establish `h` using `hs i`.

Rewrite `h` using `[← hu, ← hu, isAdd_pt]`. Rewrite using `[h, ih, Fin.val_succ, pow_succ]`. Both sides reduce to the same expression. Rewrite `hl` using `[← hu]`. Conclude with `((pt_bijective q F).1 hl).symm.trans (key _)`.

Introduce and unpack `rfl`. Conclude with `⟨fun i => pt q F (t ^ (i : ℕ)), (isZero_pt q F _).2 (pow_zero t), fun i => (isAdd_pt q F _ _ _).2 (pow_succ t i), rfl⟩`.
-/
theorem isNsmul_pt (n : ℕ) (t t') : GtPtF.IsNsmul n (pt q F t) (pt q F t') ↔ t' = t ^ n := by
  constructor
  · rintro ⟨gs, h0, hs, hl⟩
    choose u hu using fun i => (pt_bijective q F).2 (gs i)
    have key : ∀ i : Fin (n + 1), u i = t ^ (i : ℕ) := by
      intro i
      induction i using Fin.induction with
      | zero =>
        rw [← hu] at h0
        exact ((isZero_pt q F _).1 h0).trans (pow_zero t).symm
      | succ i ih =>
        have h := hs i
        rw [← hu, ← hu, isAdd_pt] at h
        rw [h, ih, Fin.val_succ, pow_succ]
        rfl
    rw [← hu] at hl
    exact ((pt_bijective q F).1 hl).symm.trans (key _)
  · rintro rfl
    exact ⟨fun i => pt q F (t ^ (i : ℕ)), (isZero_pt q F _).2 (pow_zero t),
      fun i => (isAdd_pt q F _ _ _).2 (pow_succ t i), rfl⟩

/- English proof (translation)
The claim follows from `(and_iff_right (toUnit_unique _ _)).trans (forall_congr' fun (χ : X) => (corr_iff_eq (pt_isConst q F t χ) ((isConst_pullGen (tau_isConst q y χ) (jFK (R := K) F)).of_eq (pullTop_unitOn _ _))).trans (unitOn_inj.trans Units.ext_iff))`.
-/
theorem isIota_pt (y : X) (t) : GtPtF.IsIota (D := toricPre K X q) y (pt q F t) ↔
    ∀ χ, (t (Multiplicative.ofAdd χ) : F) = algebraMap (FractionRing K) F (polar q y χ) :=
  (and_iff_right (toUnit_unique _ _)).trans (forall_congr' fun (χ : X) =>
    (corr_iff_eq (pt_isConst q F t χ)
      ((isConst_pullGen (tau_isConst q y χ) (jFK (R := K) F)).of_eq (pullTop_unitOn _ _))).trans
      (unitOn_inj.trans Units.ext_iff))

/- English proof (translation)
Use `(and_iff_right (toUnit_unique _ _)).trans ⟨fun H χ => ?_, fun H u _ hu (χ : X) => ?_⟩` and prove the remaining obligations. Establish `hc` using `H (cg _ _ 1) (cg_isGen _ _ 1) (corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _)) χ`. Establish `e` using `eq_of_corr (isConst_mulGen (pt_isConst q F t (star a • χ)) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))) (pt_isConst q F t' χ) hc`. Conclude with `(unitOn_inj.1 ((_root_.mul_one _).symm.trans e)).symm`. Conclude with `corr_of_isConst ((isConst_mulGen (pt_isConst q F t (star a • χ)) ((isConst_pullGen (isConst_one_of_zero2 q u hu) _).of_eq (map_one _))).of_eq ((_root_.mul_one _).trans (congrArg unitOn (H χ).symm))) (pt_isConst q F t' χ)`.
-/
theorem gtAct_pt (O : Type) [CommRing O] [StarRing O] [Module O X] (h) (a : O) (t t') :
    GtAct (toricOAct q O h) a (pt q F t) (pt q F t') ↔
      ∀ χ : X, t' (Multiplicative.ofAdd χ) = t (Multiplicative.ofAdd (star a • χ)) := by
  refine (and_iff_right (toUnit_unique _ _)).trans ⟨fun H χ => ?_, fun H u _ hu (χ : X) => ?_⟩
  · have hc := H (cg _ _ 1) (cg_isGen _ _ 1)
      (corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _)) χ
    have e := eq_of_corr
      (isConst_mulGen (pt_isConst q F t (star a • χ)) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)))
      (pt_isConst q F t' χ) hc
    exact (unitOn_inj.1 ((_root_.mul_one _).symm.trans e)).symm
  · exact corr_of_isConst
      ((isConst_mulGen (pt_isConst q F t (star a • χ))
        ((isConst_pullGen (isConst_one_of_zero2 q u hu) _).of_eq (map_one _))).of_eq
        ((_root_.mul_one _).trans (congrArg unitOn (H χ).symm)))
      (pt_isConst q F t' χ)

/- English proof (translation)
Establish `w : spMap f ≫ (TF (R` using `K) F).hom = (TF (R := K) F').hom := by`. Express the relevant statement in the definitionally equal form `spMap f ≫ jFK (R := K) F ≫ jK K = jFK (R := K) F' ≫ jK K`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]`. Set `φ : TF (R` to `K) F' ⟶ TF (R := K) F := Over.homMk (spMap f) w`. Establish `e : DegPre.zeroF (toricPre K X q) F' = φ ≫ DegPre.zeroF (toricPre K X q) F` using `toUnit_unique _ _`.

Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem zeroF_left_ext {F' : Type} [Field F'] [Algebra (FractionRing K) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing K) F) = algebraMap (FractionRing K) F') :
    (DegPre.zeroF (toricPre K X q) F').left = spMap f ≫ (DegPre.zeroF (toricPre K X q) F).left := by
  have w : spMap f ≫ (TF (R := K) F).hom = (TF (R := K) F').hom := by
    change spMap f ≫ jFK (R := K) F ≫ jK K = jFK (R := K) F' ≫ jK K
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
  let φ : TF (R := K) F' ⟶ TF (R := K) F := Over.homMk (spMap f) w
  have e : DegPre.zeroF (toricPre K X q) F' = φ ≫ DegPre.zeroF (toricPre K X q) F := toUnit_unique _ _
  rw [e]
  rfl

/- English proof (translation)
Take `⟨y, g, e⟩` from `p`. Take `⟨y', g', e'⟩` from `p'`. Simplify using `only at hp hp'`. Substitute `hp hp'` using the available equality. Use `and_congr_right' ((and_iff_right (zeroF_left_ext q F f hf)).trans ?_)` and prove the remaining obligations.

Use `(forall_congr' fun (χ : X) => (corr_iff_eq (pt_isConst q F' t' χ) ((isConst_pullGen (pt_isConst q F t χ) (spMap f)).of_eq (pullTop_unitOn _ _))).trans (unitOn_inj.trans Units.ext_iff)).trans ?_` and prove the remaining obligations. Conclude with `⟨fun H χ => H χ.toAdd, fun H χ => H _⟩`.
-/
theorem qkExt_pt {F' : Type} [Field F'] [Algebra (FractionRing K) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing K) F) = algebraMap (FractionRing K) F') {n : ℕ}
    (p : QkPt (toricPre K X q) F n) (p' : QkPt (toricPre K X q) F' n) (t t') (hp : p.g = pt q F t)
    (hp' : p'.g = pt q F' t') :
    QkExt f p p' ↔ p'.y = p.y ∧ ∀ χ, (t' χ : F') = f (t χ) := by
  obtain ⟨y, g, e⟩ := p
  obtain ⟨y', g', e'⟩ := p'
  dsimp only at hp hp'
  subst hp hp'
  refine and_congr_right' ((and_iff_right (zeroF_left_ext q F f hf)).trans ?_)
  refine (forall_congr' fun (χ : X) => (corr_iff_eq (pt_isConst q F' t' χ)
      ((isConst_pullGen (pt_isConst q F t χ) (spMap f)).of_eq (pullTop_unitOn _ _))).trans
      (unitOn_inj.trans Units.ext_iff)).trans ?_
  exact ⟨fun H χ => H χ.toAdd, fun H χ => H _⟩

end GlobalTheory.ToricData

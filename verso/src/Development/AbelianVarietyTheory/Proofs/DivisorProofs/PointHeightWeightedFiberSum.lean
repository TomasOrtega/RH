import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.WeightHt

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

/- English proof (translation)
Establish `hx : IsClosed ({V.π w} : Set Y.X)`. Use `V.π.isClosedMap _ hw` as an intermediate fact. Rewrite `this` using `[Set.image_singleton]`. Then use the resulting hypothesis. Take `⟨_, _⟩` from `ExtConj.pts Y _ hx`. Establish `hN : (Nat.card {y : AlgPt Y // below y.1 = V.π w} : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`.

Establish `hF : (Module.finrank ℚ F : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Establish `hd : (V.π.residueDegree w : ℝ) ≠ 0`. Use `letI := (V.π.residueFieldMap w).hom.toAlgebra`. Use `haveI : Module.Finite (Y.X.residueField (V.π w)) (V.G.residueField w) := residueFieldMap_finite_of_locallyQuasiFinite V.π _`. Conclude with `Nat.cast_ne_zero.2 (Module.finrank_pos (R := Y.X.residueField (V.π w)) (M := V.G.residueField w)).ne'`.

Rewrite using `[CoverHt.card_emb V w hw]`. Conclude with `mul_ne_zero hF (mul_ne_zero hd hN)`.
-/
theorem card_ne_zero (w : V.G) (hw : IsClosed ({w} : Set V.G)) :
    (Nat.card (V.X.residueField (V.j w) →+* ℂ) : ℝ) ≠ 0 := by
  have hx : IsClosed ({V.π w} : Set Y.X) := by
    have := V.π.isClosedMap _ hw
    rwa [Set.image_singleton] at this
  obtain ⟨_, _⟩ := ExtConj.pts Y _ hx
  have hN : (Nat.card {y : AlgPt Y // below y.1 = V.π w} : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hd : (V.π.residueDegree w : ℝ) ≠ 0 := by
    letI := (V.π.residueFieldMap w).hom.toAlgebra
    haveI : Module.Finite (Y.X.residueField (V.π w)) (V.G.residueField w) :=
      residueFieldMap_finite_of_locallyQuasiFinite V.π _
    exact Nat.cast_ne_zero.2 (Module.finrank_pos (R := Y.X.residueField (V.π w)) (M := V.G.residueField w)).ne'
  rw [CoverHt.card_emb V w hw]
  exact mul_ne_zero hF (mul_ne_zero hd hN)

/- English proof (translation)
Take `⟨Z, i, _, _, hi⟩` from `exists_isClosedImmersion_genericPoint (V.j w)`. Use `V.ar.isNoetherian_sub i` as an intermediate fact. Take `⟨hc', hd⟩` from `CoverHt.isAlgPt V w hw`. Establish `hri : Set.range i = closure {V.j w}`. Establish `h₁` using `(genericPoint_spec Z).image i.continuous`.

Rewrite `h₁` using `[Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi]`. Conclude with `h₁.def.symm`. Rewrite `hd` using `[topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hri]`. Rewrite `hc'` using `[← hi]`. Establish `hc'' : CharZero (Z.residueField (genericPoint Z))` using `charZero_of_injective_ringHom (i.residueFieldMap (genericPoint Z)).hom.injective`.

Establish `hcΓ : CharZero Γ(Z, ⊤)` using `(Z.Γevaluation (genericPoint Z)).hom.charZero`. Establish `hZ : IsArithVar (i ≫ V.p) 0` using `V.ar.of_isClosedImmersion i hcΓ hd`. Establish `hr : IsRatSec ((fnB u hu hc).restr i).B fun _ => 1` using `fun a b h => by`. Establish `hL` using `((fnB u hu hc).restr i).isLB`. Take `rfl : a = b` from `Subsingleton.elim (α := PUnit → PUnit) _ _`.

Use `congrArg (fun u : Γ(Z, _)ˣ => fnOf _ h.1 u.val) (hL.g_self a)` as an intermediate fact. Rewrite `this` using `[Units.val_one, map_one]`. Conclude with `(this.symm.trans (fnOf_resG _ h.1 _)).trans (mul_one _).symm`. Establish `hdeg` using `H.point Z i hcΓ hd _ hr`. Establish `h₁ (z : Z) : (((fnB u hu hc).restr i).div hr).mult z = 0`.

Take `⟨c, hc⟩` from `exists_chart ((fnB u hu hc).restr i).isLB z`. Conclude with `((presents_divOfRatSec _ hr).isEqn c z hc).mult_eq.trans (unitAt_one z).ord_eq_zero`. Establish `hgen (y : Sp ℂ ⟶ Z) : below y = genericPoint Z` using `SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero`. Establish `h₂ (σ : 𝓞 F →+* ℂ) (y : CxPts (i ≫ V.p) σ) : logNorm (((fnB u hu hc).restr i).φ σ) (fun _ => 1) y = -(1 / 2) * u σ (Points.PtsOver.map i rfl _ y)`. Establish `e` using `ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1`.

Rewrite `e` using `[map_one, CxPts.ev_one CxPts.mem_ptsIn_top]`. Establish `e₄` using `((fnB u hu hc).φ σ).pull_φ i rfl (CxPts.pick (((fnB u hu hc).restr i).φ σ).isLB y) y`. Rewrite using `[logNorm, Units.val_one, e, norm_one, Real.log_one]`. Use `(congrArg (fun b => 0 - b / 2) e₄).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `0 - u σ _ / 2 = _`.

Expand and normalize the polynomial expressions, which then agree. Establish `h₃ (σ : 𝓞 F →+* ℂ) : ∑ᶠ y : CxPts (i ≫ V.p) σ, logNorm (((fnB u hu hc).restr i).φ σ) (fun _ => 1) y = -(1 / 2) * ∑ᶠ y ∈ {y : CxPts V.p σ | y.1 (IsLocalRing.closedPoint ℂ) = V.j w}, u σ y`. Rewrite using `[finsum_congr (h₂ σ), ← mul_finsum, ← finsum_subtype_eq_finsum_cond]`. Use `congr 1`. Use `finsum_eq_of_bijective (fun y => ⟨Points.PtsOver.map i rfl _ y, (Scheme.Hom.comp_apply _ _ _).trans ((congrArg i (hgen y.1)).trans hi)⟩) ⟨fun a b hab => ?_, ?_⟩ fun _ => rfl` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← cancel_mono i]`. Conclude with `congrArg (fun t => t.1.1) hab`. Introduce and unpack `⟨⟨y, hy⟩, hyx⟩`. Take `⟨y', hy'⟩` from `ClosurePts.lift_closed i (genericPoint Z) y (hyx.trans hi.symm)`.

Conclude with `⟨⟨y', by rw [← Category.assoc, hy']; exact hy⟩, Subtype.ext (Subtype.ext hy')⟩`. Unfold `HermLB.curveDeg at hdeg`. Rewrite `hdeg` using `[finsum_congr h₃, ← mul_finsum, hi]`. Simplify using `only [h₁, Int.cast_zero, zero_mul, finsum_zero] at hdeg`. Rewrite using `[hdeg]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem height_eq {u : ∀ σ : 𝓞 F →+* ℂ, CxPts V.p σ → ℝ} {hu : ∀ σ y, CxPts.CInfAt (u σ) y}
    {hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))} {w : V.G}
    (hw : IsClosed ({w} : Set V.G)) {h : V.X → ℝ} (H : (fnB u hu hc).IsArithHeight h) :
    h (V.j w) = (∑ᶠ σ, ∑ᶠ y ∈ {y : CxPts V.p σ | y.1 (IsLocalRing.closedPoint ℂ) = V.j w}, u σ y) / 2 := by
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (V.j w)
  have := V.ar.isNoetherian_sub i
  obtain ⟨hc', hd⟩ := CoverHt.isAlgPt V w hw
  have hri : Set.range i = closure {V.j w} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hri] at hd
  rw [← hi] at hc'
  have hc'' : CharZero (Z.residueField (genericPoint Z)) :=
    charZero_of_injective_ringHom (i.residueFieldMap (genericPoint Z)).hom.injective
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ V.p) 0 := V.ar.of_isClosedImmersion i hcΓ hd
  have hr : IsRatSec ((fnB u hu hc).restr i).B fun _ => 1 := fun a b h => by
    have hL := ((fnB u hu hc).restr i).isLB
    obtain rfl : a = b := Subsingleton.elim (α := PUnit → PUnit) _ _
    have := congrArg (fun u : Γ(Z, _)ˣ => fnOf _ h.1 u.val) (hL.g_self a)
    rw [Units.val_one, map_one] at this
    exact (this.symm.trans (fnOf_resG _ h.1 _)).trans (mul_one _).symm
  have hdeg := H.point Z i hcΓ hd _ hr
  have h₁ (z : Z) : (((fnB u hu hc).restr i).div hr).mult z = 0 := by
    obtain ⟨c, hc⟩ := exists_chart ((fnB u hu hc).restr i).isLB z
    exact ((presents_divOfRatSec _ hr).isEqn c z hc).mult_eq.trans (unitAt_one z).ord_eq_zero
  have hgen (y : Sp ℂ ⟶ Z) : below y = genericPoint Z :=
    SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero
  have h₂ (σ : 𝓞 F →+* ℂ) (y : CxPts (i ≫ V.p) σ) :
      logNorm (((fnB u hu hc).restr i).φ σ) (fun _ => 1) y = -(1 / 2) * u σ (Points.PtsOver.map i rfl _ y) := by
    have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
    rw [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e
    have e₄ := ((fnB u hu hc).φ σ).pull_φ i rfl (CxPts.pick (((fnB u hu hc).restr i).φ σ).isLB y) y
    rw [logNorm, Units.val_one, e, norm_one, Real.log_one]
    refine (congrArg (fun b => 0 - b / 2) e₄).trans ?_
    change 0 - u σ _ / 2 = _
    ring
  have h₃ (σ : 𝓞 F →+* ℂ) : ∑ᶠ y : CxPts (i ≫ V.p) σ, logNorm (((fnB u hu hc).restr i).φ σ) (fun _ => 1) y =
      -(1 / 2) * ∑ᶠ y ∈ {y : CxPts V.p σ | y.1 (IsLocalRing.closedPoint ℂ) = V.j w}, u σ y := by
    rw [finsum_congr (h₂ σ), ← mul_finsum, ← finsum_subtype_eq_finsum_cond]
    congr 1
    refine finsum_eq_of_bijective (fun y => ⟨Points.PtsOver.map i rfl _ y,
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg i (hgen y.1)).trans hi)⟩) ⟨fun a b hab => ?_, ?_⟩ fun _ => rfl
    · apply Subtype.ext
      rw [← cancel_mono i]
      exact congrArg (fun t => t.1.1) hab
    · rintro ⟨⟨y, hy⟩, hyx⟩
      obtain ⟨y', hy'⟩ := ClosurePts.lift_closed i (genericPoint Z) y (hyx.trans hi.symm)
      exact ⟨⟨y', by rw [← Category.assoc, hy']; exact hy⟩, Subtype.ext (Subtype.ext hy')⟩
  unfold HermLB.curveDeg at hdeg
  rw [finsum_congr h₃, ← mul_finsum, hi] at hdeg
  simp only [h₁, Int.cast_zero, zero_mul, finsum_zero] at hdeg
  rw [hdeg]
  ring

/- English proof (translation)
Introduce `F _ _ Y V u hu hc w hw HE`. Take `⟨h, H⟩` from `(HE _ V.X V.p _ V.ar).1 (fnB u hu hc)`. Use `⟨h, H, ?_⟩` and prove the remaining obligations. Use `card_ne_zero V w hw` as an intermediate fact. Rewrite using `[height_eq V hw H]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y)
    (u : ∀ σ : 𝓞 F →+* ℂ, GlobalTheory.CxPts V.p σ → ℝ) (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt (u σ) y)
    (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun (u σ)).IsConj (GlobalTheory.Weight.ofFun (u σ'))) (w : V.G), IsClosed ({w} : Set V.G) →
    GlobalTheory.Published.ArExists →
    IsPtHt (fnB u hu hc) (V.j w)
      ((∑ᶠ σ, ∑ᶠ y ∈ {y : GlobalTheory.CxPts V.p σ | y.1 (IsLocalRing.closedPoint ℂ) = V.j w}, u σ y) /
        (2 * (Nat.card (V.X.residueField (V.j w) →+* ℂ) : ℝ))) := by
  intro F _ _ Y V u hu hc w hw HE
  obtain ⟨h, H⟩ := (HE _ V.X V.p _ V.ar).1 (fnB u hu hc)
  refine ⟨h, H, ?_⟩
  have := card_ne_zero V w hw
  rw [height_eq V hw H]
  field_simp

end GlobalTheory.Mean4O.WeightHt

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagZ GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlagQ.Lifts

variable {ι : Type} [Fintype ι] {N : ℕ}

def trGL {K : Type} [Field K] (B : Mat (fun _ : ι => N) K) (hB : ∀ τ, (B τ).det ≠ 0) (τ : ι) : GL (Fin N) K :=
  Matrix.GeneralLinearGroup.mk'' (B τ).transpose (by rw [Matrix.det_transpose]; exact Ne.isUnit (hB τ))

/- English proof (translation)
Establish `e (τ : ι) : ((G τ)⁻¹ * H τ).1 = ((C * B⁻¹) τ).transpose`. Rewrite using `[Units.val_mul, Matrix.coe_units_inv, hG, hH, Pi.mul_apply, Pi.inv_apply, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]`. Rewrite using `[flagPt_eq_iff_below]`. Prove the components needed by the constructor for the conclusion. Introduce `h τ`.

Use `⟨fun _ _ => trivial, ?_, trivial, fun i j _ hij => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.det_transpose, ← e]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 ((G τ)⁻¹ * H τ).isUnit).ne_zero`. Use `h τ j i ⟨(τ, i.succ), rfl, Nat.lt_succ_self _, hij⟩` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Introduce and unpack `h _ i j ⟨k, rfl, h₁, h₂⟩`. Rewrite using `[e]`. Conclude with `(h k.1).2.2.2 j i j.2 (h₁.trans_le h₂)`.
-/
theorem flagPt_eq_iff_par {K : Type} [Field K] (G H : ι → GL (Fin N) K) (B C : Mat (fun _ : ι => N) K)
    (hG : ∀ τ, (G τ).1 = (B τ).transpose) (hH : ∀ τ, (H τ).1 = (C τ).transpose) :
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G = flagPt Prod.fst Prod.snd H ↔
      Par (fun _ => N) ⊤ (C * B⁻¹) := by
  have e (τ : ι) : ((G τ)⁻¹ * H τ).1 = ((C * B⁻¹) τ).transpose := by
    rw [Units.val_mul, Matrix.coe_units_inv, hG, hH, Pi.mul_apply, Pi.inv_apply, Matrix.transpose_mul,
      Matrix.transpose_nonsing_inv]
  rw [flagPt_eq_iff_below]
  constructor
  · intro h τ
    refine ⟨fun _ _ => trivial, ?_, trivial, fun i j _ hij => ?_⟩
    · rw [← Matrix.det_transpose, ← e]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 ((G τ)⁻¹ * H τ).isUnit).ne_zero
    · have := h τ j i ⟨(τ, i.succ), rfl, Nat.lt_succ_self _, hij⟩
      rwa [e] at this
  · rintro h _ i j ⟨k, rfl, h₁, h₂⟩
    rw [e]
    exact (h k.1).2.2.2 j i j.2 (h₁.trans_le h₂)

variable {Y : Var ℚ}

/- English proof (translation)
The claim follows from `Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)`.
-/
theorem spMap_algebraMap_fromSpecStalk (y : Y.X) :
    spMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) ≫ Y.X.fromSpecStalk y = (ratOf Y).pt :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

/- English proof (translation)
Establish `hp` using `spMap_stalkClosedPointTo p`. Generalize the expression as in `(Scheme.stalkClosedPointTo (R := .of K) p).hom = ψ at hp`. Generalize the expression as in `p (IsLocalRing.closedPoint K) = y at hA ψ hp`. Substitute `hp` using the available equality. Set `θ` to `algebraMap (Y.X.presheaf.stalk y) Y.X.functionField`.

Establish `hθ : Function.Injective θ` using `IsFractionRing.injective _ _`. Establish `hs (x : Y.Fn) (hx : x ∈ (ratOf Y).O y) : ∃ a, θ a = x` using `mem_O_ratOf.1 hx`. Use `choose a ha using fun τ i k => hs _ ((hA.1 τ).1 i k)`. Establish `ea (τ : ι) : (Matrix.of (a τ)).map θ = A τ`. Use extensionality with `i k`.

Conclude with `ha τ i k`. Establish `hu (τ : ι) : IsUnit (Matrix.of (a τ)).transpose.det`. Take `⟨b, hb⟩` from `hs _ (hA.1 τ).2.2.1`. Use `IsUnit.of_mul_eq_one b (hθ ?_)` and prove the remaining obligations. Rewrite using `[Matrix.det_transpose, map_mul, map_one, hb, RingHom.map_det, RingHom.mapMatrix_apply, ea]`.

Conclude with `mul_inv_cancel₀ (hA.1.det_ne τ)`. Set `g : ι → GL (Fin N) (Y.X.presheaf.stalk y)` to `fun τ => Matrix.GeneralLinearGroup.mk'' _ (hu τ)`. Establish `hl : IsLocalRing (Y.X.presheaf.stalk y)` using `inferInstance`. Take `⟨g', hg'⟩` from `@exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) _ _ N Prod.fst Prod.snd (Y.X.presheaf.stalk y) _ hl (Y.X.fromSpecStalk y ≫ j)`. Establish `h₁ : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (fun τ => Matrix.GeneralLinearGroup.map θ (g' τ)) = flagPt Prod.fst Prod.snd (genMat j)`.

Rewrite using `[← spMap_flagPt, ← hg', ← Category.assoc, spMap_algebraMap_fromSpecStalk]`. Conclude with `flagPt_genMat j`. Establish `h₂ : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (genMat j) = flagPt Prod.fst Prod.snd (fun τ => Matrix.GeneralLinearGroup.map θ (g τ))`. Use `(flagPt_eq_iff_par _ _ (genFrame j) A (fun τ => rfl) fun τ => ?_).2 hA.2` and prove the remaining obligations. Use extensionality with `i k`.

Conclude with `ha τ k i`. Establish `h₃ : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g' = flagPt Prod.fst Prod.snd g`. Rewrite using `[flagPt_eq_iff_below]`. Introduce `τ i k hik`. Use `(flagPt_eq_iff_below _ _ _ _ _ _ _ _).1 (h₁.trans h₂) τ i k hik` as an intermediate fact.

Rewrite `this` using `[← map_inv, ← map_mul, Matrix.GeneralLinearGroup.map_apply]`. Conclude with `hθ (this.trans (map_zero θ).symm)`. Rewrite using `[Category.assoc]`. Use `(congrArg (spMap ψ ≫ ·) (hg'.trans h₃)).trans ?_` and prove the remaining obligations. Rewrite using `[spMap_flagPt]`.

Use `congr 1`. Use function extensionality and compare the values at `τ`. Use extensionality with `i k`. Rewrite using `[Matrix.GeneralLinearGroup.map_apply, hG]`. Express the relevant statement in the definitionally equal form `ψ (a τ k i) = (ratOf Y).val _ (A τ k i)`.

Rewrite using `[← ha]`. Conclude with `(val_ratOf ψ (a τ k i)).symm`.
-/
theorem comp_eq_flagPt (j : Y.X ⟶ Fl ι N) {K : Type} [Field K] (p : Sp K ⟶ Y.X) {A : Mat (fun _ : ι => N) Y.Fn}
    (hA : IsFrame j (p (IsLocalRing.closedPoint K)) A) (G : ι → GL (Fin N) K)
    (hG : ∀ τ, (G τ).1 = (A.map ((ratOf Y).val p) τ).transpose) :
    p ≫ j = flagPt Prod.fst Prod.snd G := by
  have hp := spMap_stalkClosedPointTo p
  generalize (Scheme.stalkClosedPointTo (R := .of K) p).hom = ψ at hp
  generalize p (IsLocalRing.closedPoint K) = y at hA ψ hp
  subst hp
  let θ := algebraMap (Y.X.presheaf.stalk y) Y.X.functionField
  have hθ : Function.Injective θ := IsFractionRing.injective _ _
  have hs (x : Y.Fn) (hx : x ∈ (ratOf Y).O y) : ∃ a, θ a = x := mem_O_ratOf.1 hx
  choose a ha using fun τ i k => hs _ ((hA.1 τ).1 i k)
  have ea (τ : ι) : (Matrix.of (a τ)).map θ = A τ := by
    ext i k
    exact ha τ i k
  have hu (τ : ι) : IsUnit (Matrix.of (a τ)).transpose.det := by
    obtain ⟨b, hb⟩ := hs _ (hA.1 τ).2.2.1
    refine IsUnit.of_mul_eq_one b (hθ ?_)
    rw [Matrix.det_transpose, map_mul, map_one, hb, RingHom.map_det, RingHom.mapMatrix_apply, ea]
    exact mul_inv_cancel₀ (hA.1.det_ne τ)
  let g : ι → GL (Fin N) (Y.X.presheaf.stalk y) := fun τ => Matrix.GeneralLinearGroup.mk'' _ (hu τ)
  have hl : IsLocalRing (Y.X.presheaf.stalk y) := inferInstance
  obtain ⟨g', hg'⟩ := @exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) _ _ N Prod.fst Prod.snd
    (Y.X.presheaf.stalk y) _ hl (Y.X.fromSpecStalk y ≫ j)
  have h₁ : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (fun τ => Matrix.GeneralLinearGroup.map θ (g' τ)) =
      flagPt Prod.fst Prod.snd (genMat j) := by
    rw [← spMap_flagPt, ← hg', ← Category.assoc, spMap_algebraMap_fromSpecStalk]
    exact flagPt_genMat j
  have h₂ : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (genMat j) =
      flagPt Prod.fst Prod.snd (fun τ => Matrix.GeneralLinearGroup.map θ (g τ)) := by
    refine (flagPt_eq_iff_par _ _ (genFrame j) A (fun τ => rfl) fun τ => ?_).2 hA.2
    ext i k
    exact ha τ k i
  have h₃ : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g' = flagPt Prod.fst Prod.snd g := by
    rw [flagPt_eq_iff_below]
    intro τ i k hik
    have := (flagPt_eq_iff_below _ _ _ _ _ _ _ _).1 (h₁.trans h₂) τ i k hik
    rw [← map_inv, ← map_mul, Matrix.GeneralLinearGroup.map_apply] at this
    exact hθ (this.trans (map_zero θ).symm)
  rw [Category.assoc]
  refine (congrArg (spMap ψ ≫ ·) (hg'.trans h₃)).trans ?_
  rw [spMap_flagPt]
  congr 1
  funext τ
  ext i k
  rw [Matrix.GeneralLinearGroup.map_apply, hG]
  change ψ (a τ k i) = (ratOf Y).val _ (A τ k i)
  rw [← ha]
  exact (val_ratOf ψ (a τ k i)).symm

/- English proof (translation)
Establish `h₁` using `GlobalTheory.ProjSpace.Model.isIso_str_zero (R := ℚ)`. Establish `h₂` using `isIso_proj_ι ℚ 0`. Establish `: IsIso (proj ℚ 0).str` using `@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₁`. Rewrite using `[← cancel_mono (proj ℚ 0).str, ← Spec.map_preimage (x ≫ _), ← Spec.map_preimage (x' ≫ _)]`. Use `congr 1`.

Conclude with `CommRingCat.hom_ext (Subsingleton.elim _ _)`.
-/
theorem hom_pt_ext {K : Type} [Field K] (x x' : Sp K ⟶ (proj ℚ 0).X) : x = x' := by
  have h₁ := GlobalTheory.ProjSpace.Model.isIso_str_zero (R := ℚ)
  have h₂ := isIso_proj_ι ℚ 0
  have : IsIso (proj ℚ 0).str := @IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₁
  rw [← cancel_mono (proj ℚ 0).str, ← Spec.map_preimage (x ≫ _), ← Spec.map_preimage (x' ≫ _)]
  congr 1
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/- English proof (translation)
Set `ψ` to `RatModel.valLoc (M := ratOf Y) p (p (IsLocalRing.closedPoint K)) specializes_rfl`. Establish `hψ (x : ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring) : (ratOf Y).val p x = ψ x` using `(RatModel.valLoc_eq_val (M := ratOf Y) p _ x).symm`. Establish `hB : Par 0 ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring (A.map φ)` using `hA.map (φ : (proj ℚ 0).Fn →+* Y.Fn) fun x hx => hφ.map_mem_O hx`. Establish `ec : A.map ((ratOf (proj ℚ 0)).val (p ≫ toPt Y)) = (A.map φ).map ((ratOf Y).val p)`. Use function extensionality and compare the values at `τ`.

Use extensionality with `i k`. Conclude with `hφ.val_comp p _ ((hA τ).1 i k)`. Establish `hc` using `hB.map_of _ ψ hψ`. Establish `einv : (A.map φ)⁻¹.map ((ratOf Y).val p) = ((A.map φ).map ((ratOf Y).val p))⁻¹`. Establish `e` using `hB.inv.map_mul_of hB _ ψ hψ`.

Rewrite `e` using `[Mat.inv_mul hB.det_ne]`. Use function extensionality and compare the values at `τ`. Use `(Matrix.inv_eq_left_inv ?_).symm` and prove the remaining obligations. Use `(congrFun e τ).symm.trans (Matrix.map_one _ ?_ ?_)` and prove the remaining obligations. Conclude with `(hψ 0).trans (map_zero ψ)`.

Conclude with `(hψ 1).trans (map_one ψ)`. Establish `key (A' : Mat (fun _ : ι => N) Y.Fn) (hA' : IsFrame j (p (IsLocalRing.closedPoint K)) A') : Par (fun _ => N) ⊤ (h * ((A' * (A.map φ)⁻¹).map ((ratOf Y).val p))⁻¹) ↔ p ≫ j = flagPt Prod.fst Prod.snd H`. Establish `hd` using `(hA'.1.map_of _ ψ hψ).det_ne`. Rewrite using `[comp_eq_flagPt j p hA' (trGL _ hd) fun _ => rfl, flagPt_eq_iff_par (trGL _ hd) H (A'.map ((ratOf Y).val p)) _ (fun _ => rfl) hH, hA'.1.map_mul_of hB.inv _ ψ hψ, einv, Mat.mul_inv_rev, Mat.inv_inv hc.det_ne, ec, mul_assoc]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨A', hA', hP⟩`. Conclude with `(key A' ((hE _ _).1 hA')).1 hP`. Introduce `e`. Take `⟨A', hA'⟩` from `E'.nonempty (p (IsLocalRing.closedPoint K))`. Conclude with `⟨A', hA', (key A' ((hE _ _).1 hA')).2 e⟩`.
-/
theorem bears_iff (j : Y.X ⟶ Fl ι N) (E' : Fr (ratOf Y) (fun _ : ι => N) (fun _ => N))
    (hE : ∀ y A', A' ∈ E'.S y ↔ IsFrame j y A') (φ : (proj ℚ 0).Fn →ₐ[ℚ] Y.Fn)
    (hφ : (ratOf (proj ℚ 0)).IsHom (ratOf Y) φ (toPt Y)) {K : Type} [Field K] (p : Sp K ⟶ Y.X)
    {A : Mat (fun _ : ι => N) (proj ℚ 0).Fn}
    (hA : Par 0 ((ratOf (proj ℚ 0)).O (toPt Y (p (IsLocalRing.closedPoint K)))).toSubring A)
    (h : Mat (fun _ : ι => N) K) (H : ι → GL (Fin N) K)
    (hH : ∀ τ, (H τ).1 = ((h * A.map ((ratOf (proj ℚ 0)).val (p ≫ toPt Y))) τ).transpose) :
    Bears E' φ A h p ↔ p ≫ j = flagPt Prod.fst Prod.snd H := by
  let ψ := RatModel.valLoc (M := ratOf Y) p (p (IsLocalRing.closedPoint K)) specializes_rfl
  have hψ (x : ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring) : (ratOf Y).val p x = ψ x :=
    (RatModel.valLoc_eq_val (M := ratOf Y) p _ x).symm
  have hB : Par 0 ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring (A.map φ) :=
    hA.map (φ : (proj ℚ 0).Fn →+* Y.Fn) fun x hx => hφ.map_mem_O hx
  have ec : A.map ((ratOf (proj ℚ 0)).val (p ≫ toPt Y)) = (A.map φ).map ((ratOf Y).val p) := by
    funext τ
    ext i k
    exact hφ.val_comp p _ ((hA τ).1 i k)
  have hc := hB.map_of _ ψ hψ
  have einv : (A.map φ)⁻¹.map ((ratOf Y).val p) = ((A.map φ).map ((ratOf Y).val p))⁻¹ := by
    have e := hB.inv.map_mul_of hB _ ψ hψ
    rw [Mat.inv_mul hB.det_ne] at e
    funext τ
    refine (Matrix.inv_eq_left_inv ?_).symm
    refine (congrFun e τ).symm.trans (Matrix.map_one _ ?_ ?_)
    · exact (hψ 0).trans (map_zero ψ)
    · exact (hψ 1).trans (map_one ψ)
  have key (A' : Mat (fun _ : ι => N) Y.Fn) (hA' : IsFrame j (p (IsLocalRing.closedPoint K)) A') :
      Par (fun _ => N) ⊤ (h * ((A' * (A.map φ)⁻¹).map ((ratOf Y).val p))⁻¹) ↔
        p ≫ j = flagPt Prod.fst Prod.snd H := by
    have hd := (hA'.1.map_of _ ψ hψ).det_ne
    rw [comp_eq_flagPt j p hA' (trGL _ hd) fun _ => rfl, flagPt_eq_iff_par (trGL _ hd) H (A'.map ((ratOf Y).val p)) _ (fun _ => rfl) hH,
      hA'.1.map_mul_of hB.inv _ ψ hψ, einv, Mat.mul_inv_rev, Mat.inv_inv hc.det_ne, ec, mul_assoc]
  constructor
  · rintro ⟨A', hA', hP⟩
    exact (key A' ((hE _ _).1 hA')).1 hP
  · intro e
    obtain ⟨A', hA'⟩ := E'.nonempty (p (IsLocalRing.closedPoint K))
    exact ⟨A', hA', (key A' ((hE _ _).1 hA')).2 e⟩

/- English proof (translation)
Establish `hA₀ : Par 0 ((ratOf (proj ℚ 0)).O (x (IsLocalRing.closedPoint K))).toSubring A`. Establish `e : A * (1 : Mat (fun _ : ι => N) (proj ℚ 0).Fn)⁻¹ = A`. Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `A τ * (1 : Matrix _ _ _)⁻¹ = A τ`. Rewrite using `[inv_one, mul_one]`.

Conclude with `e ▸ hA`. Establish `hc : Par 0 ⊤ (h * A.map ((ratOf (proj ℚ 0)).val x))` using `hh.mul (hA₀.map_of _ (RatModel.valLoc (M := ratOf (proj ℚ 0)) x _ specializes_rfl) fun z => (RatModel.valLoc_eq_val (M := ratOf (proj ℚ 0)) x _ z).symm)`. Establish `key (p : Sp K ⟶ Y.X) : Bears E' φ A h p ↔ p ≫ j = flagPt Prod.fst Prod.snd (trGL _ hc.det_ne)`. Take `rfl : x = p ≫ toPt Y` from `hom_pt_ext _ _`. Conclude with `bears_iff j E' hE φ hφ p hA₀ h _ fun _ => rfl`.

Set `p : Sp K ⟶ Y.X` to `hj.lift (flagPt Prod.fst Prod.snd (trGL _ hc.det_ne)) (x ≫ (proj ℚ 0).str) (toZ_ext _ _)`. Use `⟨p, ⟨hom_pt_ext _ _, (key p).2 (hj.lift_fst _ _ _)⟩, fun q hq => hj.hom_ext ?_ ?_⟩` and prove the remaining obligations. Conclude with `((key q).1 hq.2).trans (hj.lift_fst _ _ _).symm`. Rewrite using `[← Spec.map_preimage (q ≫ _), ← Spec.map_preimage (p ≫ _)]`. Use `congr 1`.

Conclude with `CommRingCat.hom_ext (Subsingleton.elim _ _)`.
-/
theorem existsUnique_bears (ι : Type) [Fintype ι] (N : ℕ) (Y : Var ℚ) (j : Y.X ⟶ Fl ι N)
    (hj : IsPullback j Y.str (flStr ι N) (spMap (algebraMap ℤ ℚ)))
    (E' : Fr (ratOf Y) (fun _ : ι => N) (fun _ => N)) (hE : ∀ y A', A' ∈ E'.S y ↔ IsFrame j y A')
    (φ : (proj ℚ 0).Fn →ₐ[ℚ] Y.Fn) (hφ : (ratOf (proj ℚ 0)).IsHom (ratOf Y) φ (toPt Y))
    (K : Type) [Field K] (x : Sp K ⟶ (proj ℚ 0).X) (A : Mat (fun _ : ι => N) (proj ℚ 0).Fn)
    (hA : A ∈ (triv ι N).S (x (IsLocalRing.closedPoint K))) (h : Mat (fun _ : ι => N) K) (hh : Par 0 ⊤ h) :
    ∃! p : Sp K ⟶ Y.X, p ≫ toPt Y = x ∧ Bears E' φ A h p := by
  have hA₀ : Par 0 ((ratOf (proj ℚ 0)).O (x (IsLocalRing.closedPoint K))).toSubring A := by
    have e : A * (1 : Mat (fun _ : ι => N) (proj ℚ 0).Fn)⁻¹ = A := by
      funext τ
      change A τ * (1 : Matrix _ _ _)⁻¹ = A τ
      rw [inv_one, mul_one]
    exact e ▸ hA
  have hc : Par 0 ⊤ (h * A.map ((ratOf (proj ℚ 0)).val x)) :=
    hh.mul (hA₀.map_of _ (RatModel.valLoc (M := ratOf (proj ℚ 0)) x _ specializes_rfl)
      fun z => (RatModel.valLoc_eq_val (M := ratOf (proj ℚ 0)) x _ z).symm)
  have key (p : Sp K ⟶ Y.X) : Bears E' φ A h p ↔ p ≫ j = flagPt Prod.fst Prod.snd (trGL _ hc.det_ne) := by
    obtain rfl : x = p ≫ toPt Y := hom_pt_ext _ _
    exact bears_iff j E' hE φ hφ p hA₀ h _ fun _ => rfl
  let p : Sp K ⟶ Y.X :=
    hj.lift (flagPt Prod.fst Prod.snd (trGL _ hc.det_ne)) (x ≫ (proj ℚ 0).str) (toZ_ext _ _)
  refine ⟨p, ⟨hom_pt_ext _ _, (key p).2 (hj.lift_fst _ _ _)⟩, fun q hq => hj.hom_ext ?_ ?_⟩
  · exact ((key q).1 hq.2).trans (hj.lift_fst _ _ _).symm
  · rw [← Spec.map_preimage (q ≫ _), ← Spec.map_preimage (p ≫ _)]
    congr 1
    exact CommRingCat.hom_ext (Subsingleton.elim _ _)

end GlobalTheory.FlagQ.Lifts

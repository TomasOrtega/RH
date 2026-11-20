import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitPeriodsBoundedBelowClosedPointStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.PreSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

/- English proof (translation)
The claim follows from `GlobalTheory.T.character_group_finrank_le_min_signature_unitary_trait E H Dw l Xo c T`.
-/
theorem rank_le (T : UTrait Xo c) : Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := GlobalTheory.T.character_group_finrank_le_min_signature_unitary_trait E H Dw l Xo c T

/- English proof (translation)
The claim follows from `GlobalTheory.T.classical_trait_periods_bounded_below_closed_point E H Dw l Xo c C X₁ p z₁ hz`.
-/
theorem lam (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (hz : IsClosed ({z₁} : Set X₁.M.Z)) :
    ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 →
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ :=
  GlobalTheory.T.classical_trait_periods_bounded_below_closed_point E H Dw l Xo c C X₁ p z₁ hz

/- English proof (translation)
The claim follows from `Module.Finite.of_restrictScalars_finite ℤ _ _`.
-/
theorem finite_X (T : UTrait Xo c) : Module.Finite (𝓞 E) T.P.D.toPre.X :=
  Module.Finite.of_restrictScalars_finite ℤ _ _

/- English proof (translation)
Establish `: Module.Finite (𝓞 E) T.P.D.toPre.X` using `finite_X T`. Establish `: Module.Flat (𝓞 E) T.P.D.toPre.X`. Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce and unpack `x ⟨a, hx⟩`. Assume the negation of the conclusion as `hx0`.

Take `⟨n, hn, b, hb⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (a : 𝓞 E)).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero (nonZeroDivisors.coe_ne_zero a))`. Establish `h : n • x = 0`. Establish `hx' : (a : 𝓞 E) • x = 0` using `hx`. Rewrite using `[← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hx', smul_zero]`. Conclude with `hx0 ((smul_eq_zero.1 h).resolve_left hn)`.

Establish `: Module.FinitePresentation (𝓞 E) T.P.D.toPre.X` using `Module.finitePresentation_of_finite _ _`. Conclude with `Module.Flat.projective_of_finitePresentation`.
-/
theorem projective_X (T : UTrait Xo c) : Module.Projective (𝓞 E) T.P.D.toPre.X := by
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := finite_X T
  have : Module.Flat (𝓞 E) T.P.D.toPre.X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨a, hx⟩
    by_contra hx0
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (a : 𝓞 E)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero (nonZeroDivisors.coe_ne_zero a))
    have h : n • x = 0 := by
      have hx' : (a : 𝓞 E) • x = 0 := hx
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hx', smul_zero]
    exact hx0 ((smul_eq_zero.1 h).resolve_left hn)
  have : Module.FinitePresentation (𝓞 E) T.P.D.toPre.X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

variable {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def evC (t : UCTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p :=
  (RatModel.valHomOf (gPt p ≫ t.y) z₁ (RatModel.gPt_specializes t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evC_apply (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : evC t a = t.val a := rfl

/- English proof (translation)
The claim follows from `RatModel.norm_val_le_one t.cen (X₁.M.stalkEquiv z₁ a).2`.
-/
theorem norm_evC_le (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖evC t a‖ ≤ 1 :=
  RatModel.norm_val_le_one t.cen (X₁.M.stalkEquiv z₁ a).2

/- English proof (translation)
Establish `h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a)` using `fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)`. Conclude with `(RatModel.norm_val_lt_one_iff t.cen (X₁.M.stalkEquiv z₁ a).2).2 h1`.
-/
theorem norm_evC_lt (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) (ha : a ∈ maximalIdeal _) :
    ‖evC t a‖ < 1 := by
  have h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a) := fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)
  exact (RatModel.norm_val_lt_one_iff t.cen (X₁.M.stalkEquiv z₁ a).2).2 h1

/- English proof (translation)
Establish `hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero`. Establish `h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0` using `(map_ne_zero _).2 hϖ0`. Establish `hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1`. Assume the negation of the conclusion as `hge`. Use `push_neg at hge`.

Establish `hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1`. Rewrite using `[map_inv₀, norm_inv]`. Conclude with `inv_le_one_of_one_le₀ hge`. Take `⟨w, hw⟩` from `(t.int _).1 hinv`. Apply `t.T.irr.not_isUnit` to reduce the goal to its premises.

Use `isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]`. Unfold `UCTrait.sc`. Use `Real.log_neg (norm_pos_iff.2 h0) hlt` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

/- English proof (translation)
Take `⟨j, hj⟩` from `IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx`. Use `fin_cases j`. Simplify using `using hj`.
-/
theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

/- English proof (translation)
Rewrite using `[balForms_eq_levelForms]`. Conclude with `T.lev`.
-/
theorem be_bal (T : UTrait Xo c) : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X := by
  rw [balForms_eq_levelForms]; exact T.lev

end GlobalTheory.UPoinc.PreSys

namespace GlobalTheory.UPoinc.PreSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

variable (E X₁ p) in

abbrev Key : Type :=
  (Sp (OO p) ⟶ X₁.M.Z) × (Σ k : ℕ, (𝓞 E →+* Module.End ℤ (Fin k → ℤ)) × ((Fin k → ℤ) → (Fin k → ℤ) → ℝ))

def Rep (t : UCTrait X₁ p z₁) (q : Key E X₁ p) : Prop :=
  t.y = q.1 ∧ ∃ e : (Fin q.2.1 → ℤ) ≃ₗ[ℤ] t.T.P.D.toPre.X, (∀ (a : 𝓞 E) u, e (q.2.2.1 a u) = a • e u) ∧
    ∀ u v, q.2.2.2 u v = t.sc * t.T.be (e u) (e v)

def coord (t : UCTrait X₁ p z₁) : (Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) ≃ₗ[ℤ] t.T.P.D.toPre.X :=
  (Module.finBasis ℤ t.T.P.D.toPre.X).equivFun.symm

def actOf (t : UCTrait X₁ p z₁) : 𝓞 E →+* Module.End ℤ (Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) where
  toFun a := (coord t).symm.toLinearMap ∘ₗ (DistribSMul.toLinearMap ℤ t.T.P.D.toPre.X a) ∘ₗ (coord t).toLinearMap
  map_one' := LinearMap.ext fun u => by simp
  map_mul' a b := LinearMap.ext fun u => by simp [mul_smul]
  map_zero' := LinearMap.ext fun u => by simp
  map_add' a b := LinearMap.ext fun u => by simp [add_smul]

/- English proof (translation)
Simplify using `[actOf]`.
-/
theorem coord_actOf (t : UCTrait X₁ p z₁) (a : 𝓞 E) (u : Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) :
    coord t (actOf t a u) = a • coord t u := by
  simp [actOf]

def keyOf (t : UCTrait X₁ p z₁) : Key E X₁ p :=
  (t.y, ⟨Module.finrank ℤ t.T.P.D.toPre.X, actOf t, fun u v => t.sc * t.T.be (coord t u) (coord t v)⟩)

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl, coord t, coord_actOf t, fun _ _ => rfl⟩`.
-/
theorem rep_keyOf (t : UCTrait X₁ p z₁) : Rep t (keyOf t) := ⟨rfl, coord t, coord_actOf t, fun _ _ => rfl⟩

variable (X₁ p z₁) in

def Pts : Type := {q : Key E X₁ p // ∃ t : UCTrait X₁ p z₁, Rep t q}

noncomputable def pick (y : Pts X₁ p z₁) : UCTrait X₁ p z₁ := Classical.choose y.2

/- English proof (translation)
The claim follows from `Classical.choose_spec y.2`.
-/
theorem pick_rep (y : Pts X₁ p z₁) : Rep (pick y) y.1 := Classical.choose_spec y.2

/- English proof (translation)
Take `⟨-, f, hf, hfb⟩` from `h`. Take `⟨-, f', hf', hfb'⟩` from `h'`. Set `g : t.T.P.D.toPre.X ≃ₗ[ℤ] t'.T.P.D.toPre.X` to `f.symm.trans f'`. Establish `hg : ∀ (a : 𝓞 E) x, g (a • x) = a • g x`. Introduce `a x`.

Take `⟨u, rfl⟩` from `f.surjective x`. Simplify using `only [g, LinearEquiv.trans_apply, ← hf, LinearEquiv.symm_apply_apply, hf']`. Use `⟨{ g with map_smul' := hg }, fun a b => ?_⟩` and prove the remaining obligations. Take `⟨u, rfl⟩` from `f.surjective a`. Take `⟨v, rfl⟩` from `f.surjective b`.

Use `show _ = t'.sc * t'.T.be (g (f u)) (g (f v))`. Simplify using `only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]`. Rewrite using `[← hfb, ← hfb']`.
-/
theorem exists_equiv_of_rep {t t' : UCTrait X₁ p z₁} {q : Key E X₁ p} (h : Rep t q) (h' : Rep t' q) :
    ∃ e : t.T.P.D.toPre.X ≃ₗ[𝓞 E] t'.T.P.D.toPre.X, ∀ a b, t.sc * t.T.be a b = t'.sc * t'.T.be (e a) (e b) := by
  obtain ⟨-, f, hf, hfb⟩ := h
  obtain ⟨-, f', hf', hfb'⟩ := h'
  let g : t.T.P.D.toPre.X ≃ₗ[ℤ] t'.T.P.D.toPre.X := f.symm.trans f'
  have hg : ∀ (a : 𝓞 E) x, g (a • x) = a • g x := by
    intro a x
    obtain ⟨u, rfl⟩ := f.surjective x
    simp only [g, LinearEquiv.trans_apply, ← hf, LinearEquiv.symm_apply_apply, hf']
  refine ⟨{ g with map_smul' := hg }, fun a b => ?_⟩
  obtain ⟨u, rfl⟩ := f.surjective a
  obtain ⟨v, rfl⟩ := f.surjective b
  show _ = t'.sc * t'.T.be (g (f u)) (g (f v))
  simp only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [← hfb, ← hfb']

variable (X₁ p z₁) in

noncomputable def sys : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁) where
  Y := Pts X₁ p z₁
  ev y := evC (pick y)
  ev_le y h := norm_evC_le _ h
  ev_lt y h hh := norm_evC_lt _ h hh
  X y := (pick y).T.P.D.toPre.X
  fin y := finite_X _
  proj y := projective_X _
  rank_le y := rank_le _
  β y := (pick y).T.be
  bal y := be_bal _
  pos y x hx := be_pos _ x hx
  sc y := (pick y).sc
  sc_pos y := sc_pos _

/- English proof (translation)
Introduce `t`. Use `⟨⟨keyOf t, t, rep_keyOf t⟩, fun a => ?_, ?_⟩` and prove the remaining obligations. Take `⟨hy, -⟩` from `pick_rep ⟨keyOf t, t, rep_keyOf t⟩ show evC _ a = t.val a`. Rewrite using `[evC_apply]`. Unfold `UCTrait.val`.

Rewrite using `[hy]`. Both sides reduce to the same expression. Conclude with `exists_equiv_of_rep (pick_rep ⟨keyOf t, t, rep_keyOf t⟩) (rep_keyOf t)`.
-/
theorem sys_matches : UMatches (sys X₁ p z₁) := by
  intro t
  refine ⟨⟨keyOf t, t, rep_keyOf t⟩, fun a => ?_, ?_⟩
  · obtain ⟨hy, -⟩ := pick_rep ⟨keyOf t, t, rep_keyOf t⟩
    show evC _ a = t.val a
    rw [evC_apply]
    unfold UCTrait.val
    rw [hy]
    rfl
  · exact exists_equiv_of_rep (pick_rep ⟨keyOf t, t, rep_keyOf t⟩) (rep_keyOf t)

/- English proof (translation)
Take `⟨K, hK⟩` from `lam X₁ p z₁ hz`. Conclude with `⟨K, fun y x hx => hK (pick y) x hx⟩`.
-/
theorem sys_lam (hz : IsClosed ({z₁} : Set X₁.M.Z)) : (sys X₁ p z₁).abelian₂ := by
  obtain ⟨K, hK⟩ := lam X₁ p z₁ hz
  exact ⟨K, fun y x hx => hK (pick y) x hx⟩

end GlobalTheory.UPoinc.PreSys

open GlobalTheory Classical in

/- English proof (translation)
Introduce `E _ _ _ H Dw _ l Xo c C X₁ p _ z₁ hz`. Conclude with `⟨GlobalTheory.UPoinc.PreSys.sys X₁ p z₁, GlobalTheory.UPoinc.PreSys.sys_matches, GlobalTheory.UPoinc.PreSys.sys_lam hz, fun y => ⟨GlobalTheory.UPoinc.PreSys.pick y, fun a => rfl, LinearEquiv.refl _ _, fun a b => rfl⟩⟩`.
-/
theorem GlobalTheory.UPoinc.PreSys.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), UMatches Φ ∧ Φ.abelian₂ ∧ (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) := by
  intro E _ _ _ H Dw _ l Xo c C X₁ p _ z₁ hz
  exact ⟨GlobalTheory.UPoinc.PreSys.sys X₁ p z₁, GlobalTheory.UPoinc.PreSys.sys_matches, GlobalTheory.UPoinc.PreSys.sys_lam hz,
    fun y => ⟨GlobalTheory.UPoinc.PreSys.pick y, fun a => rfl, LinearEquiv.refl _ _, fun a b => rfl⟩⟩

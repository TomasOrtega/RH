import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPer

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L : LB A.left}

/- English proof (translation)
Use `Over.w (u.ex w)` as an intermediate fact. Simplify using `[str, this]`.
-/
theorem holUnif_ex_left_comp_str (u : HolUnif A L g) (w : Fin g → ℂ) : (u.ex w).left ≫ str A = 𝟙 (Sp ℂ) := by
  have := Over.w (u.ex w)
  simp [str, this]

/- English proof (translation)
Use `show valAt' (u.ex w).left U (((str A).appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c`. Rewrite using `[valAt'_appLE (u.ex w).left (str A) ⊤ U le_top _ hw, holUnif_ex_left_comp_str]`. Conclude with `valAt'_id_top c`.
-/
theorem holUnif_val_algebraMap (u : HolUnif A L g) (U : A.left.Opens) (w : Fin g → ℂ) (hw : w ∈ pre u.ex U) (c : ℂ) :
    val u.ex U (algebraMap ℂ (Sec (str A) U) c) w = c := by
  show valAt' (u.ex w).left U (((str A).appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c
  rw [valAt'_appLE (u.ex w).left (str A) ⊤ U le_top _ hw, holUnif_ex_left_comp_str]
  exact valAt'_id_top c

/- English proof (translation)
The claim follows from `funext fun w => valAt'_mul (u.ex w).left U a b`.
-/
theorem holUnif_val_mul (u : HolUnif A L g) (U : A.left.Opens) (a b : Sec (str A) U) :
    val u.ex U (a * b) = fun w => val u.ex U a w * val u.ex U b w :=
  funext fun w => valAt'_mul (u.ex w).left U a b

/- English proof (translation)
The claim follows from `funext fun w => valAt'_add (u.ex w).left U a b`.
-/
theorem holUnif_val_add (u : HolUnif A L g) (U : A.left.Opens) (a b : Sec (str A) U) :
    val u.ex U (a + b) = fun w => val u.ex U a w + val u.ex U b w :=
  funext fun w => valAt'_add (u.ex w).left U a b

/- English proof (translation)
The claim follows from `(u.hol U b).2.differentiableAt (((u.hol U b).1).mem_nhds hz)`.
-/
theorem holUnif_differentiableAt_val (u : HolUnif A L g) (U : A.left.Opens) (b : Sec (str A) U) {z : Fin g → ℂ}
    (hz : z ∈ pre u.ex U) : DifferentiableAt ℂ (val u.ex U b) z :=
  (u.hol U b).2.differentiableAt (((u.hol U b).1).mem_nhds hz)

/- English proof (translation)
Set `N` to `(Fin g → ℂ) →L[ℂ] ℂ`. Set `e : Sec (str A) U →+* ℂ` to `valAtHom (u.ex z).left U hz`. Establish `he : ∀ a, e a = val u.ex U a z` using `fun a => (valAt'_eq_valAtHom (u.ex z).left hz a).symm`. Use `letI : Module (Sec (str A) U) N := Module.compHom N e`. Use `haveI : IsScalarTower ℂ (Sec (str A) U) N := ⟨fun c a n => by show e (c • a) • n = c • (e a • n)`.

Rewrite using `[Algebra.smul_def, map_mul, mul_smul, he (algebraMap ℂ _ c), holUnif_val_algebraMap u U z hz]⟩`. Establish `hc : ∀ (c : ℂ) (b : Sec (str A) U), val u.ex U (c • b) =ᶠ[nhds z] fun w => c * val u.ex U b w`. Introduce `c b`. Use `filter_upwards [((u.hol U b).1).mem_nhds hz] with w hw`. Rewrite using `[Algebra.smul_def, holUnif_val_mul]`.

Conclude with `congrArg (· * val u.ex U b w) (holUnif_val_algebraMap u U w hw c)`. Set `Dl : Sec (str A) U →ₗ[ℂ] N` to `{ toFun := fun b => fderiv ℂ (val u.ex U b) z map_add' := fun a b => (congrArg (fun f => fderiv ℂ f z) (holUnif_val_add u U a b)).trans (fderiv_add (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz)) map_smul' := fun c b => (hc c b).fderiv_eq.trans (f …`. Set `D' : Derivation ℂ (Sec (str A) U) N` to `{ Dl with map_one_eq_zero' := by show fderiv ℂ (val u.ex U 1) z = 0`. Establish `h1 : val u.ex U (1 : Sec (str A) U) =ᶠ[nhds z] fun _ => (1 : ℂ)` using `by filter_upwards [((u.hol U 1).1).mem_nhds hz] with w hw`. Conclude with `valAt'_one (u.ex w).left hw`.

Conclude with `h1.fderiv_eq.trans (fderiv_const_apply 1)`. Use the proof step `leibniz' := fun a b => by show fderiv ℂ (val u.ex U (a * b)) z = e a • fderiv ℂ (val u.ex U b) z + e b • fderiv ℂ (val u.ex U a) z`. Rewrite using `[he, he]`. Conclude with `(congrArg (fun f => fderiv ℂ f z) (holUnif_val_mul u U a b)).trans (fderiv_mul (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz)) }`. Use `⟨D'.liftKaehlerDifferential.restrictScalars ℂ, fun a b => ?_⟩` and prove the remaining obligations.

Use `show D'.liftKaehlerDifferential (a • KaehlerDifferential.D ℂ (Sec (str A) U) b) = _`. Rewrite using `[LinearMap.map_smul, Derivation.liftKaehlerDifferential_comp_D]`. Use `show e a • fderiv ℂ (val u.ex U b) z = _`. Rewrite using `[he]`.
-/
theorem exists_isEv (u : HolUnif A L g) (U : A.left.Opens) {z : Fin g → ℂ} (hz : z ∈ pre u.ex U) :
    ∃ E, IsEv u.ex U z E := by
  let N := (Fin g → ℂ) →L[ℂ] ℂ
  let e : Sec (str A) U →+* ℂ := valAtHom (u.ex z).left U hz
  have he : ∀ a, e a = val u.ex U a z := fun a => (valAt'_eq_valAtHom (u.ex z).left hz a).symm
  letI : Module (Sec (str A) U) N := Module.compHom N e
  haveI : IsScalarTower ℂ (Sec (str A) U) N := ⟨fun c a n => by
    show e (c • a) • n = c • (e a • n)
    rw [Algebra.smul_def, map_mul, mul_smul, he (algebraMap ℂ _ c), holUnif_val_algebraMap u U z hz]⟩
  have hc : ∀ (c : ℂ) (b : Sec (str A) U), val u.ex U (c • b) =ᶠ[nhds z] fun w => c * val u.ex U b w := by
    intro c b
    filter_upwards [((u.hol U b).1).mem_nhds hz] with w hw
    rw [Algebra.smul_def, holUnif_val_mul]
    exact congrArg (· * val u.ex U b w) (holUnif_val_algebraMap u U w hw c)
  let Dl : Sec (str A) U →ₗ[ℂ] N :=
    { toFun := fun b => fderiv ℂ (val u.ex U b) z
      map_add' := fun a b =>
        (congrArg (fun f => fderiv ℂ f z) (holUnif_val_add u U a b)).trans
          (fderiv_add (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz))
      map_smul' := fun c b =>
        (hc c b).fderiv_eq.trans (fderiv_const_mul (holUnif_differentiableAt_val u U b hz) c) }
  let D' : Derivation ℂ (Sec (str A) U) N :=
    { Dl with
      map_one_eq_zero' := by
        show fderiv ℂ (val u.ex U 1) z = 0
        have h1 : val u.ex U (1 : Sec (str A) U) =ᶠ[nhds z] fun _ => (1 : ℂ) := by
          filter_upwards [((u.hol U 1).1).mem_nhds hz] with w hw
          exact valAt'_one (u.ex w).left hw
        exact h1.fderiv_eq.trans (fderiv_const_apply 1)
      leibniz' := fun a b => by
        show fderiv ℂ (val u.ex U (a * b)) z = e a • fderiv ℂ (val u.ex U b) z + e b • fderiv ℂ (val u.ex U a) z
        rw [he, he]
        exact (congrArg (fun f => fderiv ℂ f z) (holUnif_val_mul u U a b)).trans
          (fderiv_mul (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz)) }
  refine ⟨D'.liftKaehlerDifferential.restrictScalars ℂ, fun a b => ?_⟩
  show D'.liftKaehlerDifferential (a • KaehlerDifferential.D ℂ (Sec (str A) U) b) = _
  rw [LinearMap.map_smul, Derivation.liftKaehlerDifferential_comp_D]
  show e a • fderiv ℂ (val u.ex U b) z = _
  rw [he]

/- English proof (translation)
Establish `h` using `exists_isEv u U hz`. Rewrite using `[evForm, dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem isEv_evForm (u : HolUnif A L g) (U : A.left.Opens) {z : Fin g → ℂ} (hz : z ∈ pre u.ex U) :
    IsEv u.ex U z (evForm u.ex U z) := by
  have h := exists_isEv u U hz
  rw [evForm, dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Introduce `A _ g L u U z hz`. Establish `hE` using `isEv_evForm u U hz`. Establish `hone : val u.ex U (1 : Sec (str A) U) z = 1` using `valAt'_one (u.ex z).left hz`. Establish `hD : ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z`. Introduce `b`.

Use `hE 1 b` as an intermediate fact. Rewrite `this` using `[one_smul, hone, one_smul]`. Then use the resulting hypothesis. Use `⟨hE, fun a ξ => ?_, hD⟩` and prove the remaining obligations. Establish `hspan` using `KaehlerDifferential.span_range_derivation ℂ (Sec (str A) U)`. Establish `hξ : ξ ∈ Submodule.span (Sec (str A) U) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U)))`.

Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`. Use `revert a`. Proceed by induction on `hξ using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨b, rfl⟩` from `hx`. Introduce `a`. Rewrite using `[hE a b, hD]`. Consider the case `zero => intro a`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy => intro a`. Rewrite using `[smul_add, map_add, map_add, hx, hy, smul_add]`. Consider the case `smul s x _ hx`. Introduce `a`. Rewrite using `[smul_smul, hx, hx, smul_smul, holUnif_val_mul]`.
-/
theorem evForm_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens),
    ∀ z ∈ pre u.ex U, IsEv u.ex U z (evForm u.ex U z) ∧
      (∀ (a : Sec (str A) U) ξ, evForm u.ex U z (a • ξ) = val u.ex U a z • evForm u.ex U z ξ) ∧
      ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
  intro A _ g L u U z hz
  have hE := isEv_evForm u U hz
  have hone : val u.ex U (1 : Sec (str A) U) z = 1 := valAt'_one (u.ex z).left hz
  have hD : ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
    intro b
    have := hE 1 b
    rwa [one_smul, hone, one_smul] at this
  refine ⟨hE, fun a ξ => ?_, hD⟩
  have hspan := KaehlerDifferential.span_range_derivation ℂ (Sec (str A) U)
  have hξ : ξ ∈ Submodule.span (Sec (str A) U) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U))) := by
    rw [hspan]; exact Submodule.mem_top
  revert a
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    intro a
    rw [hE a b, hD]
  | zero => intro a; simp
  | add x y _ _ hx hy => intro a; rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | smul s x _ hx =>
    intro a
    rw [smul_smul, hx, hx, smul_smul, holUnif_val_mul]

end GlobalTheory.CechPer

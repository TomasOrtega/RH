import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesOnPeriodSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplication
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmCurveHomOfPureTypeVector
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmEllipticCurveHomExistsPureTypeVector
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsConjSplitPointLatticeLinearMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsometryOfConjugateSplitPoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType
open scoped CategoryTheory.Obj
open GlobalTheory.CompRat (Curve wC wE IsSplit)

namespace GlobalTheory.AnyLevel

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ g ty F _ _ hty c j f S hS hval i P P' hP hP' x x' hx1 hx2 hx1' hx2'`. Establish `hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty`. Rewrite using `[(F.sig i).1, (F.sig i).2]`. Conclude with `hty`. Take `⟨B, Q, hBo, hBc, hQ, huniq⟩` from `GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'`.

Establish `hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom`. Rewrite using `[← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]`. Set `y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c)` to `fun b => if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x`. Establish `hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b)` using `fun b hb => by`. Simplify using `only [y, dif_pos hb, pullback.lift_fst]`.

Establish `hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j` using `fun b hb => by`. Simplify using `only [y, dif_pos hb, pullback.lift_snd]`. Establish `hhol : IsHolTo B y` using `GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _) (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1) (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)`. Establish `hcont : ContinuousOn (fun b => valAt' (y b) ⊤ f) B` using `((hhol ⊤ f).2.mono fun b hb => ⟨hb, le_of_eq rfl⟩).continuousOn`. Establish `hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R → z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z`.

Introduce `R hR z hz1 hz2`. Take `⟨b, ⟨hb, h, hh⟩, -⟩` from `huniq R hR`. Use `⟨b, hb, pullback.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[hy1 b hb, hz1]`. Conclude with `(F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩`.

Rewrite using `[hy2 b hb, hz2]`. Take `⟨b, hb, e⟩` from `hfind P hP x hx1 hx2`. Take `⟨b', hb', e'⟩` from `hfind P' hP' x' hx1' hx2'`. Rewrite using `[← e, ← e']`. Conclude with `hBc.isPreconnected.constant_of_mapsTo hS.isDiscrete hcont (fun a ha => hval _ (hy2 a ha)) hb hb'`.
-/
theorem valAt_eq_of_finite_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (c : Coeff l) (j : c.F →+* ℂ) (f : Γ(Xo.XF c, ⊤)) (S : Set ℂ), S.Finite → (∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f ∈ S) → ∀ i P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → ∀ x x' : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i P → x ≫ pullback.snd _ _ = spMap j → x' ≫ pullback.fst _ _ = F.u i P' → x' ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f = valAt' x' ⊤ f := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty c j f S hS hval i P P' hP hP' x x' hx1 hx2 hx1' hx2'
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hcont : ContinuousOn (fun b => valAt' (y b) ⊤ f) B :=
    ((hhol ⊤ f).2.mono fun b hb => ⟨hb, le_of_eq rfl⟩).continuousOn
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  rw [← e, ← e']
  exact hBc.isPreconnected.constant_of_mapsTo hS.isDiscrete hcont (fun a ha => hval _ (hy2 a ha)) hb hb'

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ g ty F _ _ _ C i P hP ε a ha`. Take `⟨_, _, _, _, _, m, -⟩` from `sabPull Out.CubePf.cubePull (F.u i P) Xo.univ.t`. Take `⟨φ, -, hφ⟩` from `exists_isHomFamily_complex thetaUnifAV_closed firstFiveLaws.1.weil F i hP m C.u C.g_eq C.theta C.c_ne C.lat (ρ := ((ε : ℤ) : ℂ) * H.rt0) (by`. Rewrite using `[mul_pow, H.sqrt_neg_disc_sq, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]`. Use the proof step `simp)`.

Use `⟨(φ ⟨a, ha⟩).left ≫ m.φ, ?_, fun z => hφ ⟨a, ha⟩ z⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]`.
-/
theorem exists_hom_of_pureType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ C i P hP ε a ha
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (F.u i P) Xo.univ.t
  obtain ⟨φ, -, hφ⟩ := exists_isHomFamily_complex thetaUnifAV_closed firstFiveLaws.1.weil F i hP m C.u C.g_eq
    C.theta C.c_ne C.lat (ρ := ((ε : ℤ) : ℂ) * H.rt0) (by
      rw [mul_pow, H.sqrt_neg_disc_sq, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
      simp)
  refine ⟨(φ ⟨a, ha⟩).left ≫ m.φ, ?_, fun z => hφ ⟨a, ha⟩ z⟩
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]

open GlobalTheory.CurveHomLift GlobalTheory.UniformLift in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ g ty F _ _ _ C i P hP φ x ε hx hadd hw`. Take `⟨L, hL⟩` from `exists_linear_lift_of_isHolTo F i P hP (m := 1) (fun z => x (z 0)) (fun z w => hadd _ _) (by`. Simplify using `only [hx]`. Conclude with `HolFibre.isHolTo_comp (isHolTo_pt C) φ)`. Establish `hv : ∀ z : ℂ, x z = F.ex i P (z • L fun _ => 1)` using `fun z => by`.

Rewrite using `[← map_smul, hL]`. Simplify using the standard rewrite rules. Establish `h1 : x 1 = 1`. Rewrite using `[← map_zero_eq_one x hadd]`. Conclude with `Over.OverMorphism.ext (by rw [hx, hx, pt_one])`.

Rewrite `h1` using `[hv, one_smul, F.ex_ker i P hP]`. Take `⟨a, ha⟩` from `h1`. Rewrite `hv` using `[← ha]`. Use `⟨a, fun j hj => ?_, hv⟩` and prove the remaining obligations. Use `set w : ℂ := (1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 with hwdef`.

Establish `key : ∀ z : ℂ, z • (w • P a - P (H.w0 • a)) ∈ P.range` using `fun z => by`. Establish `e1` using `hw z`. Rewrite `e1` using `[hv, hv, ← F.ex_lin i P hP]`. Establish `e2 : (fun k => ty k (H.w0 : E) * (z • P a) k) = z • P (H.w0 • a)`. Use function extensionality and compare the values at `k`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, hP.1]`. Expand and normalize the polynomial expressions, which then agree. Establish `e3` using `F.ex_add i P hP (z • (w • P a - P (H.w0 • a))) (z • P (H.w0 • a))`. Rewrite `e3` using `[← smul_add, sub_add_cancel, smul_smul, mul_comm z w, e1, e2]`. Conclude with `(F.ex_ker i P hP _).1 (mul_eq_right.1 e3.symm)`.

Take `⟨b, hb⟩` from `key 1`. Rewrite `hb` using `[one_smul]`. Establish `hb0 : b = 0` using `eq_zero_of_line hP (hb ▸ key)`. Rewrite `hb` using `[hb0, map_zero]`. Establish `e4` using `congrFun hb j`.

Simplify using `only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hP.1] at e4`. Establish `e5 : 2 * ty j (H.w0 : E) = 1 + ty j (H.rt : E)`. Use `congrArg (fun s : 𝓞 E => ty j (s : E)) H.two_weight_eq_one_add_root` as an intermediate fact. Simplify `this` using `[map_ofNat]`. Assume the negation of the conclusion as `hne`.

Apply `hj` to reduce the goal to its premises. Establish `e6 : w = ty j (H.w0 : E)` using `mul_right_cancel₀ hne (sub_eq_zero.1 e4.symm)`. Rewrite `e6` using `[hwdef]`. Take the linear combination `-e5 - 2 * e6`.
-/
theorem exists_pure_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (φ : C.P.A.left ⟶ Xo.univ.t.G.left) (x : ℂ → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ε : ℤˣ), (∀ z, (x z).left = C.pt z ≫ φ) → (∀ z w, x (z + w) = x z * x w) → (∀ z, x ((1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 * z) = x z ≫ Xo.univ.t.act.act H.w0) → ∃ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∀ z : ℂ, x z = F.ex i P (z • P a) := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ C i P hP φ x ε hx hadd hw
  obtain ⟨L, hL⟩ := exists_linear_lift_of_isHolTo F i P hP (m := 1) (fun z => x (z 0)) (fun z w => hadd _ _) (by
    simp only [hx]
    exact HolFibre.isHolTo_comp (isHolTo_pt C) φ)
  have hv : ∀ z : ℂ, x z = F.ex i P (z • L fun _ => 1) := fun z => by
    rw [← map_smul, hL]
    simp
  have h1 : x 1 = 1 := by
    rw [← map_zero_eq_one x hadd]
    exact Over.OverMorphism.ext (by rw [hx, hx, pt_one])
  rw [hv, one_smul, F.ex_ker i P hP] at h1
  obtain ⟨a, ha⟩ := h1
  rw [← ha] at hv
  refine ⟨a, fun j hj => ?_, hv⟩
  set w : ℂ := (1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 with hwdef
  have key : ∀ z : ℂ, z • (w • P a - P (H.w0 • a)) ∈ P.range := fun z => by
    have e1 := hw z
    rw [hv, hv, ← F.ex_lin i P hP] at e1
    have e2 : (fun k => ty k (H.w0 : E) * (z • P a) k) = z • P (H.w0 • a) := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, hP.1]
      ring
    have e3 := F.ex_add i P hP (z • (w • P a - P (H.w0 • a))) (z • P (H.w0 • a))
    rw [← smul_add, sub_add_cancel, smul_smul, mul_comm z w, e1, e2] at e3
    exact (F.ex_ker i P hP _).1 (mul_eq_right.1 e3.symm)
  obtain ⟨b, hb⟩ := key 1
  rw [one_smul] at hb
  have hb0 : b = 0 := eq_zero_of_line hP (hb ▸ key)
  rw [hb0, map_zero] at hb
  have e4 := congrFun hb j
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hP.1] at e4
  have e5 : 2 * ty j (H.w0 : E) = 1 + ty j (H.rt : E) := by
    have := congrArg (fun s : 𝓞 E => ty j (s : E)) H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  by_contra hne
  apply hj
  have e6 : w = ty j (H.w0 : E) := mul_right_cancel₀ hne (sub_eq_zero.1 e4.symm)
  rw [hwdef] at e6
  linear_combination -e5 - 2 * e6

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  (F : FamilyUnif Xo σ ty) {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P)

open GlobalTheory.ConjSplit hiding exists_lin in

/- English proof (translation)
Establish `key : ∀ a : lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ a' ∈ lat hP' (((ε : ℤ) : ℂ) * H.rt0), ∀ z : ℂ, U ≫ F.ex i P (f z • P a) = F.ex i' P' (z • P' a')`. Introduce and unpack `⟨a, ha⟩`. Take `⟨φ, -, hφ⟩` from `exists_hom_of_pureType E H D l Xo σ g ty F h₁ h₂ h₃ C i P hP ε a ha`. Establish `hx : ∀ z w, F.ex i P (f (z + w) • P a) = F.ex i P (f z • P a) * F.ex i P (f w • P a)` using `fun z w => by`. Rewrite using `[ex_congr_type F hP ε ha (hadd z w), add_smul, F.ex_add i P hP]`.

Use `exists_pure_vector E H D l Xo σ g ty F h₁ h₂ h₃ C i' P' hP' (io ≫ φ) (fun z => U ≫ F.ex i P (f z • P a)) ε (fun z => ?_) (fun z w => ?_) (fun z => ?_)` and prove the remaining obligations. Rewrite using `[← Category.assoc, hf, Category.assoc, hφ]`. Both sides reduce to the same expression. Use `show U ≫ _ = (U ≫ _) * (U ≫ _)`. Rewrite using `[hx, MonObj.comp_mul]`.

Use `show U ≫ _ = (U ≫ _) ≫ _`. Rewrite using `[Category.assoc, ← ex_smul F hP, period_w0_smul hP ha, smul_smul]`. Use `congr 1`. Establish `e0 : wC H (0, 1) = (1 + H.rt0) / 2` using `by simp [wC]`. Rewrite `hw` using `[e0]`.

Break down `Int.units_eq_one_or ε with rfl | rfl` into its components or cases. Use `ex_congr_type F hP 1 ha ?_` and prove the remaining obligations. Simplify `hw z` using `[mul_comm]`. Establish `e1` using `hx ((1 + -H.rt0) / 2 * z) ((1 + H.rt0) / 2 * z)`. Rewrite `e1` using `[ex_congr_type F hP _ ha (hw z), ← F.ex_add i P hP, ← add_smul, show (1 + -H.rt0) / 2 * z + (1 + H.rt0) / 2 * z = z by ring]`.

Establish `e2` using `(F.ex_ker i P hP ((f ((1 + -H.rt0) / 2 * z) + (1 + H.rt0) / 2 * f z - f z) • P a)).1 (by`. Establish `e3` using `F.ex_add i P hP ((f ((1 + -H.rt0) / 2 * z) + (1 + H.rt0) / 2 * f z - f z) • P a) (f z • P a)`. Rewrite `e3` using `[← add_smul, sub_add_cancel, ← e1]`. Conclude with `mul_eq_right.1 e3.symm)`. Use `ex_congr F hP ?_` and prove the remaining obligations.

Rewrite using `[← sub_smul]`. Use `e2 using 2` and compare the differences between its conclusion and the goal. Simplify using `only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `choose Φ hΦ hex using key`.

Use `⟨{ toFun := Φ, map_add' := fun a b => ?_, map_smul' := fun s a => ?_ }, hΦ, fun a z => (hex a z).symm⟩` and prove the remaining obligations. Use `eq_of_ex F hP' fun z => ?_` and prove the remaining obligations. Rewrite using `[map_add, smul_add, F.ex_add i' P' hP', ← hex, ← hex, ← hex, Submodule.coe_add, map_add, smul_add, F.ex_add i P hP, MonObj.comp_mul]`. Use `eq_of_ex F hP' fun z => ?_` and prove the remaining obligations. Rewrite using `[RingHom.id_apply, ex_smul F hP', ← hex, ← hex, Submodule.coe_smul, ex_smul F hP, Category.assoc]`.
-/
theorem exists_lin (h₁ : 1 ≤ D.p + D.q) (h₂ : σ (baseKA l).ρ = H.rt0) (h₃ : IsTypeFn H D.p D.q ty)
    (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left) {i' : Fin F.n} {P' : (F.Di i').La →+ (Fin g → ℂ)}
    (hP' : IsPeriod (F.Di i') ty P') (U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P)) (f : ℂ → ℂ)
    (hadd : ∀ z w, ∃ a, f (z + w) - (f z + f w) = wC H a)
    (hw : ∀ z, ∃ a, f (wC H (0, 1) * z) - wC H (0, 1) * f z = wC H a)
    (hf : ∀ z, C.pt z ≫ io = U.left ≫ C.pt (f z)) (ε : ℤˣ) :
    ∃ Φ : lat hP (((ε : ℤ) : ℂ) * H.rt0) →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' (((ε : ℤ) : ℂ) * H.rt0)) ∧
      ∀ a (z : ℂ), F.ex i' P' (z • P' (Φ a)) = U ≫ F.ex i P (f z • P a) := by
  have key : ∀ a : lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ a' ∈ lat hP' (((ε : ℤ) : ℂ) * H.rt0),
      ∀ z : ℂ, U ≫ F.ex i P (f z • P a) = F.ex i' P' (z • P' a') := by
    rintro ⟨a, ha⟩
    obtain ⟨φ, -, hφ⟩ := exists_hom_of_pureType E H D l Xo σ g ty F h₁ h₂ h₃ C i P hP ε a ha
    have hx : ∀ z w, F.ex i P (f (z + w) • P a) = F.ex i P (f z • P a) * F.ex i P (f w • P a) := fun z w => by
      rw [ex_congr_type F hP ε ha (hadd z w), add_smul, F.ex_add i P hP]
    refine exists_pure_vector E H D l Xo σ g ty F h₁ h₂ h₃ C i' P' hP' (io ≫ φ) (fun z => U ≫ F.ex i P (f z • P a)) ε
      (fun z => ?_) (fun z w => ?_) (fun z => ?_)
    · rw [← Category.assoc, hf, Category.assoc, hφ]; rfl
    · show U ≫ _ = (U ≫ _) * (U ≫ _)
      rw [hx, MonObj.comp_mul]
    · show U ≫ _ = (U ≫ _) ≫ _
      rw [Category.assoc, ← ex_smul F hP, period_w0_smul hP ha, smul_smul]
      congr 1
      have e0 : wC H (0, 1) = (1 + H.rt0) / 2 := by simp [wC]
      rw [e0] at hw
      rcases Int.units_eq_one_or ε with rfl | rfl
      · refine ex_congr_type F hP 1 ha ?_
        simpa [mul_comm] using hw z
      · have e1 := hx ((1 + -H.rt0) / 2 * z) ((1 + H.rt0) / 2 * z)
        rw [ex_congr_type F hP _ ha (hw z), ← F.ex_add i P hP, ← add_smul,
          show (1 + -H.rt0) / 2 * z + (1 + H.rt0) / 2 * z = z by ring] at e1
        have e2 := (F.ex_ker i P hP ((f ((1 + -H.rt0) / 2 * z) + (1 + H.rt0) / 2 * f z - f z) • P a)).1 (by
          have e3 := F.ex_add i P hP ((f ((1 + -H.rt0) / 2 * z) + (1 + H.rt0) / 2 * f z - f z) • P a) (f z • P a)
          rw [← add_smul, sub_add_cancel, ← e1] at e3
          exact mul_eq_right.1 e3.symm)
        refine ex_congr F hP ?_
        rw [← sub_smul]
        convert e2 using 2
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
        ring
  choose Φ hΦ hex using key
  refine ⟨{ toFun := Φ, map_add' := fun a b => ?_, map_smul' := fun s a => ?_ }, hΦ, fun a z => (hex a z).symm⟩
  · refine eq_of_ex F hP' fun z => ?_
    rw [map_add, smul_add, F.ex_add i' P' hP', ← hex, ← hex, ← hex, Submodule.coe_add, map_add, smul_add,
      F.ex_add i P hP, MonObj.comp_mul]
  · refine eq_of_ex F hP' fun z => ?_
    rw [RingHom.id_apply, ex_smul F hP', ← hex, ← hex, Submodule.coe_smul, ex_smul F hP, Category.assoc]

end Fam

open GlobalTheory.ConjSplit hiding exists_lin in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ g ty F h₁ h₂ h₃ τ hτ C io hio i P hP i' P' hP' hsp hu`. Take `⟨f, hadd, hw, hon, hact, hf⟩` from `exists_param C τ hτ io hio`. Set `U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P)` to `Over.homMk (spMap (τ : ℂ →+* ℂ)) hu`. Establish `hU : ∀ x y : Over.mk (F.u i P) ⟶ Xo.univ.t.G, U ≫ x = U ≫ y → x = y` using `fun x y h => Over.OverMorphism.ext (spMap_cancel τ (congrArg (fun m => m.left) h))`. Establish `key : ∀ (ε : ℤˣ) (ρ : ℂ), ((ε : ℤ) : ℂ) * H.rt0 = ρ → ∃ Φ : lat hP ρ →ₗ[𝓞 E] (F.Di i').La, (∀ a, Φ a ∈ lat hP' ρ) ∧ (∀ a, Φ a = 0 → a = 0) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ a : lat hP ρ, U ≫ F.ex i P ((n : ℂ)⁻¹ • P a) = F.ex i' P' ((n : ℂ)⁻¹ • wC H s • P' (Φ a))`.

Introduce and unpack `ε _ rfl`. Take `⟨Φ, hΦ, hex⟩` from `exists_lin F hP h₁ h₂ h₃ C io hP' U f hadd hw hf ε`. Use `⟨Φ, hΦ, fun a ha => Subtype.ext (eq_of_ex F hP fun z' => ?_), fun n s hA a => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hon z'`. Rewrite using `[← ex_congr_type F hP ε a.2 hz, ← ex_congr_type F hP ε (Submodule.coe_mem 0) hz]`.

Apply `hU` to reduce the goal to its premises. Rewrite using `[← hex, ← hex, ha, map_zero Φ]`. Rewrite using `[smul_smul, mul_comm (n : ℂ)⁻¹, ← div_eq_mul_inv, hex, ex_congr_type F hP ε a.2 (hact n s hA), one_div]`. Take `⟨Φp, hp, ip, tp⟩` from `key 1 H.rt0 (by simp)`. Take `⟨Φm, hm, im, tm⟩` from `key (-1) (-H.rt0) (by simp)`.

Establish `hc : IsCompl (lat hP H.rt0) (lat hP (-H.rt0))` using `⟨disjoint_lat hP rt0_ne_neg, codisjoint_iff.2 hsp⟩`. Establish `hd` using `Submodule.disjoint_def.1 (disjoint_lat hP (rt0_ne_neg (H := H)))`. Establish `hd'` using `Submodule.disjoint_def.1 (disjoint_lat hP' (rt0_ne_neg (H := H)))`. Establish `hdec : ∀ x, ∃ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), x = a.1 + b.1` using `fun x => by`. Take `⟨a, ha, b, hb, e⟩` from `Submodule.mem_sup.1 ((show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hsp) ▸ Submodule.mem_top (x := x))`.

Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, e.symm⟩`. Establish `hΦ : ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), LinearMap.ofIsCompl hc Φp Φm (a.1 + b.1) = Φp a + Φm b` using `fun a b => by`. Rewrite using `[map_add, LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right]`. Use `⟨LinearMap.ofIsCompl hc Φp Φm, (injective_iff_map_eq_zero _).2 fun x hx => ?_, fun x => ?_, fun x => ?_, fun n s _ hA a ha b hb => ?_⟩` and prove the remaining obligations. Take `⟨a, b, rfl⟩` from `hdec x`.

Rewrite `hx` using `[hΦ]`. Establish `e : Φp a = 0` using `hd' _ (hp a) (by rw [eq_neg_of_add_eq_zero_left hx]; exact neg_mem (hm b))`. Rewrite `hx` using `[e, zero_add]`. Rewrite using `[ip a e, im b hx]`. Simplify using the standard rewrite rules.

Take `⟨a, b, rfl⟩` from `hdec x`. Rewrite using `[hΦ, Submodule.add_mem_iff_right _ (hp a), Submodule.add_mem_iff_right _ a.2]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[im b (hd' _ h (hm b))]`.

Simplify using the standard rewrite rules. Introduce `h`. Rewrite using `[show b = 0 from Subtype.ext (hd _ h b.2)]`. Simplify using the standard rewrite rules. Take `⟨a, b, rfl⟩` from `hdec x`.

Rewrite using `[hΦ, Submodule.add_mem_iff_left _ (hm b), Submodule.add_mem_iff_left _ b.2]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[ip a (hd' _ (hp a) h)]`. Simplify using the standard rewrite rules.

Introduce `h`. Rewrite using `[show a = 0 from Subtype.ext (hd _ a.2 h)]`. Simplify using the standard rewrite rules. Establish `e` using `hΦ (wE H s • ⟨a, ha⟩) (H.bar (wE H s) • ⟨b, hb⟩)`. Rewrite `e` using `[map_smul, map_smul]`.

Establish `e' : LinearMap.ofIsCompl hc Φp Φm (wE H s • a + H.bar (wE H s) • b) = _` using `e`. Rewrite using `[e', map_add P', period_wE hP' (hp _), period_bar_wE hP' (hm _), smul_add, F.ex_add i' P' hP', ← tp n s hA, ← tm n s hA, ← MonObj.comp_mul, ← F.ex_add i P hP, ← smul_add, ← map_add]`. Both sides reduce to the same expression.
-/
theorem exists_conj_lattice_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La →ₗ[𝓞 E] (F.Di i').La, Function.Injective Φ ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h₁ h₂ h₃ τ hτ C io hio i P hP i' P' hP' hsp hu
  obtain ⟨f, hadd, hw, hon, hact, hf⟩ := exists_param C τ hτ io hio
  let U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have hU : ∀ x y : Over.mk (F.u i P) ⟶ Xo.univ.t.G, U ≫ x = U ≫ y → x = y := fun x y h =>
    Over.OverMorphism.ext (spMap_cancel τ (congrArg (fun m => m.left) h))
  have key : ∀ (ε : ℤˣ) (ρ : ℂ), ((ε : ℤ) : ℂ) * H.rt0 = ρ → ∃ Φ : lat hP ρ →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' ρ) ∧ (∀ a, Φ a = 0 → a = 0) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ a : lat hP ρ,
        U ≫ F.ex i P ((n : ℂ)⁻¹ • P a) = F.ex i' P' ((n : ℂ)⁻¹ • wC H s • P' (Φ a)) := by
    rintro ε _ rfl
    obtain ⟨Φ, hΦ, hex⟩ := exists_lin F hP h₁ h₂ h₃ C io hP' U f hadd hw hf ε
    refine ⟨Φ, hΦ, fun a ha => Subtype.ext (eq_of_ex F hP fun z' => ?_), fun n s hA a => ?_⟩
    · obtain ⟨z, hz⟩ := hon z'
      rw [← ex_congr_type F hP ε a.2 hz, ← ex_congr_type F hP ε (Submodule.coe_mem 0) hz]
      apply hU
      rw [← hex, ← hex, ha, map_zero Φ]
    · rw [smul_smul, mul_comm (n : ℂ)⁻¹, ← div_eq_mul_inv, hex, ex_congr_type F hP ε a.2 (hact n s hA), one_div]
  obtain ⟨Φp, hp, ip, tp⟩ := key 1 H.rt0 (by simp)
  obtain ⟨Φm, hm, im, tm⟩ := key (-1) (-H.rt0) (by simp)
  have hc : IsCompl (lat hP H.rt0) (lat hP (-H.rt0)) := ⟨disjoint_lat hP rt0_ne_neg, codisjoint_iff.2 hsp⟩
  have hd := Submodule.disjoint_def.1 (disjoint_lat hP (rt0_ne_neg (H := H)))
  have hd' := Submodule.disjoint_def.1 (disjoint_lat hP' (rt0_ne_neg (H := H)))
  have hdec : ∀ x, ∃ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), x = a.1 + b.1 := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 ((show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hsp) ▸
      Submodule.mem_top (x := x))
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e.symm⟩
  have hΦ : ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      LinearMap.ofIsCompl hc Φp Φm (a.1 + b.1) = Φp a + Φm b := fun a b => by
    rw [map_add, LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right]
  refine ⟨LinearMap.ofIsCompl hc Φp Φm, (injective_iff_map_eq_zero _).2 fun x hx => ?_, fun x => ?_, fun x => ?_,
    fun n s _ hA a ha b hb => ?_⟩
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ] at hx
    have e : Φp a = 0 := hd' _ (hp a) (by rw [eq_neg_of_add_eq_zero_left hx]; exact neg_mem (hm b))
    rw [e, zero_add] at hx
    rw [ip a e, im b hx]; simp
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ, Submodule.add_mem_iff_right _ (hp a), Submodule.add_mem_iff_right _ a.2]
    constructor
    · intro h
      rw [im b (hd' _ h (hm b))]; simp
    · intro h
      rw [show b = 0 from Subtype.ext (hd _ h b.2)]; simp
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ, Submodule.add_mem_iff_left _ (hm b), Submodule.add_mem_iff_left _ b.2]
    constructor
    · intro h
      rw [ip a (hd' _ (hp a) h)]; simp
    · intro h
      rw [show a = 0 from Subtype.ext (hd _ a.2 h)]; simp
  · have e := hΦ (wE H s • ⟨a, ha⟩) (H.bar (wE H s) • ⟨b, hb⟩)
    rw [map_smul, map_smul] at e
    have e' : LinearMap.ofIsCompl hc Φp Φm (wE H s • a + H.bar (wE H s) • b) = _ := e
    rw [e', map_add P', period_wE hP' (hp _), period_bar_wE hP' (hm _), smul_add, F.ex_add i' P' hP', ← tp n s hA,
      ← tm n s hA, ← MonObj.comp_mul, ← F.ex_add i P hP, ← smul_add, ← map_add]
    rfl

open GlobalTheory.CompRat.ConjIsometry in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ g ty F h1 hσ hty τ hτ C io hio i P hP i' P' hP' hs hu`. Take `⟨Φ, hinj, hp, hm, hact⟩` from `exists_conj_lattice_map E H D l Xo σ g ty F h1 hσ hty τ hτ C io hio i P hP i' P' hP' hs hu`. Establish `hiso : ∀ x y, (F.Di i').EF (Φ x) (Φ y) = (F.Di i).EF x y`. Introduce `x y`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := x)))`.

Take `⟨a', ha', b', hb', rfl⟩` from `Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := y)))`. Establish `key : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b')`. Introduce `n hn`. Take `⟨⟨s, hs⟩, -⟩` from `GlobalTheory.CompRat.Acts.main E H C τ hτ io hio n hn`. Establish `k` using `conj_pairing F τ hP hP' hu hn (hact n s hn hs a ha b hb) (hact n s hn hs a' ha' b' hb')`.

Establish `hN` using `GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm E H C τ hτ io n s hn hs`. Establish `hb1` using `bar_mul_wE (H := H) s`. Generalize the expression as in `s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = N at hN hb1`. Establish `hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = N` using `by rw [bar_bar, mul_comm, hb1]`. Establish `o : ∀ u ∈ lat hP H.rt0, ∀ v ∈ lat hP (-H.rt0), (F.Di i').EF (Φ u) (Φ v) = 0 ∧ (F.Di i').EF (Φ v) (Φ u) = 0` using `fun u hu v hv => by`.

Use `form_lat_eq_zero hP' ((hp u).2 hu) ((hm v).2 hv)` as an intermediate fact. Conclude with `⟨this, by rw [form_skew, this, neg_zero]⟩`. Establish `e : (F.Di i').EF (Φ (wE H s • a + H.bar (wE H s) • b)) (Φ (wE H s • a' + H.bar (wE H s) • b')) = N * (F.Di i').EF (Φ (a + b)) (Φ (a' + b'))`. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[(o _ (Submodule.smul_mem _ _ ha) _ (Submodule.smul_mem _ _ hb')).1, (o _ (Submodule.smul_mem _ _ ha') _ (Submodule.smul_mem _ _ hb)).2, (o _ ha _ hb').1, (o _ ha' _ hb).2]`.

Simplify using `only [map_smul Φ]`. Rewrite using `[form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `k` using `[e, ← mul_neg, zpow_mul, ← hN]`. Establish `prim : IsPrimitiveRoot (τ (zeta n)) n` using `(Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective`.

Establish `ne : τ (zeta n) ≠ 0` using `prim.ne_zero hn.ne'`. Rewrite using `[← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]`. Use `key (((F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b')).natAbs + 1) (by omega)` as an intermediate fact. Conclude with `sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))`. Apply the tactic sequence `have hsurj := surjective_of_isometry (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso`.

Conclude with `⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, hp, hm, hact⟩`.
-/
theorem exists_isometry_of_conj_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty τ hτ C io hio i P hP i' P' hP' hs hu
  obtain ⟨Φ, hinj, hp, hm, hact⟩ :=
    exists_conj_lattice_map E H D l Xo σ g ty F h1 hσ hty τ hτ C io hio i P hP i' P' hP' hs hu
  have hiso : ∀ x y, (F.Di i').EF (Φ x) (Φ y) = (F.Di i).EF x y := by
    intro x y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := x)))
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := y)))
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b') := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.CompRat.Acts.main E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (hact n s hn hs a ha b hb) (hact n s hn hs a' ha' b' hb')
      have hN := GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = N at hN hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = N := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP H.rt0, ∀ v ∈ lat hP (-H.rt0),
          (F.Di i').EF (Φ u) (Φ v) = 0 ∧ (F.Di i').EF (Φ v) (Φ u) = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' ((hp u).2 hu) ((hm v).2 hv)
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φ (wE H s • a + H.bar (wE H s) • b)) (Φ (wE H s • a' + H.bar (wE H s) • b')) =
          N * (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) := by
        simp only [map_add, LinearMap.add_apply]
        rw [(o _ (Submodule.smul_mem _ _ ha) _ (Submodule.smul_mem _ _ hb')).1,
          (o _ (Submodule.smul_mem _ _ ha') _ (Submodule.smul_mem _ _ hb)).2, (o _ ha _ hb').1, (o _ ha' _ hb).2]
        simp only [map_smul Φ]
        rw [form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hN] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b')).natAbs + 1) (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, hp, hm, hact⟩

end GlobalTheory.AnyLevel

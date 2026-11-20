import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompactStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSpace

open GlobalTheory.WeilVacMove

variable {D : D7} {S T : HSp D}

/- English proof (translation)
Use `⟨Submodule.fg_span (Set.finite_range _), ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← (Pi.basisFun E (Fin r)).span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.subset_span ⟨a, by simp⟩`.
-/
theorem stdL_full (E : Type) [Field E] [NumberField E] (r : ℕ) :
    (stdL E r).FG ∧ Submodule.span E (stdL E r : Set (Fin r → E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin r)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

/- English proof (translation)
Rewrite using `[map_sub, ha, hb, sub_zero]`.
-/
theorem map_sub_eq_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {a b : A} (ha : φ a = 0) (hb : φ b = 0) :
    φ (a - b) = 0 := by rw [map_sub, ha, hb, sub_zero]

/- English proof (translation)
Rewrite using `[map_nsmul, ha, smul_zero]`.
-/
theorem map_nsmul_eq_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {a : A} (ha : φ a = 0) (N : ℕ) :
    φ (N • a) = 0 := by rw [map_nsmul, ha, smul_zero]

/- English proof (translation)
Use extensionality with `i j`. Establish `h1 : finPart D (u i j) = 0` using `congrFun (congrFun hu i) j`. Establish `h2 : finPart D (v i j) = 0` using `congrFun (congrFun hv i) j`. Conclude with `map_sub_eq_zero (finPart D) h1 h2`.
-/
theorem isRealPt_sub {u v : WO S T} (hu : IsRealPt u) (hv : IsRealPt v) : IsRealPt (u - v) := by
  ext i j
  have h1 : finPart D (u i j) = 0 := congrFun (congrFun hu i) j
  have h2 : finPart D (v i j) = 0 := congrFun (congrFun hv i) j
  exact map_sub_eq_zero (finPart D) h1 h2

/- English proof (translation)
Use extensionality with `i j`. Establish `h1 : infPart D (u i j) = 0` using `congrFun (congrFun hu i) j`. Conclude with `map_nsmul_eq_zero (infPart D) h1 N`.
-/
theorem isFinPt_nsmul {u : WO S T} (hu : IsFinPt u) (N : ℕ) : IsFinPt (N • u) := by
  ext i j
  have h1 : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  exact map_nsmul_eq_zero (infPart D) h1 N

/- English proof (translation)
Take `⟨R, -, -, -, h1, -, h2, -⟩` from `GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C`. Conclude with `⟨_, _, h2 w, (h1 _).1, (sub_add_cancel _ _).symm⟩`.
-/
theorem exists_fin_add_real (C : Ctx S T) (w : WO S T) : ∃ u v, IsFinPt u ∧ IsRealPt v ∧ w = u + v := by
  obtain ⟨R, -, -, -, h1, -, h2, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  exact ⟨_, _, h2 w, (h1 _).1, (sub_add_cancel _ _).symm⟩

/- English proof (translation)
Take `⟨u, v, hu, hv, rfl⟩` from `exists_fin_add_real C w`. Establish `h` using `GlobalTheory.FinTranslate.isTheta_heisO_fin C.std.1 hu (isTheta_heisO_real C.std hv hf)`. Rewrite `h` using `[heisO_heisO, (symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one, one_smul]`. Then use the resulting hypothesis.
-/
theorem isTh_rho (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (w : WO S T) : C.IsTh (C.rho w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real C w
  have h := GlobalTheory.FinTranslate.isTheta_heisO_fin C.std.1 hu (isTheta_heisO_real C.std hv hf)
  rwa [heisO_heisO, (symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one, one_smul] at h

/- English proof (translation)
Take `⟨-, -, h3, h4, -⟩` from `GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩`. Take `⟨U, hU, h⟩` from `hf.level`. Take `⟨N, hN, hNU⟩` from `h4 U hU`. Conclude with `⟨N, hN, fun u hu => h _ (hNU u hu) (isFinPt_nsmul (h3 u hu).1 N)⟩`.
-/
theorem exists_level (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  obtain ⟨U, hU, h⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := h4 U hU
  exact ⟨N, hN, fun u hu => h _ (hNU u hu) (isFinPt_nsmul (h3 u hu).1 N)⟩

/- English proof (translation)
Take `⟨h1, -, h3, -⟩` from `GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩`. Establish `h7` using `(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.2`. Take `⟨N, hN, hl⟩` from `exists_level C hf`. Use function extensionality and compare the values at `w`. Take `⟨u, v, hu, hv, rfl⟩` from `exists_fin_add_real C w`.

Take `⟨y, hy⟩` from `h1 u hu`. Take `⟨-, hy2⟩` from `h3 _ hy`. Take `⟨y', -, u', hu', e⟩` from `hy2 N hN`. Establish `hr` using `isRealPt_sub hv (h7 (y + y')).2.2.1`. Establish `e1 : u + v = ratW T S (y + y')ᵀ + ((v - (ratW T S (y + y')ᵀ - finW S T (y + y'))) + N • u')`.

Rewrite using `[(h7 y).2.2.2 y', sub_eq_iff_eq_add.1 e]`. Normalize the expressions using the abelian group laws. Establish `e2` using `congrFun (hl u' hu') (v - (ratW T S (y + y')ᵀ - finW S T (y + y')))`. Rewrite `e2` using `[h0 _ hr]`. Unfold `Ctx.rho heisO at e2`.

Rewrite `e2` using `[(symplOH_fin_real S T _ _ (isFinPt_nsmul (h3 u' hu').1 N) hr).2, AddChar.map_zero_eq_one, one_mul]`. Rewrite using `[e1, hf.quasi, e2, mul_zero, Pi.zero_apply]`.
-/
theorem eq_zero_of_real (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (h0 : ∀ w, IsRealPt w → f w = 0) :
    f = 0 := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have h7 := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.2
  obtain ⟨N, hN, hl⟩ := exists_level C hf
  funext w
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real C w
  obtain ⟨y, hy⟩ := h1 u hu
  obtain ⟨-, hy2⟩ := h3 _ hy
  obtain ⟨y', -, u', hu', e⟩ := hy2 N hN
  have hr := isRealPt_sub hv (h7 (y + y')).2.2.1
  have e1 : u + v = ratW T S (y + y')ᵀ + ((v - (ratW T S (y + y')ᵀ - finW S T (y + y'))) + N • u') := by
    rw [(h7 y).2.2.2 y', sub_eq_iff_eq_add.1 e]
    abel
  have e2 := congrFun (hl u' hu') (v - (ratW T S (y + y')ᵀ - finW S T (y + y')))
  rw [h0 _ hr] at e2
  unfold Ctx.rho heisO at e2
  rw [(symplOH_fin_real S T _ _ (isFinPt_nsmul (h3 u' hu').1 N) hr).2, AddChar.map_zero_eq_one, one_mul] at e2
  rw [e1, hf.quasi, e2, mul_zero, Pi.zero_apply]

/- English proof (translation)
Take `⟨-, h2, -, -, -, -, -, h7⟩` from `GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C`. Take `⟨-, -, -, hadd, -, -, -, hfin, -⟩` from `GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C`. Take `⟨a1, a2, a3, -⟩` from `h7 y`. Use `set z := ratW T S yᵀ - finW S T y with hz`. Establish `hr : ratW T S yᵀ = finW S T y + z` using `by rw [hz]; abel`.

Establish `hp : C.realPt z = embR C.X y`. Rewrite using `[← a1, hr, hadd, hfin _ a2, zero_add]`. Establish `e1 : w + finW S T y = ratW T S yᵀ + (w - z)` using `by rw [hz]; abel`. Establish `hzz : symplOH S T z z = 0`. Unfold `symplOH`.

Rewrite using `[(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.1, mul_zero]`. Establish `e2 : -symplOH S T (ratW T S yᵀ) (w - z) = symplOH S T w z`. Establish `e3 : symplOH S T z w = symplOH S T z (w - z) + symplOH S T z z`. Rewrite using `[← symplOH_add_right, sub_add_cancel]`. Rewrite using `[hr, symplOH_add_left, (symplOH_fin_real S T _ _ a2 (isRealPt_sub hw a3)).1, zero_add, symplOH_skew S T z w, e3, hzz, add_zero]`.

Unfold `Ctx.rho heisO`. Rewrite using `[(symplOH_fin_real S T _ _ a2 hw).2, AddChar.map_zero_eq_one, one_mul, e1, hf.quasi, e2, h2 w z hw a3, hp]`.
-/
theorem rho_finW (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
    (w : WO S T) (hw : IsRealPt w) : C.rho (finW S T y) f w =
      cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y)) := by
  obtain ⟨-, h2, -, -, -, -, -, h7⟩ := GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C
  obtain ⟨-, -, -, hadd, -, -, -, hfin, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  obtain ⟨a1, a2, a3, -⟩ := h7 y
  set z := ratW T S yᵀ - finW S T y with hz
  have hr : ratW T S yᵀ = finW S T y + z := by rw [hz]; abel
  have hp : C.realPt z = embR C.X y := by
    rw [← a1, hr, hadd, hfin _ a2, zero_add]
  have e1 : w + finW S T y = ratW T S yᵀ + (w - z) := by rw [hz]; abel
  have hzz : symplOH S T z z = 0 := by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.1, mul_zero]
  have e2 : -symplOH S T (ratW T S yᵀ) (w - z) = symplOH S T w z := by
    have e3 : symplOH S T z w = symplOH S T z (w - z) + symplOH S T z z := by
      rw [← symplOH_add_right, sub_add_cancel]
    rw [hr, symplOH_add_left, (symplOH_fin_real S T _ _ a2 (isRealPt_sub hw a3)).1, zero_add, symplOH_skew S T z w,
      e3, hzz, add_zero]
  unfold Ctx.rho heisO
  rw [(symplOH_fin_real S T _ _ a2 hw).2, AddChar.map_zero_eq_one, one_mul, e1, hf.quasi, e2, h2 w z hw a3, hp]

/- English proof (translation)
Take `⟨γ', -, e⟩` from `h`. Conclude with `⟨γ'.1, (congrArg Units.val e).symm⟩`.
-/
theorem exists_mt_eq (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) :
    ∃ m : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = m.map (incA D) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

/- English proof (translation)
Establish `hs : ∀ w w', symplOH S T (actO S T γ γ' w) (actO S T γ γ' w') = symplOH S T w w'` using `fun w w' => by`. Unfold `symplOH`. Rewrite using `[(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.1]`. Take `⟨R, -, -, -, -, -, -, -, -, hact⟩` from `GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C`. Set `A : WO S T →+ WO S T` to `AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')`.

Establish `hA : Continuous (actO S T γ γ')` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Use `⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `exists_mt_eq S ((GQ S).inv_mem hγ)`. Take `⟨m', hm'⟩` from `exists_mt_eq T hγ'`. Establish `e : actO S T γ γ' (ratW T S x) = ratW T S (m' * x * m)`.

Unfold `actO ratW`. Rewrite using `[hm, hm', Matrix.map_mul, Matrix.map_mul]`. Rewrite using `[actO_add, ← hs, e, hf.quasi]`. Take `⟨U, hU, h⟩` from `hf.level`. Use `⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `w`. Establish `e` using `congrFun (h _ hu ((hact γ γ' u).2.1 h0)) (actO S T γ γ' w)`. Unfold `heisO at e ⊢`. Rewrite using `[← e, ← hs w u]`. Conclude with `congrArg (fun x => _ * f x) (actO_add γ γ' w u)`.

Use `hf.smooth k (A.comp L) (hA.comp h1) (fun t => (hact γ γ' (L t)).1 (h2 t)) (actO S T γ γ' w)` as an intermediate fact. Simplify using `only [actO_add]`. Conclude with `this`.
-/
theorem isTh_actO (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T}
    (hγ' : γ' ∈ GQ T) : C.IsTh fun w => f (actO S T γ γ' w) := by
  have hs : ∀ w w', symplOH S T (actO S T γ γ' w) (actO S T γ γ' w') = symplOH S T w w' := fun w w' => by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.1]
  obtain ⟨R, -, -, -, -, -, -, -, -, hact⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  let A : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')
  have hA : Continuous (actO S T γ γ') := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨m, hm⟩ := exists_mt_eq S ((GQ S).inv_mem hγ)
    obtain ⟨m', hm'⟩ := exists_mt_eq T hγ'
    have e : actO S T γ γ' (ratW T S x) = ratW T S (m' * x * m) := by
      unfold actO ratW
      rw [hm, hm', Matrix.map_mul, Matrix.map_mul]
    rw [actO_add, ← hs, e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu ((hact γ γ' u).2.1 h0)) (actO S T γ γ' w)
    unfold heisO at e ⊢
    rw [← e, ← hs w u]
    exact congrArg (fun x => _ * f x) (actO_add γ γ' w u)
  · have := hf.smooth k (A.comp L) (hA.comp h1) (fun t => (hact γ γ' (L t)).1 (h2 t)) (actO S T γ γ' w)
    simp only [actO_add]
    exact this

/- English proof (translation)
Introduce `D S T C`. Use `⟨isTheta_zero, fun f f' hf hf' => ⟨isTheta_add hf hf', fun h => ?_⟩, fun f hf => ⟨fun a => isTheta_smul a hf, isTh_rho C hf, fun w w' => heisO_heisO _ _ _ _ _ _, rho_finW C hf, fun γ hγ γ' hγ' => isTh_actO C hf hγ hγ', exists_level C hf⟩⟩` and prove the remaining obligations. Conclude with `sub_eq_zero.1 (eq_zero_of_real C (isTheta_sub hf hf') fun w hw => sub_eq_zero.2 (h w hw))`.
-/
theorem theta_space_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), C.IsTh 0 ∧ (∀ f f', C.IsTh f → C.IsTh f' → C.IsTh (f + f') ∧ ((∀ w, IsRealPt w → f w = f' w) → f = f')) ∧ ∀ f, C.IsTh f → (∀ a : ℂ, C.IsTh (a • f)) ∧ (∀ w, C.IsTh (C.rho w f)) ∧ (∀ w w', C.rho w (C.rho w' f) = C.ψ (symplOH S T w w') • C.rho (w + w') f) ∧ (∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) w, IsRealPt w → C.rho (finW S T y) f w = cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y))) ∧ (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, C.IsTh fun w => f (actO S T γ γ' w)) ∧ ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  intro D S T C
  refine ⟨isTheta_zero, fun f f' hf hf' => ⟨isTheta_add hf hf', fun h => ?_⟩, fun f hf =>
    ⟨fun a => isTheta_smul a hf, isTh_rho C hf, fun w w' => heisO_heisO _ _ _ _ _ _, rho_finW C hf,
      fun γ hγ γ' hγ' => isTh_actO C hf hγ hγ', exists_level C hf⟩⟩
  exact sub_eq_zero.1 (eq_zero_of_real C (isTheta_sub hf hf') fun w hw => sub_eq_zero.2 (h w hw))

end GlobalTheory.ThetaSpace

end

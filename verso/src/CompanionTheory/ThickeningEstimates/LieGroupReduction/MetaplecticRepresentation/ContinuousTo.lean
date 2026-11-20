import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousOm
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real ContDiff

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

namespace MpA

/- English proof (translation)
The claim follows from `SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top`.
-/
theorem dense_sch : DenseRange (schwartzToL2 l) :=
  SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top

def ext (V : (Sch l →L[ℂ] Sch l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) : L2 l ≃ₗᵢ[ℂ] L2 l :=
  (ContinuousLinearEquiv.unitsEquiv ℂ (Sch l) V).toLinearEquiv.extendOfIsometry
    (schwartzToL2 l).toLinearMap (schwartzToL2 l).toLinearMap dense_sch dense_sch fun f => hn f

/- English proof (translation)
The claim follows from `LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f`.
-/
theorem ext_sch (V : (Sch l →L[ℂ] Sch l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) (f : Sch l) :
    ext V hn (schwartzToL2 l f) = schwartzToL2 l (V.1 f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

/- English proof (translation)
The claim follows from `Subtype.ext (p := (· ∈ sub l)) (Prod.ext h1 (Prod.ext h2 (Units.ext h3)))`.
-/
theorem G_ext {g h : G l} (h1 : pr g = pr h) (h2 : om g = om h) (h3 : omS g = omS h) : g = h :=
  Subtype.ext (p := (· ∈ sub l)) (Prod.ext h1 (Prod.ext h2 (Units.ext h3)))

/- English proof (translation)
The claim follows from `continuous_induced_rng.2 (h1.prodMk (continuous_pi h2))`.
-/
theorem continuous_to {X : Type} [TopologicalSpace X] {F : X → G l} (h1 : Continuous fun x => pr (F x))
    (h2 : ∀ f, Continuous fun x => om (F x) f) : Continuous F :=
  continuous_induced_rng.2 (h1.prodMk (continuous_pi h2))

/- English proof (translation)
The claim follows from `continuous_induced_rng.2 ((continuous_subtype_val.comp ha).mul (continuous_subtype_val.comp hb))`.
-/
theorem sp_mul {X : Type} [TopologicalSpace X] {a b : X → Sp l} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => a x * b x :=
  continuous_induced_rng.2 ((continuous_subtype_val.comp ha).mul (continuous_subtype_val.comp hb))

/- English proof (translation)
Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Use `show Continuous fun x => -Matrix.J l ℝ * ((a x : Mat l))ᵀ * Matrix.J l ℝ`. Conclude with `(continuous_const.mul (continuous_subtype_val.comp ha).matrix_transpose).mul continuous_const`.
-/
theorem sp_inv {X : Type} [TopologicalSpace X] {a : X → Sp l} (ha : Continuous a) :
    Continuous fun x => (a x)⁻¹ := by
  refine continuous_induced_rng.2 ?_
  show Continuous fun x => -Matrix.J l ℝ * ((a x : Mat l))ᵀ * Matrix.J l ℝ
  exact (continuous_const.mul (continuous_subtype_val.comp ha).matrix_transpose).mul continuous_const

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun q => ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]`. Establish `h1 : Continuous fun p : G l × L2 l => ‖p.2 - q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖` using `(continuous_snd.sub continuous_const).norm.add (((continuous_om q.2).comp continuous_fst).sub continuous_const).norm`. Establish `h2` using `h1.tendsto q`. Simplify using `only [sub_self, norm_zero, add_zero] at h2`.

Use `squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) h2` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sub_add_sub_cancel]`. Use `_ ≤ ‖om p.1 p.2 - om p.1 q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ := norm_add_le _ _`. Use `_ = ‖p.2 - q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ := by rw [← map_sub, LinearIsometryEquiv.norm_map]`.
-/
theorem om_cont2 : Continuous fun p : G l × L2 l => om p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun q => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Continuous fun p : G l × L2 l => ‖p.2 - q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ :=
    (continuous_snd.sub continuous_const).norm.add (((continuous_om q.2).comp continuous_fst).sub continuous_const).norm
  have h2 := h1.tendsto q
  simp only [sub_self, norm_zero, add_zero] at h2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) h2
  calc ‖om p.1 p.2 - om q.1 q.2‖ = ‖(om p.1 p.2 - om p.1 q.2) + (om p.1 q.2 - om q.1 q.2)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖om p.1 p.2 - om p.1 q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ := norm_add_le _ _
    _ = ‖p.2 - q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ := by rw [← map_sub, LinearIsometryEquiv.norm_map]

/- English proof (translation)
Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem om_mul (g h : G l) (f : L2 l) : om (g * h) f = om g (om h f) := by
  rw [map_mul]; rfl

abbrev gs (l : Type) [Fintype l] : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2) (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x` using `((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)`. Establish `h2` using `(ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp`. Establish `e : ⇑(gs l) = (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2)`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules.

Rewrite using `[e, h2.fderiv]`. Simplify using `[EuclideanSpace.inner_single_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_gs (j : l) (x : EuclideanSpace ℝ l) :
    fderiv ℝ (⇑(gs l)) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * gs l x = 0 := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2)
      (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x :=
    ((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)
  have h2 := (ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp
  have e : ⇑(gs l) = (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2) := by
    funext y; simp
  rw [e, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

/- English proof (translation)
Introduce `j` and use `by have e1 : ((1 : Sp l) : Mat l) = 1 := rfl rw [e1, one_mulVec, one_mulVec] ext x rw [SchwartzMap.smul_apply, dRho_single_inr, dRho_single_inl, lineDerivOp_apply_eq_fderiv, smul_eq_mul] linear_combination fderiv_gs j x - (2 * π * (x j : ℂ) * gs l x) * I_sq`.
-/
theorem ann_gs : Ann (1 : Sp l).1 (gs l) := fun j => by
  have e1 : ((1 : Sp l) : Mat l) = 1 := rfl
  rw [e1, one_mulVec, one_mulVec]
  ext x
  rw [SchwartzMap.smul_apply, dRho_single_inr, dRho_single_inl, lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  linear_combination fderiv_gs j x - (2 * π * (x j : ℂ) * gs l x) * I_sq

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem gs_zero : gs l 0 = 1 := by simp

/- English proof (translation)
Establish `h : upperParabolic (1 : Mat l) = 1`. Use extensionality with `a b`. Apply the tactic sequence `by_cases hab : a = b <;> simp [upperParabolic, Matrix.one_apply, hab]`. Rewrite using `[dd, h, det_one]`.
-/
theorem dd_one : dd (1 : Mat l) = 1 := by
  have h : upperParabolic (1 : Mat l) = 1 := by
    ext a b
    by_cases hab : a = b <;> simp [upperParabolic, Matrix.one_apply, hab]
  rw [dd, h, det_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun f => by simp, fun w f => by simp, fun w f => by simp, fun s' f _ => by simp⟩`.
-/
theorem eps_mem : Mem ((1, LinearIsometryEquiv.neg ℂ, -1) : Amb l) :=
  ⟨fun f => by simp, fun w f => by simp, fun w f => by simp, fun s' f _ => by simp⟩

def eps : G l := ⟨((1, LinearIsometryEquiv.neg ℂ, -1) : Amb l), eps_mem⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem om_eps (f : L2 l) : om (eps : G l) f = -f := rfl

/- English proof (translation)
Use `show (((-1 : (Sch l →L[ℂ] Sch l)ˣ) : Sch l →L[ℂ] Sch l)) f = -f`. Simplify using the standard rewrite rules.
-/
theorem omS_eps (f : Sch l) : omS (eps : G l) f = -f := by
  show (((-1 : (Sch l →L[ℂ] Sch l)ˣ) : Sch l →L[ℂ] Sch l)) f = -f
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_eps : pr (eps : G l) = 1 := rfl

/- English proof (translation)
Introduce `h`. Take `⟨φ, hφ⟩` from `exists_ne_zero (0 : EuclideanSpace ℝ l)`. Establish `h1 : omS (eps : G l) φ = omS (1 : G l) φ` using `by rw [h]`. Rewrite `h1` using `[omS_eps, map_one, ContinuousLinearMap.one_apply]`. Establish `h2 : -φ 0 = φ 0`.

Use `congrArg (fun u : Sch l => u 0) h1` as an intermediate fact. Simplify using `using this`. Conclude with `hφ (by linear_combination (-1 / 2 : ℂ) * h2)`.
-/
theorem eps_ne : (eps : G l) ≠ 1 := by
  intro h
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have h1 : omS (eps : G l) φ = omS (1 : G l) φ := by rw [h]
  rw [omS_eps, map_one, ContinuousLinearMap.one_apply] at h1
  have h2 : -φ 0 = φ 0 := by
    have := congrArg (fun u : Sch l => u 0) h1
    simpa using this
  exact hφ (by linear_combination (-1 / 2 : ℂ) * h2)

/- English proof (translation)
Use `dense_sch.induction_on (p := fun F => om g F = c • F) F (isClosed_eq (om g).continuous (continuous_const_smul c)) fun f => ?_` and prove the remaining obligations. Rewrite using `[om_sch, hc, map_smul]`.
-/
theorem om_of_omS {g : G l} {c : ℂ} (hc : ∀ f, omS g f = c • f) (F : L2 l) : om g F = c • F := by
  refine dense_sch.induction_on (p := fun F => om g F = c • F) F
    (isClosed_eq (om g).continuous (continuous_const_smul c)) fun f => ?_
  rw [om_sch, hc, map_smul]

end MpA

open MpA

/- English proof (translation)
Introduce `s U hU hI hN`. Take `⟨V, rfl⟩` from `hU`. Establish `hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖` using `fun f => hI.norm f`. Establish `hsurj : Function.Surjective ⇑(V : Sch l →L[ℂ] Sch l)` using `fun f => ⟨V⁻¹.1 f, by show (V.1 * V⁻¹.1) f = f`. Rewrite using `[V.mul_inv]`.

Use the proof step `rfl⟩`. Establish `hI' : Impl (⇑(Matrix.mulVecLin s.1)) (V : Sch l →L[ℂ] Sch l).toLinearMap` using `hI`. Establish `hd : ∀ w f, V.1 (dRho w f) = dRho (s.1 *ᵥ w) (V.1 f)` using `fun w f => hI'.dRho hsurj w f`. Use `set u := ext V hn with hu`. Establish `hc : ∀ f, u (schwartzToL2 l f) = schwartzToL2 l (V.1 f)` using `fun f => ext_sch V hn f`.

Establish `hrho : ∀ w F, u (rho w F) = rho (s.1 *ᵥ w) (u F)` using `fun w F => by`. Use `dense_sch.induction_on (p := fun F => u (rho w F) = rho (s.1 *ᵥ w) (u F)) F (isClosed_eq (u.continuous.comp (rho w).continuous) ((rho _).continuous.comp u.continuous)) fun f => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `exists_rho w f`. Establish `hg'` using `hI.impl w f g hg`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[schwartzToL2_apply, schwartzToL2_apply]`. Conclude with `toLp_rho hg'`. Use `_ = rho (s.1 *ᵥ w) (u (schwartzToL2 l f)) := by rw [hc]`. Establish `hm : Mem ((s, u, V) : Amb l)` using `⟨hc, hrho, hd, hN⟩`. Conclude with `⟨(⟨((s, u, V) : Amb l), hm⟩ : sub l), rfl, rfl⟩`.
-/
theorem mkElt : MkElt l := by
  intro s U hU hI hN
  obtain ⟨V, rfl⟩ := hU
  have hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖ := fun f => hI.norm f
  have hsurj : Function.Surjective ⇑(V : Sch l →L[ℂ] Sch l) := fun f => ⟨V⁻¹.1 f, by
    show (V.1 * V⁻¹.1) f = f
    rw [V.mul_inv]; rfl⟩
  have hI' : Impl (⇑(Matrix.mulVecLin s.1)) (V : Sch l →L[ℂ] Sch l).toLinearMap := hI
  have hd : ∀ w f, V.1 (dRho w f) = dRho (s.1 *ᵥ w) (V.1 f) := fun w f => hI'.dRho hsurj w f
  set u := ext V hn with hu
  have hc : ∀ f, u (schwartzToL2 l f) = schwartzToL2 l (V.1 f) := fun f => ext_sch V hn f
  have hrho : ∀ w F, u (rho w F) = rho (s.1 *ᵥ w) (u F) := fun w F => by
    refine dense_sch.induction_on (p := fun F => u (rho w F) = rho (s.1 *ᵥ w) (u F)) F
      (isClosed_eq (u.continuous.comp (rho w).continuous) ((rho _).continuous.comp u.continuous)) fun f => ?_
    obtain ⟨g, hg⟩ := exists_rho w f
    have hg' := hI.impl w f g hg
    calc u (rho w (schwartzToL2 l f)) = u (schwartzToL2 l g) := by rw [schwartzToL2_apply, schwartzToL2_apply, toLp_rho hg]
      _ = schwartzToL2 l (V.1 g) := hc g
      _ = rho (s.1 *ᵥ w) (schwartzToL2 l (V.1 f)) := by
        rw [schwartzToL2_apply, schwartzToL2_apply]; exact toLp_rho hg'
      _ = rho (s.1 *ᵥ w) (u (schwartzToL2 l f)) := by rw [hc]
  have hm : Mem ((s, u, V) : Amb l) := ⟨hc, hrho, hd, hN⟩
  exact ⟨(⟨((s, u, V) : Amb l), hm⟩ : sub l), rfl, rfl⟩

/- English proof (translation)
Establish `hm : ContinuousMul (G l)` using `⟨continuous_to (by`. Simplify using `only [map_mul]`. Conclude with `sp_mul (continuous_pr.comp continuous_fst) (continuous_pr.comp continuous_snd)) fun f => by`. Simplify using `only [om_mul]`. Conclude with `om_cont2.comp (continuous_fst.prodMk ((continuous_om f).comp continuous_snd))⟩`.

Establish `hi : ContinuousInv (G l)` using `⟨continuous_to (by`. Simplify using `only [map_inv]`. Conclude with `sp_inv continuous_pr) fun f => by`. Use `continuous_iff_continuousAt.2 fun g0 => ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]`.

Take `⟨v, hv⟩ : ∃ v, om g0⁻¹ f = v` from `⟨_, rfl⟩`. Establish `hv0 : om g0 v = f`. Rewrite using `[← hv, ← om_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Establish `key : ∀ g : G l, ‖f - om g v‖ = ‖om g⁻¹ f - v‖` using `fun g => by`.

Rewrite using `[← LinearIsometryEquiv.norm_map (om g) (om g⁻¹ f - v), map_sub, ← om_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Establish `hc : Continuous fun g : G l => ‖f - om g v‖` using `(continuous_const.sub (continuous_om v)).norm`. Establish `h0` using `hc.tendsto g0`. Rewrite `h0` using `[hv0, sub_self, norm_zero]`.

Rewrite using `[hv]`. Conclude with `h0.congr key⟩`. Conclude with `{ toContinuousMul := hm, toContinuousInv := hi }`.
-/
theorem topG : TopG l := by
  have hm : ContinuousMul (G l) := ⟨continuous_to (by
      simp only [map_mul]
      exact sp_mul (continuous_pr.comp continuous_fst) (continuous_pr.comp continuous_snd)) fun f => by
      simp only [om_mul]
      exact om_cont2.comp (continuous_fst.prodMk ((continuous_om f).comp continuous_snd))⟩
  have hi : ContinuousInv (G l) := ⟨continuous_to (by
      simp only [map_inv]
      exact sp_inv continuous_pr) fun f => by
      refine continuous_iff_continuousAt.2 fun g0 => ?_
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      obtain ⟨v, hv⟩ : ∃ v, om g0⁻¹ f = v := ⟨_, rfl⟩
      have hv0 : om g0 v = f := by
        rw [← hv, ← om_mul, mul_inv_cancel, map_one]; rfl
      have key : ∀ g : G l, ‖f - om g v‖ = ‖om g⁻¹ f - v‖ := fun g => by
        rw [← LinearIsometryEquiv.norm_map (om g) (om g⁻¹ f - v), map_sub, ← om_mul, mul_inv_cancel, map_one]
        rfl
      have hc : Continuous fun g : G l => ‖f - om g v‖ := (continuous_const.sub (continuous_om v)).norm
      have h0 := hc.tendsto g0
      rw [hv0, sub_self, norm_zero] at h0
      rw [hv]
      exact h0.congr key⟩
  exact { toContinuousMul := hm, toContinuousInv := hi }

/- English proof (translation)
Use `⟨eps, eps_ne, fun g => ⟨fun hg => ?_, ?_⟩, om_eps⟩` and prove the remaining obligations. Establish `hsurj : Function.Surjective (omS g)` using `fun f => ⟨omS g⁻¹ f, by show (omS g * omS g⁻¹) f = f`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Use the proof step `rfl⟩`. Establish `hpg : ((pr g : Sp l) : Mat l) = 1` using `by rw [hg]; rfl`.

Establish `hI : Impl id (omS g).toLinearMap`. Use `⟨fun f => ?_, fun w f k hk => ?_⟩` and prove the remaining obligations. Use `show ‖schwartzToL2 l (omS g f)‖ = ‖schwartzToL2 l f‖`. Rewrite using `[← om_sch, LinearIsometryEquiv.norm_map]`. Take `⟨k', hk'⟩` from `exists_rho w (omS g f)`.

Establish `e : omS g k = k'`. Apply `injective_toLp 2 volume` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `show ⇑(omS g k) = rhoFun w (omS g f)`. Rewrite using `[e, hk']`.

Take `⟨c, hc⟩` from `hI.scalar hsurj`. Establish `hc' : ∀ f, omS g f = c • f` using `hc`. Establish `hn` using `omS_nrm g 1 (gs l) ann_gs`. Establish `e1 : ((1 : Sp l) : Mat l) = 1` using `rfl`. Rewrite `hn` using `[hpg, e1, Matrix.one_mul, dd_one, hc', SchwartzMap.smul_apply, gs_zero]`.

Establish `hc2 : (c - 1) * (c + 1) = 0` using `by linear_combination hn`. Break down `mul_eq_zero.1 hc2 with h | h` into its components or cases. Use `left`. Establish `hc1 : c = 1` using `sub_eq_zero.1 h`. Use `G_ext (by rw [hg, map_one]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)` and prove the remaining obligations.

Rewrite using `[om_of_omS hc', hc1, one_smul, map_one]`. Both sides reduce to the same expression. Rewrite using `[hc', hc1, one_smul, map_one]`. Both sides reduce to the same expression. Use `right`.

Establish `hc1 : c = -1` using `eq_neg_of_add_eq_zero_left h`. Use `G_ext (by rw [hg, pr_eps]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)` and prove the remaining obligations. Rewrite using `[om_of_omS hc', hc1, om_eps, neg_one_smul]`. Rewrite using `[hc', hc1, omS_eps, neg_one_smul]`. Introduce and unpack `(rfl | rfl)`.

Conclude with `map_one _`. Conclude with `pr_eps`.
-/
theorem ker : Ker l := by
  refine ⟨eps, eps_ne, fun g => ⟨fun hg => ?_, ?_⟩, om_eps⟩
  · have hsurj : Function.Surjective (omS g) := fun f => ⟨omS g⁻¹ f, by
      show (omS g * omS g⁻¹) f = f
      rw [← map_mul, mul_inv_cancel, map_one]; rfl⟩
    have hpg : ((pr g : Sp l) : Mat l) = 1 := by rw [hg]; rfl
    have hI : Impl id (omS g).toLinearMap := by
      refine ⟨fun f => ?_, fun w f k hk => ?_⟩
      · show ‖schwartzToL2 l (omS g f)‖ = ‖schwartzToL2 l f‖
        rw [← om_sch, LinearIsometryEquiv.norm_map]
      · obtain ⟨k', hk'⟩ := exists_rho w (omS g f)
        have e : omS g k = k' := by
          apply injective_toLp 2 volume
          calc (omS g k).toLp 2 volume = om g (k.toLp 2 volume) := (om_sch g k).symm
            _ = om g (rho w (f.toLp 2 volume)) := by rw [toLp_rho hk]
            _ = rho w (om g (f.toLp 2 volume)) := by rw [om_rho, hpg, one_mulVec]
            _ = rho w ((omS g f).toLp 2 volume) := by rw [← schwartzToL2_apply, om_sch]; rfl
            _ = k'.toLp 2 volume := (toLp_rho hk').symm
        show ⇑(omS g k) = rhoFun w (omS g f)
        rw [e, hk']
    obtain ⟨c, hc⟩ := hI.scalar hsurj
    have hc' : ∀ f, omS g f = c • f := hc
    have hn := omS_nrm g 1 (gs l) ann_gs
    have e1 : ((1 : Sp l) : Mat l) = 1 := rfl
    rw [hpg, e1, Matrix.one_mul, dd_one, hc', SchwartzMap.smul_apply, gs_zero] at hn
    have hc2 : (c - 1) * (c + 1) = 0 := by linear_combination hn
    rcases mul_eq_zero.1 hc2 with h | h
    · left
      have hc1 : c = 1 := sub_eq_zero.1 h
      refine G_ext (by rw [hg, map_one]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)
      · rw [om_of_omS hc', hc1, one_smul, map_one]; rfl
      · rw [hc', hc1, one_smul, map_one]; rfl
    · right
      have hc1 : c = -1 := eq_neg_of_add_eq_zero_left h
      refine G_ext (by rw [hg, pr_eps]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)
      · rw [om_of_omS hc', hc1, om_eps, neg_one_smul]
      · rw [hc', hc1, omS_eps, neg_one_smul]
  · rintro (rfl | rfl)
    · exact map_one _
    · exact pr_eps

end CompanionTheory.ThKR.Mp

end

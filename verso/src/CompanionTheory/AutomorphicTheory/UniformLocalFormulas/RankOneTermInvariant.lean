import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocNorm
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RMeasP
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPfLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PiMeasureScaling
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformLocalSums.IntegralEqOfQuotientMeasuresBesselUnitaryImports
import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformLocalSums.UnipotentRadicalInterConjugateClosedUnimodularIm
import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformLocalSums.BesselRootMeasureIndependentOfChoicesImports

noncomputable section

open scoped Classical ENNReal InnerProductSpace
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.RealObj Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocJEq Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.RealConjugatorData

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `rdE_pos D` as an intermediate fact. Unfold `Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v`. Check the signs of the components of the expression.
-/
theorem ka_pos (D : D7) : 0 < D.host.ka := by
  have := rdE_pos D
  unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
  positivity

variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hs`.

Rewrite using `[Function.update_of_ne hw]`. Establish `h1 : uMat ((1 : X.B.I.Ginf) w) = 1` using `rfl`. Rewrite using `[h1]`. Apply the tactic sequence `refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> simp`.
-/
theorem upd_mem (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) {s : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ JointQuot.NV X u v) :
    Function.update (1 : X.B.I.Ginf) v s ∈ X.NinfU u := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [Function.update_self]
    exact hs
  · rw [Function.update_of_ne hw]
    have h1 : uMat ((1 : X.B.I.Ginf) w) = 1 := rfl
    rw [h1]
    refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> simp

/- English proof (translation)
Take `⟨x0, hx0⟩` from `EnergyPfLoc.wu_ne X u`. Use `set S : X.B.I.Ginf := Function.update 1 v s with hSdef`. Establish `hS : S ∈ X.NinfU u` using `upd_mem u v hs`. Establish `hmul : S * Function.update x0 v a = Function.update x0 v (s * a)`. Use function extensionality and compare the values at `w`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using `[S]`. Simplify using `[S, Function.update_of_ne hw]`. Establish `hW : X.Wu u (S * Function.update x0 v a) = JointQuot.psiU X u S • X.Wu u (Function.update x0 v a)`.

Rewrite using `[(X.Wu_spec u).1 S (fun v => (hS v).1) _, (X.piU_rep u).2.2.2.1 S hS]`. Both sides reduce to the same expression. Establish `hK : (∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ) ≠ 0`. Establish `h0` using `EnergyPfLoc.inner_upd X u v x0 (x0 v) (x0 v)`. Rewrite `h0` using `[Function.update_eq_self]`.

Establish `hne : ⟪X.Wu u x0, X.Wu u x0⟫_ℂ ≠ 0` using `inner_self_ne_zero.2 hx0`. Rewrite `hne` using `[h0]`. Conclude with `right_ne_zero_of_mul hne`. Establish `key : ∀ b, ⟪X.Wloc u v b, X.Wloc u v (s * a) - JointQuot.psiU X u S • X.Wloc u v a⟫_ℂ = 0`. Introduce `b`.

Establish `h1` using `EnergyPfLoc.inner_upd X u v x0 b (s * a)`. Rewrite `h1` using `[← hmul, hW, inner_smul_right, EnergyPfLoc.inner_upd, ← mul_assoc]`. Rewrite using `[inner_sub_right, inner_smul_right, mul_right_cancel₀ hK h1, sub_self]`. Rewrite using `[← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]`. Use `nth_rewrite 1 [inner_sub_left]`.

Rewrite using `[inner_smul_left, key, key, mul_zero, sub_zero]`.
-/
theorem wloc_N (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) {s : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ JointQuot.NV X u v)
    (a : Formalism.REAL.UJ (X.B.I.ε v)) :
    X.Wloc u v (s * a) = JointQuot.psiU X u (Function.update 1 v s) • X.Wloc u v a := by
  obtain ⟨x0, hx0⟩ := EnergyPfLoc.wu_ne X u
  set S : X.B.I.Ginf := Function.update 1 v s with hSdef
  have hS : S ∈ X.NinfU u := upd_mem u v hs
  have hmul : S * Function.update x0 v a = Function.update x0 v (s * a) := by
    funext w
    by_cases hw : w = v
    · subst hw
      simp [S]
    · simp [S, Function.update_of_ne hw]
  have hW : X.Wu u (S * Function.update x0 v a) = JointQuot.psiU X u S • X.Wu u (Function.update x0 v a) := by
    rw [(X.Wu_spec u).1 S (fun v => (hS v).1) _, (X.piU_rep u).2.2.2.1 S hS]
    rfl
  have hK : (∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ) ≠ 0 := by
    have h0 := EnergyPfLoc.inner_upd X u v x0 (x0 v) (x0 v)
    rw [Function.update_eq_self] at h0
    have hne : ⟪X.Wu u x0, X.Wu u x0⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx0
    rw [h0] at hne
    exact right_ne_zero_of_mul hne
  have key : ∀ b, ⟪X.Wloc u v b, X.Wloc u v (s * a) - JointQuot.psiU X u S • X.Wloc u v a⟫_ℂ = 0 := by
    intro b
    have h1 := EnergyPfLoc.inner_upd X u v x0 b (s * a)
    rw [← hmul, hW, inner_smul_right, EnergyPfLoc.inner_upd, ← mul_assoc] at h1
    rw [inner_sub_right, inner_smul_right, mul_right_cancel₀ hK h1, sub_self]
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
  nth_rewrite 1 [inner_sub_left]
  rw [inner_smul_left, key, key, mul_zero, sub_zero]

/- English proof (translation)
Use `set γ := gamW X u u' w with hγ`. Establish `he : (γ v)⁻¹ * (s * z) = ((γ v)⁻¹ * s * γ v) * ((γ v)⁻¹ * z)` using `by group`. Establish `hc : γ⁻¹ * Function.update (1 : X.B.I.Ginf) v s * γ = Function.update (1 : X.B.I.Ginf) v ((γ v)⁻¹ * s * γ v)`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x = v`.

Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hx]`. Establish `hrel` using `JointQuot.stRel_holds X u u' w hw (Function.update 1 v s) ⟨upd_mem u v hs.1, by rw [hc]; exact upd_mem u' v hs.2⟩`. Rewrite `hrel` using `[hc]`.

Rewrite using `[he, wloc_N u v hs.1, wloc_N u' v hs.2, JointQuot.rankOneInnerOperator_smul_smul_eq_mul_conj_smul, hrel, one_smul]`.
-/
theorem rank_one_term_invariant (u u' : D.what₂.Word) {w : Point D.host.E (D.R.rS + 1)} (hw : JointQuot.OkPt X u u' w)
    (v : InfinitePlace X.B.I.F) {s : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ JointQuot.StV X u u' (gamW X u u' w) v)
    (z : Formalism.REAL.UJ (X.B.I.ε v)) :
    TermOp.rk1 (X.Wloc u v (s * z)) (X.Wloc u' v ((gamW X u u' w v)⁻¹ * (s * z))) =
      TermOp.rk1 (X.Wloc u v z) (X.Wloc u' v ((gamW X u u' w v)⁻¹ * z)) := by
  set γ := gamW X u u' w with hγ
  have he : (γ v)⁻¹ * (s * z) = ((γ v)⁻¹ * s * γ v) * ((γ v)⁻¹ * z) := by group
  have hc : γ⁻¹ * Function.update (1 : X.B.I.Ginf) v s * γ = Function.update (1 : X.B.I.Ginf) v ((γ v)⁻¹ * s * γ v) := by
    funext x
    by_cases hx : x = v
    · subst hx
      simp
    · simp [Function.update_of_ne hx]
  have hrel := JointQuot.stRel_holds X u u' w hw (Function.update 1 v s)
    ⟨upd_mem u v hs.1, by rw [hc]; exact upd_mem u' v hs.2⟩
  rw [hc] at hrel
  rw [he, wloc_N u v hs.1, wloc_N u' v hs.2, JointQuot.rankOneInnerOperator_smul_smul_eq_mul_conj_smul, hrel, one_smul]

variable {θ : ℝ} (C : Choice X θ)

/- English proof (translation)
Rewrite using `[smap_val, smap_val]`. Use `show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * (uMat (γ (vOf X τ)) * C.Q τ) * (C.Qi τ * (uMat (γ (vOf X τ))⁻¹ * uMat z) * C.Q τ * (C.y τ)⁻¹) = C.Qi τ * (uMat (γ (vOf X τ))⁻¹ * (uMat s * uMat z)) * C.Q τ * (C.y τ)⁻¹`. Rewrite using `[uMat_inv']`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (C.Q τ) (C.Qi τ), (C.isT τ).2.1, Matrix.one_mul, ← Matrix.mul_assoc (uMat (γ (vOf X τ))) (uMat (γ (vOf X τ)))⁻¹, uMat_mul_inv, Matrix.one_mul]`.
-/
theorem cMr_smap (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (s z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (Matrix.of (cMr C γ τ s) * Matrix.of (Smap C τ (γ (vOf X τ)) z) : MatKR D.R.k D.R.rS) =
      Matrix.of (Smap C τ (γ (vOf X τ)) (s * z)) := by
  rw [smap_val, smap_val]
  show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * (uMat (γ (vOf X τ)) * C.Q τ) *
      (C.Qi τ * (uMat (γ (vOf X τ))⁻¹ * uMat z) * C.Q τ * (C.y τ)⁻¹) =
    C.Qi τ * (uMat (γ (vOf X τ))⁻¹ * (uMat s * uMat z)) * C.Q τ * (C.y τ)⁻¹
  rw [uMat_inv']
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), (C.isT τ).2.1, Matrix.one_mul, ← Matrix.mul_assoc (uMat (γ (vOf X τ))) (uMat (γ (vOf X τ)))⁻¹, uMat_mul_inv, Matrix.one_mul]

/- English proof (translation)
Establish `: (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant` using `⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩`. Use `set y' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := ujOf' _ (y_facts C τ).1 with hy'`. Establish `e : Smap C τ g = (fun γ => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) γ)) ∘ (fun x => x * y') ∘ fun x => g⁻¹ * x`. Use function extensionality and compare the values at `z`. Use `show Matrix.of.symm (C.Qi τ * umat (g⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) = Matrix.of.symm (C.Qi τ * (umat (g⁻¹ * z) * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)) * C.Q τ)`.

Use `congr 1`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[(C.isT τ).1, Matrix.mul_one]`. Establish `hm : Measurable fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) γ)`. Use `Continuous.measurable ?_` and prove the remaining obligations.

Unfold `trG`. Conclude with `(continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul continuous_const`. Rewrite using `[e, ← Measure.map_map hm ((measurable_mul_const _).comp (measurable_const_mul _)), ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self, map_mul_right_eq_self]`. Both sides reduce to the same expression.
-/
theorem map_smap (τ : D.what₂.Tau) (g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (Smap C τ g) = muGB X (C.Q τ) (C.Qi τ) τ := by
  have : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  set y' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := ujOf' _ (y_facts C τ).1 with hy'
  have e : Smap C τ g = (fun γ => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) γ)) ∘ (fun x => x * y') ∘ fun x => g⁻¹ * x := by
    funext z
    show Matrix.of.symm (C.Qi τ * umat (g⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) =
      Matrix.of.symm (C.Qi τ * (umat (g⁻¹ * z) * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)) * C.Q τ)
    congr 1
    simp only [Matrix.mul_assoc]
    rw [(C.isT τ).1, Matrix.mul_one]
  have hm : Measurable fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) γ) := by
    refine Continuous.measurable ?_
    unfold trG
    exact (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul continuous_const
  rw [e, ← Measure.map_map hm ((measurable_mul_const _).comp (measurable_const_mul _)),
    ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self, map_mul_right_eq_self]
  rfl

/- English proof (translation)
Introduce `f hf`. Establish `he` using `smap_measEmb C τ (γ (vOf X τ))`. Rewrite using `[← map_smap C τ (γ (vOf X τ)), he.lintegral_map, he.lintegral_map]`. Use `(h _ (hf.comp he.measurable)).trans (lintegral_congr fun x => ?_)` and prove the remaining obligations. Rewrite using `[(cMr_measEmb C γ τ).lintegral_map]`.

Use `lintegral_congr fun s => ?_` and prove the remaining obligations. Conclude with `congrArg f (cMr_smap C γ τ s x).symm`.
-/
theorem quot_push (γ : X.B.I.Ginf) (τ : D.what₂.Tau) {μR ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))}
    (h : IsQuotLoc μR ν) :
    IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μR.map (cMr C γ τ)) (ν.map (Smap C τ (γ (vOf X τ)))) := by
  intro f hf
  have he := smap_measEmb C τ (γ (vOf X τ))
  rw [← map_smap C τ (γ (vOf X τ)), he.lintegral_map, he.lintegral_map]
  refine (h _ (hf.comp he.measurable)).trans (lintegral_congr fun x => ?_)
  rw [(cMr_measEmb C γ τ).lintegral_map]
  refine lintegral_congr fun s => ?_
  exact congrArg f (cMr_smap C γ τ s x).symm

/- English proof (translation)
Rewrite using `[range_smap]`. Establish `h1` using `transp_mem C τ ((Formalism.FourierDecayAlt.P.unitary_group_closed D.R.k D.R.rS).mul_mem _ hx _ (C.y_mem τ))`. Establish `e : C.Q τ * Matrix.of x * C.y τ * C.Qi τ = C.Q τ * (x * C.y τ) * C.Qi τ`. Rewrite using `[← Matrix.mul_assoc]`. Both sides reduce to the same expression.

Use `show umat g * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset _`. Rewrite using `[e]`. Conclude with `(g * ujOf' _ h1).2`.
-/
theorem mem_range (τ : D.what₂.Tau) (g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) {x : MatKR D.R.k D.R.rS}
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : x ∈ Set.range (Smap C τ g) := by
  rw [range_smap]
  have h1 := transp_mem C τ ((Formalism.FourierDecayAlt.P.unitary_group_closed D.R.k D.R.rS).mul_mem _ hx _ (C.y_mem τ))
  have e : C.Q τ * Matrix.of x * C.y τ * C.Qi τ = C.Q τ * (x * C.y τ) * C.Qi τ := by
    rw [← Matrix.mul_assoc]; rfl
  show umat g * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset _
  rw [e]
  exact (g * ujOf' _ h1).2

/- English proof (translation)
Use `set γ := gamW X u u' w with hγ`. Establish `hemb` using `cMr_measEmb C γ τ`. Establish `hN1 : (1 : MatKR D.R.k D.R.rS) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS` using `(Formalism.FourierDecayAlt.P.unipotent_radical_closed D.R.k D.R.rS).one_mem`. Establish `hid : (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = id`. Use function extensionality and compare the values at `x i j`.

Simplify using the standard rewrite rules. Use `⟨1, hN1, 1, hN1, JointAmplitudePoints.gamP C u u' w τ, by simp, RelPtR.zhatO_gamP C u u' w hw τ, μR.map (cMr C γ τ), ?_, ?_, by rw [hid, Measure.map_id]⟩` and prove the remaining obligations. Rewrite using `[hemb.map_apply]`. Conclude with `measure_mono_null (fun y hy hyS => hy ((stV_iff C γ τ u u' y).1 hyS)) hc`. Establish `hcomp : rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ cMr C γ τ = (fun (y : FreeE w → ℂ) i => (1 : ℂ) * y (RootPatterns.idxF τ w i)) ∘ JointQuot.stCoordV X u' w γ (vOf X τ)`.

Use function extensionality and compare the values at `y i`. Establish `h` using `congrFun (congrFun (RootPatterns.stCoordV_comp C u' w γ τ) y) (RootPatterns.idxF τ w i)`. Simplify using `only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply] at h`. Simplify using `only [Function.comp_apply, one_mul]`. Conclude with `h.symm`.

Establish `hst : Measurable (JointQuot.stCoordV X u' w γ (vOf X τ))`. Use `Continuous.measurable ?_` and prove the remaining obligations. Unfold `JointQuot.stCoordV hJ`. Use `fun_prop`. Establish `hGm : Measurable fun (y : FreeE w → ℂ) (i : ↥(rootPat (ptLoc D τ w))) => (1 : ℂ) * y (RootPatterns.idxF τ w i)` using `measurable_pi_lambda _ fun q => measurable_const.mul (measurable_pi_apply _)`.

Rewrite using `[Measure.map_map (RootPatterns.rootCoords_cont _ _ _ _).measurable hemb.measurable, hcomp, ← Measure.map_map hGm hst, hp]`. Unfold `JointQuot.muStabV`. Rewrite using `[PiMeasureScaling.pi_reindex_scale (RootPatterns.idxF τ w) _ ENNReal.ofReal_ne_top (fun _ => (1 : ℂ)) fun _ => one_ne_zero]`. Use `congr 1`. Establish `hka : 0 < D.host.ka` using `ka_pos D`.

Establish `hg : (X.B.g : ℝ) = gg D` using `by rw [X.g_eq, gg]; push_cast; rfl`. Establish `hg0 : 0 < gg D`. Establish `a` using `(D.host.g_prime 0).pos`. Establish `b` using `(D.host.g_prime 1).pos`. Unfold `gg`.

Check the signs of the components of the expression. Establish `e : 2 * D.host.ka / gg D / (2 * Real.pi) = D.host.ka / gg D / Real.pi` using `by field_simp`. Rewrite using `[hg, e, ENNReal.ofReal_pow (by positivity)]`. Simplify using the standard rewrite rules.
-/
theorem root_push (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, IsPtRep X u u' w g) (τ : D.what₂.Tau)
    {μR : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))}
    (hc : μR (JointQuot.StV X u u' (gamW X u u' w) (vOf X τ))ᶜ = 0)
    (hp : μR.map (JointQuot.stCoordV X u' w (gamW X u u' w) (vOf X τ)) = JointQuot.muStabV X w) :
    IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (ptLoc D τ w) (JointAmplitudePoints.gamP C u u' w τ)
      (μR.map (cMr C (gamW X u u' w) τ)) := by
  set γ := gamW X u u' w with hγ
  have hemb := cMr_measEmb C γ τ
  have hN1 : (1 : MatKR D.R.k D.R.rS) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS :=
    (Formalism.FourierDecayAlt.P.unipotent_radical_closed D.R.k D.R.rS).one_mem
  have hid : (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = id := by
    funext x i j
    simp
  refine ⟨1, hN1, 1, hN1, JointAmplitudePoints.gamP C u u' w τ, by simp, RelPtR.zhatO_gamP C u u' w hw τ, μR.map (cMr C γ τ), ?_, ?_,
    by rw [hid, Measure.map_id]⟩
  · rw [hemb.map_apply]
    exact measure_mono_null (fun y hy hyS => hy ((stV_iff C γ τ u u' y).1 hyS)) hc
  · have hcomp : rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ cMr C γ τ =
        (fun (y : FreeE w → ℂ) i => (1 : ℂ) * y (RootPatterns.idxF τ w i)) ∘ JointQuot.stCoordV X u' w γ (vOf X τ) := by
      funext y i
      have h := congrFun (congrFun (RootPatterns.stCoordV_comp C u' w γ τ) y) (RootPatterns.idxF τ w i)
      simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply] at h
      simp only [Function.comp_apply, one_mul]
      exact h.symm
    have hst : Measurable (JointQuot.stCoordV X u' w γ (vOf X τ)) := by
      refine Continuous.measurable ?_
      unfold JointQuot.stCoordV hJ
      fun_prop
    have hGm : Measurable fun (y : FreeE w → ℂ) (i : ↥(rootPat (ptLoc D τ w))) => (1 : ℂ) * y (RootPatterns.idxF τ w i) :=
      measurable_pi_lambda _ fun q => measurable_const.mul (measurable_pi_apply _)
    rw [Measure.map_map (RootPatterns.rootCoords_cont _ _ _ _).measurable hemb.measurable, hcomp,
      ← Measure.map_map hGm hst, hp]
    unfold JointQuot.muStabV
    rw [PiMeasureScaling.pi_reindex_scale (RootPatterns.idxF τ w) _ ENNReal.ofReal_ne_top (fun _ => (1 : ℂ)) fun _ => one_ne_zero]
    congr 1
    have hka : 0 < D.host.ka := ka_pos D
    have hg : (X.B.g : ℝ) = gg D := by rw [X.g_eq, gg]; push_cast; rfl
    have hg0 : 0 < gg D := by
      have a := (D.host.g_prime 0).pos
      have b := (D.host.g_prime 1).pos
      unfold gg
      positivity
    have e : 2 * D.host.ka / gg D / (2 * Real.pi) = D.host.ka / gg D / Real.pi := by field_simp
    rw [hg, e, ENNReal.ofReal_pow (by positivity)]
    simp

/- English proof (translation)
Introduce `w hb hw τ`. Establish `hok : JointQuot.OkPt X u u' w` using `⟨hw, OOCoreHilbertSchmidt.gxPos_holds u u' w hb hw⟩`. Take `⟨μR, hH, hQ, hp⟩` from `hP w hok (vOf X τ)`. Use `set γ := gamW X u u' w with hγ`. Take `⟨hz, hT⟩` from `zTr C u τ`.

Take `⟨hz', hT'⟩` from `zTr C u' τ`. Establish `hTu : ∀ u0 : D.what₂.Word, 0 < Tr D u0` using `fun u0 => Nat.cast_pos.2 (D.mem u0).A.T_prime.pos`. Establish `hg : JointAmplitudePoints.gamP C u u' w τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)` using `LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _`. Establish `hex : ∃ ν, RMeas D (locW C u u' τ) (JointAmplitudePoints.gamP C u u' w τ) 1 ν` using `RMeasP.rMeas_exact D (locW C u u' τ) hz (hT.symm ▸ hTu u) hz' (hT'.symm ▸ hTu u') (haarTr C τ) (ptLoc D τ w) _ hg (RelPtR.zhatO_gamP C u u' w hw τ)`. Establish `h1 : RMeas D (locW C u u' τ) (JointAmplitudePoints.gamP C u u' w τ) 1 (JointAmplitudePoints.nu1P C u u' w τ)`.

Unfold `JointAmplitudePoints.nu1P`. Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`. Take `⟨p, μ₁, hr1, hq1⟩` from `h1`. Rewrite `hq1` using `[ENNReal.ofReal_one, one_smul]`.

Establish `hG : Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (JointAmplitudePoints.gamP C u u' w τ) ≠ 0`. Rewrite using `[RelPtR.gf_gamP C u u' w hw τ]`. Conclude with `(hb.2 τ).ne'`. Take `⟨-, hμ, hHaar⟩` from `GlobalTheory.T.besselRootMeasure_independent_of_choices D _ _ _ _ _ _ _ hz hz' (hT.symm ▸ hTu u) (hT'.symm ▸ hTu u') hg hG (ka_pos D) hr1 (root_push C u u' w hw τ hH.2.2.1 hp)`. Establish `hq2` using `quot_push C γ τ hQ`.

Rewrite `hq2` using `[← hμ]`. Take `⟨hcl, hun⟩` from `GlobalTheory.T.unipotentRadical_inter_conjugate_closed_unimodular D.R.k D.R.rS _ hg`. Use `FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ))` as an intermediate fact. Use `set F : MatKR D.R.k D.R.rS → (X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)) := fun x => (innerSL ℂ ((locS hB u u' τ).Φ' x)).smulRight ((locS hB u u' τ).Φ (JointAmplitudePoints.gamP C u u' w τ * x)) with hF`. Establish `hFS : ∀ z, F (Smap C τ (γ (vOf X τ)) z) = sclOf hB u u' τ • TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) ((γ (vOf X τ))⁻¹ * z))` using `fun z => integrand_S C hB u u' τ (γ (vOf X τ)) z`.

Establish `hFc : ContinuousOn F (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS))`. Use `ContinuousOn.mono (s := Set.range (Smap C τ (γ (vOf X τ)))) ?_ fun x hx => mem_range C τ _ hx` and prove the remaining obligations. Use `continuousOn_iff_continuous_restrict.2 ?_` and prove the remaining obligations. Establish `hemb : Continuous fun z => F (Smap C τ (γ (vOf X τ)) z)`. Rewrite using `[funext hFS]`.

Conclude with `(rank_one_continuous (X.Wloc_cont u (vOf X τ)) ((X.Wloc_cont u' (vOf X τ)).comp (continuous_const.mul continuous_id))).const_smul (sclOf hB u u' τ)`. Use `(hemb.comp (smapInv_cont C τ (γ (vOf X τ)))).congr ?_` and prove the remaining obligations. Introduce and unpack `⟨_, z, rfl⟩`. Establish `: smapInv C τ (γ (vOf X τ)) ⟨_, z, rfl⟩ = z`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Use `show umat (γ (vOf X τ)) * (C.Q τ * Matrix.of (Smap C τ (γ (vOf X τ)) z) * C.y τ * C.Qi τ) = umat z`. Rewrite using `[smap_val, back_smap]`. Simplify using `only [Function.comp_apply, this]`. Both sides reduce to the same expression.

Establish `hFi : ∀ ρ ∈ Rset D.R.k D.R.rS (JointAmplitudePoints.gamP C u u' w τ), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), F (ρ * x) = F x`. Introduce `ρ hρ x hx`. Take `⟨z, rfl⟩` from `mem_range C τ (γ (vOf X τ)) hx`. Take `⟨s, rfl⟩` from `rset_range C γ τ ρ hρ`. Establish `hs` using `(stV_iff C γ τ u u' s).2 hρ`.

Establish `e` using `cMr_smap C γ τ s z`. Use `(congrArg F e).trans ?_` and prove the remaining obligations. Use `(hFS (s * z)).trans ?_` and prove the remaining obligations. Rewrite using `[rank_one_term_invariant u u' hok _ hs z]`. Conclude with `(hFS z).symm`.

Establish `hI` using `(GlobalTheory.T.integral_eq_of_quotientMeasures_besselUnitary D.R.k D.R.rS _ _ _ _ _ hcl (haarTr C τ) hHaar (hun _ hHaar) hq1 hq2 _ F hFc hFi).2`. Conclude with `congrArg (fun A => hsNormSq (((cOf hB u τ : ℝ) : ℂ)⁻¹ • A)) hI`.
-/
theorem use₇ (hB : WuBessel C) (u u' : D.what₂.Word)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hP : ∀ w, JointQuot.OkPt X u u' w → JointQuot.LocPin X u u' w νl) : LocNorm.LocUniqP u u' C hB νl := by
  intro w hb hw τ
  have hok : JointQuot.OkPt X u u' w := ⟨hw, OOCoreHilbertSchmidt.gxPos_holds u u' w hb hw⟩
  obtain ⟨μR, hH, hQ, hp⟩ := hP w hok (vOf X τ)
  set γ := gamW X u u' w with hγ
  obtain ⟨hz, hT⟩ := zTr C u τ
  obtain ⟨hz', hT'⟩ := zTr C u' τ
  have hTu : ∀ u0 : D.what₂.Word, 0 < Tr D u0 := fun u0 => Nat.cast_pos.2 (D.mem u0).A.T_prime.pos
  have hg : JointAmplitudePoints.gamP C u u' w τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _
  have hex : ∃ ν, RMeas D (locW C u u' τ) (JointAmplitudePoints.gamP C u u' w τ) 1 ν :=
    RMeasP.rMeas_exact D (locW C u u' τ) hz (hT.symm ▸ hTu u) hz' (hT'.symm ▸ hTu u') (haarTr C τ) (ptLoc D τ w) _ hg
      (RelPtR.zhatO_gamP C u u' w hw τ)
  have h1 : RMeas D (locW C u u' τ) (JointAmplitudePoints.gamP C u u' w τ) 1 (JointAmplitudePoints.nu1P C u u' w τ) := by
    unfold JointAmplitudePoints.nu1P
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨p, μ₁, hr1, hq1⟩ := h1
  rw [ENNReal.ofReal_one, one_smul] at hq1
  have hG : Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (JointAmplitudePoints.gamP C u u' w τ) ≠ 0 := by
    rw [RelPtR.gf_gamP C u u' w hw τ]
    exact (hb.2 τ).ne'
  obtain ⟨-, hμ, hHaar⟩ := GlobalTheory.T.besselRootMeasure_independent_of_choices D _ _ _ _ _ _ _ hz hz' (hT.symm ▸ hTu u) (hT'.symm ▸ hTu u') hg hG
    (ka_pos D) hr1 (root_push C u u' w hw τ hH.2.2.1 hp)
  have hq2 := quot_push C γ τ hQ
  rw [← hμ] at hq2
  obtain ⟨hcl, hun⟩ := GlobalTheory.T.unipotentRadical_inter_conjugate_closed_unimodular D.R.k D.R.rS _ hg
  have := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ))
  set F : MatKR D.R.k D.R.rS → (X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)) := fun x =>
    (innerSL ℂ ((locS hB u u' τ).Φ' x)).smulRight ((locS hB u u' τ).Φ (JointAmplitudePoints.gamP C u u' w τ * x)) with hF
  have hFS : ∀ z, F (Smap C τ (γ (vOf X τ)) z) = sclOf hB u u' τ •
      TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) ((γ (vOf X τ))⁻¹ * z)) :=
    fun z => integrand_S C hB u u' τ (γ (vOf X τ)) z
  have hFc : ContinuousOn F (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) := by
    refine ContinuousOn.mono (s := Set.range (Smap C τ (γ (vOf X τ)))) ?_ fun x hx => mem_range C τ _ hx
    refine continuousOn_iff_continuous_restrict.2 ?_
    have hemb : Continuous fun z => F (Smap C τ (γ (vOf X τ)) z) := by
      rw [funext hFS]
      exact (rank_one_continuous (X.Wloc_cont u (vOf X τ))
        ((X.Wloc_cont u' (vOf X τ)).comp (continuous_const.mul continuous_id))).const_smul (sclOf hB u u' τ)
    refine (hemb.comp (smapInv_cont C τ (γ (vOf X τ)))).congr ?_
    rintro ⟨_, z, rfl⟩
    have : smapInv C τ (γ (vOf X τ)) ⟨_, z, rfl⟩ = z := by
      apply Subtype.ext
      apply Units.ext
      show umat (γ (vOf X τ)) * (C.Q τ * Matrix.of (Smap C τ (γ (vOf X τ)) z) * C.y τ * C.Qi τ) = umat z
      rw [smap_val, back_smap]
    simp only [Function.comp_apply, this]
    rfl
  have hFi : ∀ ρ ∈ Rset D.R.k D.R.rS (JointAmplitudePoints.gamP C u u' w τ), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      F (ρ * x) = F x := by
    intro ρ hρ x hx
    obtain ⟨z, rfl⟩ := mem_range C τ (γ (vOf X τ)) hx
    obtain ⟨s, rfl⟩ := rset_range C γ τ ρ hρ
    have hs := (stV_iff C γ τ u u' s).2 hρ
    have e := cMr_smap C γ τ s z
    refine (congrArg F e).trans ?_
    refine (hFS (s * z)).trans ?_
    rw [rank_one_term_invariant u u' hok _ hs z]
    exact (hFS z).symm
  have hI := (GlobalTheory.T.integral_eq_of_quotientMeasures_besselUnitary D.R.k D.R.rS _ _ _ _ _ hcl (haarTr C τ) hHaar (hun _ hHaar) hq1 hq2 _ F hFc hFi).2
  exact congrArg (fun A => hsNormSq (((cOf hB u τ : ℝ) : ℂ)⁻¹ • A)) hI

end Formalism.MainStatements.RowRest

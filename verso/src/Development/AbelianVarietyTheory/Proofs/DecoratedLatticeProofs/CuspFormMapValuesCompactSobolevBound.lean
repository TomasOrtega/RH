import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeMultiplicityMapValueEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DRepAddAndBracket
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothVecHeadOfDerivativeFamilyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobUnif

open GlobalTheory.TypeSum GlobalTheory.TypeSum.SmoothFrechet GlobalTheory.SmoothGlob
open scoped NNReal

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Use `⟨GlobalTheory.T.smoothVec_head_of_derivative_family n ε H σ hσ v hv, fun l => ?_⟩` and prove the remaining obligations. Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons X l ih => show dRep σ X (Dw σ (l.map Subtype.val) (v [])) = v (X :: l)`. Rewrite using `[ih]`.

Conclude with `(hv.1 l X).deriv`.
-/
theorem fam_smooth [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {v : List (GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)) → H} (hv : v ∈ Fam ε σ) :
    SmoothVec (lieSet ε) σ (v []) ∧
      ∀ l : List (GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)), Dw σ (l.map Subtype.val) (v []) = v l := by
  refine ⟨GlobalTheory.T.smoothVec_head_of_derivative_family n ε H σ hσ v hv, fun l => ?_⟩
  induction l with
  | nil => rfl
  | cons X l ih =>
    show dRep σ X (Dw σ (l.map Subtype.val) (v [])) = v (X :: l)
    rw [ih]
    exact (hv.1 l X).deriv

/- English proof (translation)
Establish `h` using `GlobalTheory.SmoothCyclic.hasDerivAt_dRep (σ := σ) (ε := ε) hw hX`. Establish `hm : HasDerivAt (fun t : ℝ => a * t) a 0` using `by simpa using (hasDerivAt_id (0 : ℝ)).const_mul a`. Establish `h2` using `HasDerivAt.scomp (0 : ℝ) (by simpa using h) hm`. Establish `e : (fun t : ℝ => σ (NormedSpace.exp (t • (a • X))) w) = (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) ∘ fun t => a * t`. Use function extensionality and compare the values at `t`.

Simplify using `[smul_smul, mul_comm]`. Use `show deriv (fun t : ℝ => σ (NormedSpace.exp (t • (a • X))) w) 0 = _`. Rewrite using `[e, h2.deriv, Complex.coe_smul]`.
-/
theorem dRep_smul_of_sm {σ : Mx n → (H →L[ℂ] H)} {w : H} (hw : Sm ε σ w) {X : Mx n} (hX : X ∈ lieSet ε) (a : ℝ) :
    dRep σ (a • X) w = (a : ℂ) • dRep σ X w := by
  have h := GlobalTheory.SmoothCyclic.hasDerivAt_dRep (σ := σ) (ε := ε) hw hX
  have hm : HasDerivAt (fun t : ℝ => a * t) a 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
  have h2 := HasDerivAt.scomp (0 : ℝ) (by simpa using h) hm
  have e : (fun t : ℝ => σ (NormedSpace.exp (t • (a • X))) w) =
      (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) ∘ fun t => a * t := by
    funext t
    simp [smul_smul, mul_comm]
  show deriv (fun t : ℝ => σ (NormedSpace.exp (t • (a • X))) w) 0 = _
  rw [e, h2.deriv, Complex.coe_smul]

/- English proof (translation)
Establish `hmem : ∀ l : List (GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)), ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε` using `fun l X hX => by`. Take `⟨Y, -, rfl⟩` from `List.mem_map.1 hX`. Conclude with `Y.2`. Establish `hs : ∀ l : List (GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)), Sm ε σ (Dw σ (l.map Subtype.val) w)` using `fun l => Sm.word hσ hw (hmem l)`. Establish `hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε`.

Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[Pi.star_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hJd : IsUnit (Formalism.REAL.Jm ε).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (isUnit_Jm ε)`. Establish `hab` using `fun u (hu : Sm ε σ u) X (hX : X ∈ lieSet ε) Y (hY : Y ∈ lieSet ε) => GlobalTheory.DerivedAction.dRep_add_and_bracket n H (Formalism.REAL.Jm ε) σ hJ hJd hσ u hu X hX Y hY`. Establish `hcons : ∀ (Z : Mx n) (l : List (Mx n)) (u : H), Dw σ (Z :: l) u = dRep σ Z (Dw σ l u)` using `fun _ _ _ => rfl`. Use `⟨fun l X => ?_, fun l₁ l₂ a X Y => ?_, fun l₁ l₂ X Y Z hZ => ?_⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.SmoothCyclic.hasDerivAt_dRep (hs l) X.2`. Simplify using `only [List.map_append, List.map_cons, Dw_append, hcons]`. Establish `hu` using `hs l₂`. Establish `hX` using `GlobalTheory.SmoothCyclic.dRep_mem hσ hu X.2`. Establish `hY` using `GlobalTheory.SmoothCyclic.dRep_mem hσ hu Y.2`.

Establish `haX : (a : ℂ) • dRep σ X (Dw σ (l₂.map Subtype.val) w) ∈ GlobalTheory.SmoothCyclic.smSub ε σ` using `(GlobalTheory.SmoothCyclic.smSub ε σ).smul_mem _ hX`. Rewrite using `[Submodule.coe_add, Submodule.coe_smul, (hab _ hu _ ((GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)).smul_mem a X.2) _ Y.2).1, dRep_smul_of_sm hu X.2, Dw_add hσ (hmem l₁) haX hY, Dw_smul hσ (hmem l₁) _ hX]`. Simplify using `only [List.map_append, List.map_cons, Dw_append, hcons]`. Establish `hu` using `hs l₂`. Establish `hX` using `GlobalTheory.SmoothCyclic.dRep_mem hσ hu X.2`.

Establish `hY` using `GlobalTheory.SmoothCyclic.dRep_mem hσ hu Y.2`. Establish `hXY` using `GlobalTheory.SmoothCyclic.dRep_mem hσ hY X.2`. Establish `hYX` using `GlobalTheory.SmoothCyclic.dRep_mem hσ hX Y.2`. Rewrite using `[hZ, (hab _ hu _ X.2 _ Y.2).2]`. Establish `e` using `Dw_add hσ (hmem l₁) ((GlobalTheory.SmoothCyclic.smSub ε σ).sub_mem hXY hYX) hYX`.

Rewrite `e` using `[sub_add_cancel]`. Rewrite using `[e, add_sub_cancel_right]`.
-/
theorem smooth_fam [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {w : H}
    (hw : SmoothVec (lieSet ε) σ w) :
    (fun l : List (GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)) => Dw σ (l.map Subtype.val) w) ∈ Fam ε σ := by
  have hmem : ∀ l : List (GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)), ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε :=
    fun l X hX => by
      obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
      exact Y.2
  have hs : ∀ l : List (GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)), Sm ε σ (Dw σ (l.map Subtype.val) w) :=
    fun l => Sm.word hσ hw (hmem l)
  have hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    rw [Pi.star_apply]
    split_ifs <;> simp
  have hJd : IsUnit (Formalism.REAL.Jm ε).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_Jm ε)
  have hab := fun u (hu : Sm ε σ u) X (hX : X ∈ lieSet ε) Y (hY : Y ∈ lieSet ε) =>
    GlobalTheory.DerivedAction.dRep_add_and_bracket n H (Formalism.REAL.Jm ε) σ hJ hJd hσ u hu X hX Y hY
  have hcons : ∀ (Z : Mx n) (l : List (Mx n)) (u : H), Dw σ (Z :: l) u = dRep σ Z (Dw σ l u) := fun _ _ _ => rfl
  refine ⟨fun l X => ?_, fun l₁ l₂ a X Y => ?_, fun l₁ l₂ X Y Z hZ => ?_⟩
  · exact GlobalTheory.SmoothCyclic.hasDerivAt_dRep (hs l) X.2
  · simp only [List.map_append, List.map_cons, Dw_append, hcons]
    have hu := hs l₂
    have hX := GlobalTheory.SmoothCyclic.dRep_mem hσ hu X.2
    have hY := GlobalTheory.SmoothCyclic.dRep_mem hσ hu Y.2
    have haX : (a : ℂ) • dRep σ X (Dw σ (l₂.map Subtype.val) w) ∈ GlobalTheory.SmoothCyclic.smSub ε σ :=
      (GlobalTheory.SmoothCyclic.smSub ε σ).smul_mem _ hX
    rw [Submodule.coe_add, Submodule.coe_smul, (hab _ hu _ ((GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)).smul_mem a X.2) _ Y.2).1,
      dRep_smul_of_sm hu X.2, Dw_add hσ (hmem l₁) haX hY, Dw_smul hσ (hmem l₁) _ hX]
  · simp only [List.map_append, List.map_cons, Dw_append, hcons]
    have hu := hs l₂
    have hX := GlobalTheory.SmoothCyclic.dRep_mem hσ hu X.2
    have hY := GlobalTheory.SmoothCyclic.dRep_mem hσ hu Y.2
    have hXY := GlobalTheory.SmoothCyclic.dRep_mem hσ hY X.2
    have hYX := GlobalTheory.SmoothCyclic.dRep_mem hσ hX Y.2
    rw [hZ, (hab _ hu _ X.2 _ Y.2).2]
    have e := Dw_add hσ (hmem l₁) ((GlobalTheory.SmoothCyclic.smSub ε σ).sub_mem hXY hYX) hYX
    rw [sub_add_cancel] at e
    rw [e, add_sub_cancel_right]

/- English proof (translation)
Establish `hρ : ModRep ε σ` using `⟨hσ.1.1, hσ.1.2, 1, 0, fun g hg => by`. Rewrite using `[pow_zero, mul_one]`. Conclude with `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hσ.2.1 g hg v, one_mul]⟩`. Take `⟨d, b, φ, hb⟩` from `exists_frame ε`. Use `haveI : IsUniformAddGroup (Fam ε σ) := (Fam ε σ).toAddSubgroup.isUniformAddGroup`.

Use `haveI : CompleteSpace (Fam ε σ) := (GlobalTheory.T.isClosed_derivativeFamilies_moderateGrowth n ε H σ hρ).completeSpace_coe`. Use `haveI := (withSeminorms_sn (ρ := σ) hb).firstCountableTopology`. Use `haveI : (_root_.uniformity (Fam ε σ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated`. Use `letI := UniformSpace.pseudoMetricSpace (Fam ε σ)`. Use `infer_instance`.
-/
theorem fam_baire [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) :
    BaireSpace (Fam ε σ) := by
  have hρ : ModRep ε σ := ⟨hσ.1.1, hσ.1.2, 1, 0, fun g hg => by
    rw [pow_zero, mul_one]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hσ.2.1 g hg v, one_mul]⟩
  obtain ⟨d, b, φ, hb⟩ := exists_frame ε
  haveI : IsUniformAddGroup (Fam ε σ) := (Fam ε σ).toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace (Fam ε σ) := (GlobalTheory.T.isClosed_derivativeFamilies_moderateGrowth n ε H σ hρ).completeSpace_coe
  haveI := (withSeminorms_sn (ρ := σ) hb).firstCountableTopology
  haveI : (_root_.uniformity (Fam ε σ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI := UniformSpace.pseudoMetricSpace (Fam ε σ)
  infer_instance

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨[], rfl⟩`. Consider the case `cons X l ih`. Take `⟨l', hl'⟩` from `ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY))`. Conclude with `⟨⟨X, hl X List.mem_cons_self⟩ :: l', by simp [hl']⟩`.
-/
theorem exists_lift (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    ∃ l' : List (GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)), l'.map Subtype.val = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons X l ih =>
    obtain ⟨l', hl'⟩ := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY))
    exact ⟨⟨X, hl X List.mem_cons_self⟩ :: l', by simp [hl']⟩

/- English proof (translation)
Proceed by induction on `S with`. Consider the case `nil => exact ⟨0, continuous_const, rfl, fun v => by simp⟩`. Consider the case `cons l S ih`. Take `⟨q, hq, hq0, hqb⟩` from `ih (fun l' hl' => hS l' (List.mem_cons_of_mem _ hl'))`. Take `⟨l', rfl⟩` from `exists_lift l (hS l List.mem_cons_self)`.

Take `⟨C, -, h⟩` from `norm_le_sn (ρ := σ) hb l'`. Use `⟨fun v => C * sn σ b l'.length v + q v, (continuous_const.mul (continuous_sn b _)).add hq, by simp [hq0], fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_cons, List.sum_cons, (fam_smooth hσ v.2).2 l']`. Conclude with `add_le_add (h v) (hqb v)`.
-/
theorem exists_cont_bound [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {d : ℕ}
    {b : Fin d → GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε)} {φ : Fin d → (Mx n →ₗ[ℝ] ℝ)}
    (hb : ∀ X : GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε), ∑ j, φ j X • b j = X)
    (S : List (List (Mx n))) (hS : ∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) :
    ∃ q : Fam ε σ → ℝ, Continuous q ∧ q 0 = 0 ∧
      ∀ v : Fam ε σ, (S.map fun l => ‖Dw σ l (v.1 [])‖).sum ≤ q v := by
  induction S with
  | nil => exact ⟨0, continuous_const, rfl, fun v => by simp⟩
  | cons l S ih =>
    obtain ⟨q, hq, hq0, hqb⟩ := ih (fun l' hl' => hS l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨l', rfl⟩ := exists_lift l (hS l List.mem_cons_self)
    obtain ⟨C, -, h⟩ := norm_le_sn (ρ := σ) hb l'
    refine ⟨fun v => C * sn σ b l'.length v + q v, (continuous_const.mul (continuous_sn b _)).add hq,
      by simp [hq0], fun v => ?_⟩
    rw [List.map_cons, List.sum_cons, (fam_smooth hσ v.2).2 l']
    exact add_le_add (h v) (hqb v)

/- English proof (translation)
Use `continuous_of_continuousAt_zero f ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]`. Use `squeeze_zero (fun _ => norm_nonneg _) h ?_` and prove the remaining obligations. Simplify `hq.tendsto 0` using `[hq0]`.
-/
theorem continuous_of_bound {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (f : E →ₗ[ℂ] ℂ) (q : E → ℝ) (hq : Continuous q) (hq0 : q 0 = 0)
    (h : ∀ x, ‖f x‖ ≤ q x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) h ?_
  simpa [hq0] using hq.tendsto 0

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨[[]], fun v => by simp [sn_zero]⟩`. Consider the case `succ k ih`. Take `⟨L, hL⟩` from `ih`. Use `⟨(List.ofFn fun j => L.map (· ++ [b j])).flatten, fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[sn_succ, List.map_flatten, List.sum_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hL]`. Simplify using `[Function.comp_def, der_apply]`.
-/
theorem sn_eq_sum {σ : Mx n → (H →L[ℂ] H)} {d : ℕ} (b : Fin d → GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε))
    (k : ℕ) : ∃ L : List (List (GlobalTheory.LowTypeDetermined.lie (Formalism.REAL.Jm ε))), ∀ v : Fam ε σ,
      sn σ b k v = (L.map fun l => ‖v.1 l‖).sum := by
  induction k with
  | zero => exact ⟨[[]], fun v => by simp [sn_zero]⟩
  | succ k ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨(List.ofFn fun j => L.map (· ++ [b j])).flatten, fun v => ?_⟩
    rw [sn_succ, List.map_flatten, List.sum_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hL]
    simp [Function.comp_def, der_apply]

/- English proof (translation)
Take `⟨d, b, φ, hb⟩` from `exists_frame ε`. Use `haveI : IsUniformAddGroup (Fam ε σ) := (Fam ε σ).toAddSubgroup.isUniformAddGroup`. Use `haveI : BaireSpace (Fam ε σ) := fam_baire hσ`. Establish `hW` using `withSeminorms_sn (ρ := σ) hb`. Set `ev0 : Fam ε σ →ₗ[ℂ] H` to `(LinearMap.proj []).comp (Fam ε σ).subtype`.

Set `Λ : ι → Fam ε σ →ₗ[ℂ] ℂ` to `fun i => (ℓ i).comp ev0`. Establish `hΛ : ∀ i v, Λ i v = ℓ i (v.1 [])` using `fun _ _ => rfl`. Establish `hc : ∀ i, Continuous (Λ i)`. Introduce `i`. Take `⟨S, C, hS, hC⟩` from `hℓ i`.

Take `⟨q, hq, hq0, hqb⟩` from `exists_cont_bound hσ hb S hS`. Use `continuous_of_bound (Λ i) (fun v => |C| * q v) (continuous_const.mul hq) (by simp [hq0]) fun v => ?_` and prove the remaining obligations. Rewrite using `[hΛ]`. Establish `h0 : 0 ≤ (S.map fun l => ‖Dw σ l (v.1 [])‖).sum` using `List.sum_nonneg fun x hx => by`. Take `⟨l, -, rfl⟩` from `List.mem_map.1 hx`.

Conclude with `norm_nonneg _`. Use `(hC _ (fam_smooth hσ v.2).1).trans ?_` and prove the remaining obligations. Conclude with `(mul_le_mul_of_nonneg_right (le_abs_self C) h0).trans (mul_le_mul_of_nonneg_left (hqb v) (abs_nonneg C))`. Set `p : ι → Seminorm ℂ (Fam ε σ)` to `fun i => (normSeminorm ℂ ℂ).comp (Λ i)`. Establish `hp : ∀ i v, p i v = ‖ℓ i (v.1 [])‖` using `fun _ _ => rfl`.

Establish `hpv : ∀ v : Fam ε σ, BddAbove (Set.range fun i => p i v)` using `fun v => by`. Take `⟨B, hB⟩` from `hbd _ (fam_smooth hσ v.2).1`. Conclude with `⟨B, by rintro _ ⟨i, rfl⟩; exact (hp i v).trans_le (hB i)⟩`. Establish `hpb : BddAbove (Set.range p)` using `Seminorm.bddAbove_range_iff.2 hpv`. Establish `hpc : Continuous (⨆ i, p i : Seminorm ℂ (Fam ε σ))`.

Rewrite using `[Seminorm.coe_iSup_eq hpb]`. Conclude with `Seminorm.continuous_iSup p (fun i => continuous_norm.comp (hc i)) hpb`. Take `⟨s, C, -, hle⟩` from `Seminorm.bound_of_continuous hW _ hpc`. Use `choose L hL using fun k => sn_eq_sum (σ := σ) b k`. Use `⟨(s.toList.map fun k => (L k).map fun l => l.map Subtype.val).flatten, C, ?_, fun i w hw => ?_⟩` and prove the remaining obligations.

Introduce `l hl X hX`. Take `⟨m, hm, hlm⟩` from `List.mem_flatten.1 hl`. Take `⟨k, -, rfl⟩` from `List.mem_map.1 hm`. Take `⟨l', -, rfl⟩` from `List.mem_map.1 hlm`. Take `⟨Y, -, rfl⟩` from `List.mem_map.1 hX`.

Conclude with `Y.2`. Set `v : Fam ε σ` to `⟨fun l => Dw σ (l.map Subtype.val) w, smooth_fam hσ hw⟩`. Establish `hv : ∀ l, v.1 l = Dw σ (l.map Subtype.val) w` using `fun _ => rfl`. Establish `h1 : ‖ℓ i w‖ ≤ (⨆ i, p i : Seminorm ℂ (Fam ε σ)) v`. Rewrite using `[Seminorm.coe_iSup_eq hpb, iSup_apply]`.

Conclude with `le_ciSup (hpv v) i`. Establish `h2 : (s.sup (sn σ b)) v ≤ ∑ k ∈ s, sn σ b k v` using `Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun k _ => apply_nonneg _ _) fun k hk => Finset.single_le_sum (f := fun k => sn σ b k v) (fun _ _ => apply_nonneg _ _) hk`. Establish `h3 : ∑ k ∈ s, sn σ b k v = sobNorm σ ((s.toList.map fun k => (L k).map fun l => l.map Subtype.val).flatten) w`. Rewrite using `[sobNorm, List.map_flatten, List.sum_flatten, List.map_map, List.map_map, Finset.sum_map_toList]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hL, Function.comp_apply, Function.comp_apply, List.map_map]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem unif_model [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {ι : Type}
    (ℓ : ι → H →ₗ[ℂ] ℂ) (hℓ : ∀ i, Sobolev₂ (lieSet ε) σ (ℓ i))
    (hbd : ∀ w, SmoothVec (lieSet ε) σ w → ∃ B, ∀ i, ‖ℓ i w‖ ≤ B) :
    ∃ (S : List (List (Mx n))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧
      ∀ i w, SmoothVec (lieSet ε) σ w → ‖ℓ i w‖ ≤ C * sobNorm σ S w := by
  obtain ⟨d, b, φ, hb⟩ := exists_frame ε
  haveI : IsUniformAddGroup (Fam ε σ) := (Fam ε σ).toAddSubgroup.isUniformAddGroup
  haveI : BaireSpace (Fam ε σ) := fam_baire hσ
  have hW := withSeminorms_sn (ρ := σ) hb
  let ev0 : Fam ε σ →ₗ[ℂ] H := (LinearMap.proj []).comp (Fam ε σ).subtype
  let Λ : ι → Fam ε σ →ₗ[ℂ] ℂ := fun i => (ℓ i).comp ev0
  have hΛ : ∀ i v, Λ i v = ℓ i (v.1 []) := fun _ _ => rfl
  have hc : ∀ i, Continuous (Λ i) := by
    intro i
    obtain ⟨S, C, hS, hC⟩ := hℓ i
    obtain ⟨q, hq, hq0, hqb⟩ := exists_cont_bound hσ hb S hS
    refine continuous_of_bound (Λ i) (fun v => |C| * q v) (continuous_const.mul hq) (by simp [hq0]) fun v => ?_
    rw [hΛ]
    have h0 : 0 ≤ (S.map fun l => ‖Dw σ l (v.1 [])‖).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    refine (hC _ (fam_smooth hσ v.2).1).trans ?_
    exact (mul_le_mul_of_nonneg_right (le_abs_self C) h0).trans
      (mul_le_mul_of_nonneg_left (hqb v) (abs_nonneg C))
  let p : ι → Seminorm ℂ (Fam ε σ) := fun i => (normSeminorm ℂ ℂ).comp (Λ i)
  have hp : ∀ i v, p i v = ‖ℓ i (v.1 [])‖ := fun _ _ => rfl
  have hpv : ∀ v : Fam ε σ, BddAbove (Set.range fun i => p i v) := fun v => by
    obtain ⟨B, hB⟩ := hbd _ (fam_smooth hσ v.2).1
    exact ⟨B, by rintro _ ⟨i, rfl⟩; exact (hp i v).trans_le (hB i)⟩
  have hpb : BddAbove (Set.range p) := Seminorm.bddAbove_range_iff.2 hpv
  have hpc : Continuous (⨆ i, p i : Seminorm ℂ (Fam ε σ)) := by
    rw [Seminorm.coe_iSup_eq hpb]
    exact Seminorm.continuous_iSup p (fun i => continuous_norm.comp (hc i)) hpb
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous hW _ hpc
  choose L hL using fun k => sn_eq_sum (σ := σ) b k
  refine ⟨(s.toList.map fun k => (L k).map fun l => l.map Subtype.val).flatten, C, ?_, fun i w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨m, hm, hlm⟩ := List.mem_flatten.1 hl
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hm
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hlm
    obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
    exact Y.2
  · let v : Fam ε σ := ⟨fun l => Dw σ (l.map Subtype.val) w, smooth_fam hσ hw⟩
    have hv : ∀ l, v.1 l = Dw σ (l.map Subtype.val) w := fun _ => rfl
    have h1 : ‖ℓ i w‖ ≤ (⨆ i, p i : Seminorm ℂ (Fam ε σ)) v := by
      rw [Seminorm.coe_iSup_eq hpb, iSup_apply]
      exact le_ciSup (hpv v) i
    have h2 : (s.sup (sn σ b)) v ≤ ∑ k ∈ s, sn σ b k v :=
      Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun k _ => apply_nonneg _ _)
        fun k hk => Finset.single_le_sum (f := fun k => sn σ b k v) (fun _ _ => apply_nonneg _ _) hk
    have h3 : ∑ k ∈ s, sn σ b k v =
        sobNorm σ ((s.toList.map fun k => (L k).map fun l => l.map Subtype.val).flatten) w := by
      rw [sobNorm, List.map_flatten, List.sum_flatten, List.map_map, List.map_map, Finset.sum_map_toList]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hL, Function.comp_apply, Function.comp_apply, List.map_map]
      rfl
    calc ‖ℓ i w‖ ≤ (C • s.sup (sn σ b)) v := h1.trans (hle v)
      _ = C * (s.sup (sn σ b)) v := rfl
      _ ≤ C * ∑ k ∈ s, sn σ b k v := mul_le_mul_of_nonneg_left h2 C.2
      _ = _ := by rw [h3]

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`. Use function extensionality and compare the values at `w`. Unfold `dRep`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Use `show σ (P * NormedSpace.exp (t • (P⁻¹ * X * P)) * P⁻¹) w = σ (NormedSpace.exp (t • X)) w`. Rewrite using `[GlobalTheory.SmVec.exp_conj_inv hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]`.
-/
theorem dRep_conj_eq (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (X : Mx n) :
    dRep (fun g => σ (P * g * P⁻¹)) (P⁻¹ * X * P) = dRep σ X := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  funext w
  unfold dRep
  congr 1
  funext t
  show σ (P * NormedSpace.exp (t • (P⁻¹ * X * P)) * P⁻¹) w = σ (NormedSpace.exp (t • X)) w
  rw [GlobalTheory.SmVec.exp_conj_inv hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons X l ih => simp only [List.map_cons, List.foldr_cons, ih, dRep_conj_eq σ hP]`.
-/
theorem foldr_conj_eq (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (l : List (Mx n)) (w : H) :
    (l.map fun X => P⁻¹ * X * P).foldr (dRep (fun g => σ (P * g * P⁻¹))) w = l.foldr (dRep σ) w := by
  induction l with
  | nil => rfl
  | cons X l ih => simp only [List.map_cons, List.foldr_cons, ih, dRep_conj_eq σ hP]

end GlobalTheory.SobUnif

open GlobalTheory.SobUnif in

/- English proof (translation)
Introduce `D θ V S M J χ _ T hT Ω hΩ τ v`. Use `haveI : CompleteSpace (M.H τ) := (M.ds τ).1`. Establish `hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ)` using `(M.ds τ).2.2.1`. Establish `hP` using `M.fr_unit τ`. Establish `hG` using `M.fr_gram τ`.

Use `choose ℓ hℓ hℓT using fun g : Ω => hT.cont τ v g.1`. Establish `hsm : ∀ u : M.H τ, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) u → u ∈ M.sm τ` using `fun u hu => Submodule.subset_span ((GlobalTheory.SmoothCyclic.smoothVec_transport hP hG u).2 hu)`. Take `⟨L, C, hL, hC⟩` from `unif_model hσ ℓ (fun g => GlobalTheory.SmoothCyclic.sobCont_transport hP hG (hℓ g)) (fun u hu => by`. Take `⟨B, hB⟩` from `hΩ.exists_bound_of_continuousOn (f := T (Function.update v τ ⟨u, hsm u hu⟩)) (hT.aut _).cont.continuousOn`. Conclude with `⟨B, fun g => by rw [hℓT g ⟨u, hsm u hu⟩]; exact hB g.1 g.2⟩)`.

Use `⟨L.map fun l => l.map fun X => (M.fr τ)⁻¹ * X * M.fr τ, C, ?_, fun w g hg => ?_⟩` and prove the remaining obligations. Introduce `l hl Y hY`. Take `⟨l0, hl0, rfl⟩` from `List.mem_map.1 hl`. Take `⟨X, hX, rfl⟩` from `List.mem_map.1 hY`. Conclude with `GlobalTheory.SmoothCyclic.conj_lie (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)) hG (hL l0 hl0 X hX)`.

Establish `hw` using `(GlobalTheory.SmoothCyclic.smoothVec_transport hP hG (w : M.H τ)).1 (GlobalTheory.HolRead.MultDer.smoothVec_of_mem M τ w.2)`. Establish `h1` using `hC ⟨g, hg⟩ (w : M.H τ) hw`. Rewrite `h1` using `[hℓT ⟨g, hg⟩ w]`. Use `h1.trans_eq ?_` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[GlobalTheory.SmoothGlob.sobNorm, List.map_map]`. Use `congrArg List.sum (List.map_congr_left fun l _ => ?_)` and prove the remaining obligations. Conclude with `congrArg norm (foldr_conj_eq (M.σ τ) hP l (w : M.H τ)).symm`.
-/
theorem GlobalTheory.Core.Mi.sobolev_unif_bound : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ T : MMap M, IsMultMap θ M J χ T → ∀ Ω : Set (GA D V), IsCompact Ω → ∀ τ (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧ ∀ w : M.sm τ, ∀ g ∈ Ω, ‖T (Function.update v τ w) g‖ ≤ C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  intro D θ V S M J χ _ T hT Ω hΩ τ v
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.1
  have hP := M.fr_unit τ
  have hG := M.fr_gram τ
  choose ℓ hℓ hℓT using fun g : Ω => hT.cont τ v g.1
  have hsm : ∀ u : M.H τ, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) u → u ∈ M.sm τ := fun u hu =>
    Submodule.subset_span ((GlobalTheory.SmoothCyclic.smoothVec_transport hP hG u).2 hu)
  obtain ⟨L, C, hL, hC⟩ := unif_model hσ ℓ (fun g => GlobalTheory.SmoothCyclic.sobCont_transport hP hG (hℓ g))
    (fun u hu => by
      obtain ⟨B, hB⟩ := hΩ.exists_bound_of_continuousOn
        (f := T (Function.update v τ ⟨u, hsm u hu⟩)) (hT.aut _).cont.continuousOn
      exact ⟨B, fun g => by rw [hℓT g ⟨u, hsm u hu⟩]; exact hB g.1 g.2⟩)
  refine ⟨L.map fun l => l.map fun X => (M.fr τ)⁻¹ * X * M.fr τ, C, ?_, fun w g hg => ?_⟩
  · intro l hl Y hY
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
    exact GlobalTheory.SmoothCyclic.conj_lie (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)) hG
      (hL l0 hl0 X hX)
  · have hw := (GlobalTheory.SmoothCyclic.smoothVec_transport hP hG (w : M.H τ)).1
      (GlobalTheory.HolRead.MultDer.smoothVec_of_mem M τ w.2)
    have h1 := hC ⟨g, hg⟩ (w : M.H τ) hw
    rw [hℓT ⟨g, hg⟩ w] at h1
    refine h1.trans_eq ?_
    congr 1
    rw [GlobalTheory.SmoothGlob.sobNorm, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun l _ => ?_)
    exact congrArg norm (foldr_conj_eq (M.σ τ) hP l (w : M.H τ)).symm

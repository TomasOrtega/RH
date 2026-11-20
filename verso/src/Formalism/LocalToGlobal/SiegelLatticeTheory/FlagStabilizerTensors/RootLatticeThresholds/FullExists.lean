import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

noncomputable section

open scoped Classical TensorProduct
open Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter)

/- English proof (translation)
Unfold `phVal`. Simplify using `only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phVal_add (T T' : Cu X u hK) (yinf : X.B.I.Ginf) (n : X.B.I.Gf) (h : Hfin X u) (k : X.B.I.Gf) :
    phVal X u hK (T + T') yinf n h k = phVal X u hK T yinf n h k + phVal X u hK T' yinf n h k := by
  unfold phVal
  simp only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply]
  ring

/- English proof (translation)
Unfold `phVal`. Simplify using `only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phVal_smul (c : ℂ) (T : Cu X u hK) (yinf : X.B.I.Ginf) (n : X.B.I.Gf) (h : Hfin X u) (k : X.B.I.Gf) :
    phVal X u hK (c • T) yinf n h k = c * phVal X u hK T yinf n h k := by
  unfold phVal
  simp only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `Ph`. Use `split_ifs with hd`. Conclude with `phVal_add X u hK T T' _ _ _ _`. Simplify using the standard rewrite rules.
-/
theorem Ph_add (T T' : Cu X u hK) (y : X.B.I.GA) :
    Ph X u hK (T + T') y = Ph X u hK T y + Ph X u hK T' y := by
  unfold Ph
  split_ifs with hd
  · exact phVal_add X u hK T T' _ _ _ _
  · simp

/- English proof (translation)
Unfold `Ph`. Use `split_ifs with hd`. Conclude with `phVal_smul X u hK c T _ _ _ _`. Simplify using the standard rewrite rules.
-/
theorem Ph_smul (c : ℂ) (T : Cu X u hK) (y : X.B.I.GA) : Ph X u hK (c • T) y = c * Ph X u hK T y := by
  unfold Ph
  split_ifs with hd
  · exact phVal_smul X u hK c T _ _ _ _
  · simp

/- English proof (translation)
Introduce `hD hin`. Establish `hS : ∀ (T : Cu X u hK) (x : X.B.I.GA), Summable fun δ : Dt => Ph X u hK T ((δ : X.B.I.GA) * x)` using `fun T x => ((hin T Dt hD).1 x).of_norm`. Establish `hM : ∀ T : Cu X u hK, MemLp (Pser X u hK Dt T) 2 ((X.B.I.muA X.B.μf).restrict X.B.fund)` using `fun T => (hin T Dt hD).2.2.1`. Use `⟨fun T T' => ?_, fun c T => ?_⟩` and prove the remaining obligations. Establish `he : Pser X u hK Dt (T + T') = Pser X u hK Dt T + Pser X u hK Dt T'`.

Use function extensionality and compare the values at `x`. Simplify using `only [Pser, Formalism.L2.SG.PoincareSeriesSquareIntegrable.poinc, Pi.add_apply, Ph_add]`. Conclude with `(hS T x).tsum_add (hS T' x)`. Unfold `PuFun`. Rewrite using `[dif_pos (hM _), dif_pos (hM T), dif_pos (hM T'), ← MemLp.toLp_add]`.

Conclude with `MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun he x)`. Establish `he : Pser X u hK Dt (c • T) = c • Pser X u hK Dt T`. Use function extensionality and compare the values at `x`. Simplify using `only [Pser, Formalism.L2.SG.PoincareSeriesSquareIntegrable.poinc, Pi.smul_apply, smul_eq_mul, Ph_smul]`. Conclude with `tsum_mul_left`.

Unfold `PuFun`. Rewrite using `[dif_pos (hM _), dif_pos (hM T), ← MemLp.toLp_const_smul]`. Conclude with `MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun he x)`.
-/
theorem puLinear (Dt : Set X.B.I.GA) : PuLinear X u hK Dt := by
  intro hD hin
  have hS : ∀ (T : Cu X u hK) (x : X.B.I.GA), Summable fun δ : Dt => Ph X u hK T ((δ : X.B.I.GA) * x) :=
    fun T x => ((hin T Dt hD).1 x).of_norm
  have hM : ∀ T : Cu X u hK, MemLp (Pser X u hK Dt T) 2 ((X.B.I.muA X.B.μf).restrict X.B.fund) :=
    fun T => (hin T Dt hD).2.2.1
  refine ⟨fun T T' => ?_, fun c T => ?_⟩
  · have he : Pser X u hK Dt (T + T') = Pser X u hK Dt T + Pser X u hK Dt T' := by
      funext x
      simp only [Pser, Formalism.L2.SG.PoincareSeriesSquareIntegrable.poinc, Pi.add_apply, Ph_add]
      exact (hS T x).tsum_add (hS T' x)
    unfold PuFun
    rw [dif_pos (hM _), dif_pos (hM T), dif_pos (hM T'), ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun he x)
  · have he : Pser X u hK Dt (c • T) = c • Pser X u hK Dt T := by
      funext x
      simp only [Pser, Formalism.L2.SG.PoincareSeriesSquareIntegrable.poinc, Pi.smul_apply, smul_eq_mul, Ph_smul]
      exact tsum_mul_left
    unfold PuFun
    rw [dif_pos (hM _), dif_pos (hM T), ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun he x)

end Lin

/- English proof (translation)
Introduce `_ X Y u` and use `puLinear X u Y.hK (Y.Dt u)`.
-/
theorem puLinearC : PuLinearC := fun _ X Y u => puLinear X u Y.hK (Y.Dt u)

section Vol

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def NOSub : Prop := ∀ s ∈ NOinf X u, ∀ t ∈ NOinf X u, t * s⁻¹ ∈ NOinf X u

def NOCount : Prop := (NOinf X u).Countable

def NOCofinite : Prop :=
  ∃ C : Set X.B.I.Ginf, MeasurableSet C ∧ X.muN u C < ⊤ ∧
    ∀ x ∈ X.NinfU u, ∃ s ∈ NOinf X u, ∃ c ∈ C, x = s * c

def HFinite : Prop := X.muH u Set.univ < ⊤

/- English proof (translation)
Take `⟨γ, -, h1, h2, -⟩` from `hs`. Conclude with `h1 ▸ h2`.
-/
theorem no_sub_ninf {s : X.B.I.Ginf} (hs : s ∈ NOinf X u) : s ∈ X.NinfU u := by
  obtain ⟨γ, -, h1, h2, -⟩ := hs
  exact h1 ▸ h2

/- English proof (translation)
Establish `h` using `(X.muN_haar u).2.2.2 s hs`. Rewrite using `[← Measure.map_apply (measurable_const_mul s) hA, h]`.
-/
theorem muN_pre (s : X.B.I.Ginf) (hs : s ∈ X.NinfU u) {A : Set X.B.I.Ginf} (hA : MeasurableSet A) :
    X.muN u ((fun x => s * x) ⁻¹' A) = X.muN u A := by
  have h := (X.muN_haar u).2.2.2 s hs
  rw [← Measure.map_apply (measurable_const_mul s) hA, h]

/- English proof (translation)
Establish `hne` using `(X.muN_haar u).2.1`. Establish `hcompl : X.muN u (X.NinfU u)ᶜ = 0` using `(X.muN_haar u).2.2.1`. Rewrite using `[pos_iff_ne_zero]`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Establish `hsub : X.NinfU u ⊆ ⋃ s ∈ NOinf X u, (fun x => s * x) ⁻¹' FN`. Introduce `x _`. Take `⟨s, hs, hsx⟩` from `hF.2.1 x`. Conclude with `Set.mem_biUnion hs hsx`. Establish `hN : X.muN u (X.NinfU u) = 0`.

Use `measure_mono_null hsub ?_` and prove the remaining obligations. Use `(measure_biUnion_null_iff hc).2 fun s hs => ?_` and prove the remaining obligations. Rewrite using `[muN_pre X u s (no_sub_ninf X u hs) hF.1]`. Conclude with `h0`. Rewrite using `[← Measure.measure_univ_eq_zero]`.

Conclude with `measure_mono_null (fun x _ => em (x ∈ X.NinfU u)) (measure_union_null hN hcompl)`.
-/
theorem muN_pos_of (hc : NOCount X u) {FN : Set X.B.I.Ginf} (hF : IsSFund X.B.I (NOinf X u) FN) :
    0 < X.muN u FN := by
  have hne := (X.muN_haar u).2.1
  have hcompl : X.muN u (X.NinfU u)ᶜ = 0 := (X.muN_haar u).2.2.1
  rw [pos_iff_ne_zero]
  intro h0
  apply hne
  have hsub : X.NinfU u ⊆ ⋃ s ∈ NOinf X u, (fun x => s * x) ⁻¹' FN := by
    intro x _
    obtain ⟨s, hs, hsx⟩ := hF.2.1 x
    exact Set.mem_biUnion hs hsx
  have hN : X.muN u (X.NinfU u) = 0 := by
    refine measure_mono_null hsub ?_
    refine (measure_biUnion_null_iff hc).2 fun s hs => ?_
    rw [muN_pre X u s (no_sub_ninf X u hs) hF.1]
    exact h0
  rw [← Measure.measure_univ_eq_zero]
  exact measure_mono_null (fun x _ => em (x ∈ X.NinfU u)) (measure_union_null hN hcompl)

/- English proof (translation)
Take `⟨C, hCm, hCf, hcov⟩` from `hC`. Establish `hcompl : X.muN u (X.NinfU u)ᶜ = 0` using `(X.muN_haar u).2.2.1`. Set `P : X.B.I.Ginf → Set X.B.I.Ginf` to `fun s => {c | c ∈ C ∧ s * c ∈ FN}`. Set `Q : X.B.I.Ginf → Set X.B.I.Ginf` to `fun s => {x | x ∈ FN ∧ s⁻¹ * x ∈ C}`. Establish `hPm : ∀ s, MeasurableSet (P s)` using `fun s => hCm.inter (hF.1.preimage (measurable_const_mul s))`.

Establish `hQm : ∀ s, MeasurableSet (Q s)` using `fun s => hF.1.inter (hCm.preimage (measurable_const_mul s⁻¹))`. Establish `hPQ : ∀ s, (fun x => s * x) ⁻¹' Q s = P s`. Introduce `s`. Use extensionality with `c`. Simplify using `[P, Q, and_comm]`.

Establish `hQP : ∀ s ∈ NOinf X u, X.muN u (Q s) = X.muN u (P s)`. Introduce `s hs`. Rewrite using `[← hPQ s, muN_pre X u s (no_sub_ninf X u hs) (hQm s)]`. Establish `hcovF : FN ∩ X.NinfU u ⊆ ⋃ s ∈ NOinf X u, Q s`. Introduce and unpack `x ⟨hxF, hxN⟩`.

Take `⟨s, hs, c, hc, rfl⟩` from `hcov x hxN`. Conclude with `Set.mem_biUnion hs ⟨hxF, by simpa using hc⟩`. Establish `hdisj : (NOinf X u).PairwiseDisjoint P`. Introduce `s hs t ht hst`. Rewrite using `[Function.onFun, Set.disjoint_left]`.

Introduce and unpack `c ⟨_, hsc⟩ ⟨_, htc⟩`. Apply `hst` to reduce the goal to its premises. Establish `h1` using `hF.2.2 (s * c) hsc (t * s⁻¹) (hsub s hs t ht) (by simpa [mul_assoc] using htc)`. Conclude with `(mul_inv_eq_one.1 h1).symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem muN_fin_of (hsub : NOSub X u) (hc : NOCount X u) (hC : NOCofinite X u) {FN : Set X.B.I.Ginf}
    (hF : IsSFund X.B.I (NOinf X u) FN) : X.muN u FN < ⊤ := by
  obtain ⟨C, hCm, hCf, hcov⟩ := hC
  have hcompl : X.muN u (X.NinfU u)ᶜ = 0 := (X.muN_haar u).2.2.1
  let P : X.B.I.Ginf → Set X.B.I.Ginf := fun s => {c | c ∈ C ∧ s * c ∈ FN}
  let Q : X.B.I.Ginf → Set X.B.I.Ginf := fun s => {x | x ∈ FN ∧ s⁻¹ * x ∈ C}
  have hPm : ∀ s, MeasurableSet (P s) := fun s => hCm.inter (hF.1.preimage (measurable_const_mul s))
  have hQm : ∀ s, MeasurableSet (Q s) := fun s => hF.1.inter (hCm.preimage (measurable_const_mul s⁻¹))
  have hPQ : ∀ s, (fun x => s * x) ⁻¹' Q s = P s := by
    intro s
    ext c
    simp [P, Q, and_comm]
  have hQP : ∀ s ∈ NOinf X u, X.muN u (Q s) = X.muN u (P s) := by
    intro s hs
    rw [← hPQ s, muN_pre X u s (no_sub_ninf X u hs) (hQm s)]
  have hcovF : FN ∩ X.NinfU u ⊆ ⋃ s ∈ NOinf X u, Q s := by
    rintro x ⟨hxF, hxN⟩
    obtain ⟨s, hs, c, hc, rfl⟩ := hcov x hxN
    exact Set.mem_biUnion hs ⟨hxF, by simpa using hc⟩
  have hdisj : (NOinf X u).PairwiseDisjoint P := by
    intro s hs t ht hst
    rw [Function.onFun, Set.disjoint_left]
    rintro c ⟨_, hsc⟩ ⟨_, htc⟩
    apply hst
    have h1 := hF.2.2 (s * c) hsc (t * s⁻¹) (hsub s hs t ht) (by simpa [mul_assoc] using htc)
    exact (mul_inv_eq_one.1 h1).symm
  calc X.muN u FN = X.muN u (FN ∩ X.NinfU u) := (measure_inter_conull hcompl).symm
    _ ≤ X.muN u (⋃ s ∈ NOinf X u, Q s) := measure_mono hcovF
    _ ≤ ∑' s : NOinf X u, X.muN u (Q s) := measure_biUnion_le _ hc _
    _ = ∑' s : NOinf X u, X.muN u (P s) := tsum_congr fun s => hQP s s.2
    _ = X.muN u (⋃ s ∈ NOinf X u, P s) := (measure_biUnion hc hdisj fun s _ => hPm s).symm
    _ ≤ X.muN u C := measure_mono (Set.iUnion₂_subset fun s _ => fun c hc => hc.1)
    _ < ⊤ := hCf

/- English proof (translation)
Establish `hK : 0 < X.volK2` using `ENNReal.toReal_pos hL.2.2.1.ne' hL.2.2.2.ne`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `Full.volN`. Conclude with `mul_pos hK (ENNReal.toReal_pos (muN_pos_of X u hc (Y.FN_fund u)).ne' (muN_fin_of X u hsub hc hC (Y.FN_fund u)).ne)`. Unfold `Full.volH`.

Use `ENNReal.toReal_pos ?_ hH.ne` and prove the remaining obligations. Introduce `h0`. Conclude with `(X.muH_haar u).2.1 (Measure.measure_univ_eq_zero.1 h0)`.
-/
theorem volPos_of (hsub : NOSub X u) (hc : NOCount X u) (hC : NOCofinite X u) (hH : HFinite X u)
    (Y : Full X) (hL : X.LevelSubgroupNormalized) : 0 < Y.volN u ∧ 0 < Y.volH u := by
  have hK : 0 < X.volK2 := ENNReal.toReal_pos hL.2.2.1.ne' hL.2.2.2.ne
  refine ⟨?_, ?_⟩
  · unfold Full.volN
    exact mul_pos hK (ENNReal.toReal_pos (muN_pos_of X u hc (Y.FN_fund u)).ne'
      (muN_fin_of X u hsub hc hC (Y.FN_fund u)).ne)
  · unfold Full.volH
    refine ENNReal.toReal_pos ?_ hH.ne
    intro h0
    exact (X.muH_haar u).2.1 (Measure.measure_univ_eq_zero.1 h0)

end Vol

def NOSubC : Prop := ∀ (D : D7) (X : HidaSetting D), X.LevelSubgroupCharacter → ∀ u, NOSub X u

def NOCountC : Prop := ∀ (D : D7) (X : HidaSetting D) u, NOCount X u

def NOCofiniteC : Prop := ∀ (D : D7) (X : HidaSetting D) u, NOCofinite X u

def HFiniteC : Prop := ∀ (D : D7) (X : HidaSetting D) u, HFinite X u

/- English proof (translation)
Introduce `D X Y u hL` and use `volPos_of X u (h1 D X Y.hK u) (h2 D X u) (h3 D X u) (h4 D X u) Y hL`.
-/
theorem volPosC_of (h1 : NOSubC) (h2 : NOCountC) (h3 : NOCofiniteC) (h4 : HFiniteC) : VolPosC :=
  fun D X Y u hL => volPos_of X u (h1 D X Y.hK u) (h2 D X u) (h3 D X u) (h4 D X u) Y hL

/- English proof (translation)
Set `r : Setoid G` to `QuotientGroup.rightRel S`. Set `o : G → G` to `fun g => (Quotient.mk r g).out`. Establish `ho : ∀ g, g * (o g)⁻¹ ∈ S` using `fun g => by`. Establish `h` using `Quotient.mk_out (s := r) g`. Conclude with `QuotientGroup.rightRel_apply.1 h`.

Establish `hoeq : ∀ g g', g' * g⁻¹ ∈ S → o g = o g'` using `fun g g' h => by`. Establish `h' : Quotient.mk r g = Quotient.mk r g'` using `Quotient.sound (QuotientGroup.rightRel_apply.2 h)`. Simplify using `only [o, h']`. Use `⟨{d | d ∈ Γ ∧ o d = d}, fun d hd => hd.1, fun γ hγ => ?_⟩` and prove the remaining obligations. Establish `hsm : γ * (o γ)⁻¹ ∈ S` using `ho γ`.

Establish `hoo : o (o γ) = o γ` using `hoeq _ _ hsm`. Establish `hdΓ : o γ ∈ Γ`. Establish `e : o γ = (γ * (o γ)⁻¹)⁻¹ * γ` using `by group`. Rewrite using `[e]`. Conclude with `Γ.mul_mem (Γ.inv_mem (hS hsm)) hγ`.

Use `⟨(⟨γ * (o γ)⁻¹, hsm⟩, ⟨o γ, hdΓ, hoo⟩), by simp, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨s, hs⟩, ⟨d, hdΓ', hdo⟩⟩ hsd`. Simplify using `only at hsd`. Establish `hs' : γ * d⁻¹ = s` using `by rw [← hsd]; group`. Establish `hd : d = o γ`.

Rewrite using `[← hdo]`. Conclude with `hoeq _ _ (hs' ▸ hs)`. Substitute `hd` using the available equality. Use `ext`. Simplify using `only`.

Rewrite using `[← hs']`. Both sides reduce to the same expression.
-/
theorem exists_rightTransversal' {G : Type*} [Group G] (Γ S : Subgroup G) (hS : S ≤ Γ) :
    ∃ Dt : Set G, Formalism.L2.SG.FoldBound.IsRightTransversal Γ S Dt := by
  let r : Setoid G := QuotientGroup.rightRel S
  let o : G → G := fun g => (Quotient.mk r g).out
  have ho : ∀ g, g * (o g)⁻¹ ∈ S := fun g => by
    have h := Quotient.mk_out (s := r) g
    exact QuotientGroup.rightRel_apply.1 h
  have hoeq : ∀ g g', g' * g⁻¹ ∈ S → o g = o g' := fun g g' h => by
    have h' : Quotient.mk r g = Quotient.mk r g' := Quotient.sound (QuotientGroup.rightRel_apply.2 h)
    simp only [o, h']
  refine ⟨{d | d ∈ Γ ∧ o d = d}, fun d hd => hd.1, fun γ hγ => ?_⟩
  have hsm : γ * (o γ)⁻¹ ∈ S := ho γ
  have hoo : o (o γ) = o γ := hoeq _ _ hsm
  have hdΓ : o γ ∈ Γ := by
    have e : o γ = (γ * (o γ)⁻¹)⁻¹ * γ := by group
    rw [e]
    exact Γ.mul_mem (Γ.inv_mem (hS hsm)) hγ
  refine ⟨(⟨γ * (o γ)⁻¹, hsm⟩, ⟨o γ, hdΓ, hoo⟩), by simp, ?_⟩
  rintro ⟨⟨s, hs⟩, ⟨d, hdΓ', hdo⟩⟩ hsd
  simp only at hsd
  have hs' : γ * d⁻¹ = s := by rw [← hsd]; group
  have hd : d = o γ := by
    rw [← hdo]
    exact hoeq _ _ (hs' ▸ hs)
  subst hd
  ext
  · simp only
    rw [← hs']
  · rfl

/- English proof (translation)
The claim follows from `exists_rightTransversal' _ _ inf_le_left`.
-/
theorem repsExist {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : ∃ Dt : Set X.B.I.GA, IsReps X u Dt :=
  exists_rightTransversal' _ _ inf_le_left

section Rows

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def latOf (h : Hfin X u) : Set (VS D).V :=
  {y | X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf}

def Eqv (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  ∃ γ ∈ stabF D (X.Fu u), Formalism.HermitianLatticesTheory.gmap γ Λ = Λ'

def dc (hK : X.LevelSubgroupCharacter) (h h' : Hfin X u) : Prop :=
  ∃ (g : Gam X u) (κ : Ku X u hK), h' = iotaF X u g * h * (κ : Hfin X u)

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 1, by simp⟩ symm := by rintro h h' ⟨g, κ, rfl⟩ refine ⟨g⁻¹, κ⁻¹, ?_⟩ simp only [map_inv, Subgroup.coe_inv] group trans := by rintro h h' h'' ⟨g, κ, rfl⟩ ⟨g', κ', rfl⟩ refine ⟨g' * g, κ * κ', ?_⟩ simp only [map_mul, Subgroup.coe_mul] group`.
-/
theorem dc_equiv (hK : X.LevelSubgroupCharacter) : Equivalence (dc X u hK) where
  refl h := ⟨1, 1, by simp⟩
  symm := by
    rintro h h' ⟨g, κ, rfl⟩
    refine ⟨g⁻¹, κ⁻¹, ?_⟩
    simp only [map_inv, Subgroup.coe_inv]
    group
  trans := by
    rintro h h' h'' ⟨g, κ, rfl⟩ ⟨g', κ', rfl⟩
    refine ⟨g' * g, κ * κ', ?_⟩
    simp only [map_mul, Subgroup.coe_mul]
    group

def dcSetoid (hK : X.LevelSubgroupCharacter) : Setoid (Hfin X u) := ⟨dc X u hK, dc_equiv X u hK⟩

def EqvEquiv : Prop := Equivalence (Eqv X u)

def LatSub : Prop :=
  ∀ h : Hfin X u, ∃ Λ : Submodule (𝓞 D.host.E) (VS D).V, (Λ : Set (VS D).V) = latOf X u h

def LatRow : Prop :=
  ∀ (h : Hfin X u) (Λ : Submodule (𝓞 D.host.E) (VS D).V), (Λ : Set (VS D).V) = latOf X u h →
    IsRowLat D (X.Fu u) Λ ∧ Formalism.L2.SG.Saturated.IsSplitRow D (X.Fu u) Λ

def LatSurj : Prop :=
  ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, IsRowLat D (X.Fu u) Λ →
    ∃ (h : Hfin X u) (Λ' : Submodule (𝓞 D.host.E) (VS D).V), (Λ' : Set (VS D).V) = latOf X u h ∧ Eqv X u Λ' Λ

def LatInj : Prop :=
  ∀ (h h' : Hfin X u) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    (Λ : Set (VS D).V) = latOf X u h → (Λ' : Set (VS D).V) = latOf X u h' → Eqv X u Λ Λ' →
    ∃ (g : Gam X u) (k : Hfin X u), h' = iotaF X u g * h * k ∧ latOf X u (h * k) = latOf X u h

def ClassFin (hK : X.LevelSubgroupCharacter) : Prop := Finite (Quotient (dcSetoid X u hK))

def LatCompat (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (h : Hfin X u) (g : Gam X u) (κ : Ku X u hK) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    (Λ : Set (VS D).V) = latOf X u h → (Λ' : Set (VS D).V) = latOf X u (iotaF X u g * h * (κ : Hfin X u)) →
    Eqv X u Λ Λ'

/- English proof (translation)
Use `choose L hL using h1`. Establish `: Finite (Quotient (dcSetoid X u hK))` using `h5`. Set `hq : Quotient (dcSetoid X u hK) → Hfin X u` to `fun q => q.out`. Set `e : Setoid (Quotient (dcSetoid X u hK))` to `⟨fun q q' => Eqv X u (L (hq q)) (L (hq q')), ⟨fun _ => h0.refl _, fun h => h0.symm h, fun h h' => h0.trans h h'⟩⟩`. Use `haveI : Fintype (Quotient e) := Fintype.ofFinite _`.

Use `haveI : Fintype (Quotient (dcSetoid X u hK)) := Fintype.ofFinite _`. Set `qc : Quotient (dcSetoid X u hK) → Quotient (dcSetoid X u hK)` to `fun q => (Quotient.mk e q).out`. Establish `hqc : ∀ q, Eqv X u (L (hq (qc q))) (L (hq q))` using `fun q => Quotient.mk_out (s := e) q`. Establish `hadj : ∀ q, ∃ (g : Gam X u) (k : Hfin X u), hq q = iotaF X u g * hq (qc q) * k ∧ latOf X u (hq (qc q) * k) = latOf X u (hq (qc q))` using `fun q => h4 _ _ _ _ (hL _) (hL _) (hqc q)`. Use `choose gq kq hgk hlat using hadj`.

Establish `hqcc : ∀ c : Quotient e, qc c.out = c.out` using `fun c => by`. Simplify using `only [qc, Quotient.out_eq]`. Set `what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)` to `Finset.univ.image fun c : Quotient e => L (hq c.out)`. Establish `hmem : ∀ Λ, Λ ∈ what₂ ↔ ∃ c : Quotient e, L (hq c.out) = Λ` using `fun Λ => by simp [what₂]`. Establish `hrowsLat : ∀ Λ ∈ what₂, IsRowLat D (X.Fu u) Λ ∧ Formalism.L2.SG.Saturated.IsSplitRow D (X.Fu u) Λ`.

Introduce `Λ hΛ`. Take `⟨c, rfl⟩` from `(hmem Λ).1 hΛ`. Conclude with `h2 _ _ (hL _)`. Establish `hq0 : Nonempty (Quotient (dcSetoid X u hK))` using `⟨Quotient.mk _ 1⟩`. Set `cs : ColSys X u what₂` to `{ Cl := Quotient (dcSetoid X u hK) lamOf := fun ρ => L (hq (qc ρ)) lam_mem := fun ρ => (hmem _).2 ⟨Quotient.mk e ρ, rfl⟩ h := fun ρ => hq (qc ρ) * kq ρ base := fun Λ => if hΛ : ∃ c : Quotient e, L (hq c.out) = Λ then hΛ.choose.out else Classical.arbitrary _ base_lam := by`.

Introduce `Λ hΛ`. Establish `hΛ'` using `(hmem Λ).1 hΛ`. Simplify using `only [dif_pos hΛ', hqcc]`. Conclude with `hΛ'.choose_spec`. Use `lat_eq := by`.

Introduce `ρ y`. Rewrite using `[← SetLike.mem_coe, hL, ← hlat ρ]`. Use `rfl }`. Use `⟨what₂, ⟨fun Λ hΛ => (hrowsLat Λ hΛ).1, fun Λ hΛ => ?_⟩, fun Λ hΛ => (hrowsLat Λ hΛ).2, cs, ?_⟩` and prove the remaining obligations. Take `⟨h, Λ', hΛ', hE⟩` from `h3 Λ hΛ`.

Take `⟨g, κ, hgκ⟩ : dc X u hK (hq (Quotient.mk _ h)) h` from `Quotient.mk_out (s := dcSetoid X u hK) h`. Establish `hE1 : Eqv X u (L (hq (Quotient.mk _ h))) Λ'` using `h6 _ g κ _ _ (hL _) (hgκ ▸ hΛ')`. Use `⟨L (hq (qc (Quotient.mk _ h))), ⟨(hmem _).2 ⟨Quotient.mk e _, rfl⟩, h0.trans (h0.trans (hqc _) hE1) hE⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `Λ2 ⟨hΛ2, hE2⟩`. Take `⟨c2, rfl⟩` from `(hmem _).1 hΛ2`.

Establish `hc : (Quotient.mk e c2.out) = Quotient.mk e (qc (Quotient.mk _ h))` using `Quotient.sound (h0.trans hE2 (h0.symm (h0.trans (h0.trans (hqc _) hE1) hE)))`. Rewrite `hc` using `[Quotient.out_eq]`. Rewrite using `[hc]`. Conclude with `congrArg (fun q => L (hq q)) (hqcc (Quotient.mk e (Quotient.mk _ h)))`. Establish `hrel : ∀ ρ : Quotient (dcSetoid X u hK), dc X u hK (hq ρ) (hq (qc ρ) * kq ρ)`.

Introduce `ρ`. Use `⟨(gq ρ)⁻¹, 1, ?_⟩` and prove the remaining obligations. Rewrite using `[hgk ρ]`. Simplify using `only [map_inv, OneMemClass.coe_one, mul_one]`. Use `group`.

Introduce `h`. Use `⟨Quotient.mk _ h, ?_, ?_⟩` and prove the remaining obligations. Establish `h1' : dc X u hK (hq (Quotient.mk _ h)) h` using `Quotient.mk_out (s := dcSetoid X u hK) h`. Conclude with `(dc_equiv X u hK).trans ((dc_equiv X u hK).symm (hrel _)) h1'`. Introduce and unpack `ρ ⟨g, κ, hgk'⟩`.

Establish `h2' : dc X u hK (hq ρ) h` using `(dc_equiv X u hK).trans (hrel ρ) ⟨g, κ, hgk'⟩`. Establish `: Quotient.mk (dcSetoid X u hK) (hq ρ) = Quotient.mk (dcSetoid X u hK) h` using `Quotient.sound h2'`. Simplify `this` using `[hq, Quotient.out_eq]`.
-/
theorem rowsCols_of (hK : X.LevelSubgroupCharacter) (h0 : EqvEquiv X u) (h1 : LatSub X u) (h2 : LatRow X u)
    (h3 : LatSurj X u) (h4 : LatInj X u) (h5 : ClassFin X u hK) (h6 : LatCompat X u hK) :
    ∃ what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V), IsRowReps D (X.Fu u) what₂ ∧
      (∀ Λ ∈ what₂, Formalism.L2.SG.Saturated.IsSplitRow D (X.Fu u) Λ) ∧ ∃ cs : ColSys X u what₂, ColReps hK cs := by
  choose L hL using h1
  have : Finite (Quotient (dcSetoid X u hK)) := h5
  let hq : Quotient (dcSetoid X u hK) → Hfin X u := fun q => q.out
  let e : Setoid (Quotient (dcSetoid X u hK)) :=
    ⟨fun q q' => Eqv X u (L (hq q)) (L (hq q')), ⟨fun _ => h0.refl _, fun h => h0.symm h, fun h h' => h0.trans h h'⟩⟩
  haveI : Fintype (Quotient e) := Fintype.ofFinite _
  haveI : Fintype (Quotient (dcSetoid X u hK)) := Fintype.ofFinite _
  let qc : Quotient (dcSetoid X u hK) → Quotient (dcSetoid X u hK) := fun q => (Quotient.mk e q).out
  have hqc : ∀ q, Eqv X u (L (hq (qc q))) (L (hq q)) := fun q => Quotient.mk_out (s := e) q
  have hadj : ∀ q, ∃ (g : Gam X u) (k : Hfin X u), hq q = iotaF X u g * hq (qc q) * k ∧
      latOf X u (hq (qc q) * k) = latOf X u (hq (qc q)) :=
    fun q => h4 _ _ _ _ (hL _) (hL _) (hqc q)
  choose gq kq hgk hlat using hadj
  have hqcc : ∀ c : Quotient e, qc c.out = c.out := fun c => by
    simp only [qc, Quotient.out_eq]
  let what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V) := Finset.univ.image fun c : Quotient e => L (hq c.out)
  have hmem : ∀ Λ, Λ ∈ what₂ ↔ ∃ c : Quotient e, L (hq c.out) = Λ := fun Λ => by simp [what₂]
  have hrowsLat : ∀ Λ ∈ what₂, IsRowLat D (X.Fu u) Λ ∧ Formalism.L2.SG.Saturated.IsSplitRow D (X.Fu u) Λ := by
    intro Λ hΛ
    obtain ⟨c, rfl⟩ := (hmem Λ).1 hΛ
    exact h2 _ _ (hL _)
  have hq0 : Nonempty (Quotient (dcSetoid X u hK)) := ⟨Quotient.mk _ 1⟩
  let cs : ColSys X u what₂ :=
    { Cl := Quotient (dcSetoid X u hK)
      lamOf := fun ρ => L (hq (qc ρ))
      lam_mem := fun ρ => (hmem _).2 ⟨Quotient.mk e ρ, rfl⟩
      h := fun ρ => hq (qc ρ) * kq ρ
      base := fun Λ => if hΛ : ∃ c : Quotient e, L (hq c.out) = Λ then hΛ.choose.out else Classical.arbitrary _
      base_lam := by
        intro Λ hΛ
        have hΛ' := (hmem Λ).1 hΛ
        simp only [dif_pos hΛ', hqcc]
        exact hΛ'.choose_spec
      lat_eq := by
        intro ρ y
        rw [← SetLike.mem_coe, hL, ← hlat ρ]
        rfl }
  refine ⟨what₂, ⟨fun Λ hΛ => (hrowsLat Λ hΛ).1, fun Λ hΛ => ?_⟩, fun Λ hΛ => (hrowsLat Λ hΛ).2, cs, ?_⟩
  ·
    obtain ⟨h, Λ', hΛ', hE⟩ := h3 Λ hΛ
    obtain ⟨g, κ, hgκ⟩ : dc X u hK (hq (Quotient.mk _ h)) h := Quotient.mk_out (s := dcSetoid X u hK) h
    have hE1 : Eqv X u (L (hq (Quotient.mk _ h))) Λ' := h6 _ g κ _ _ (hL _) (hgκ ▸ hΛ')
    refine ⟨L (hq (qc (Quotient.mk _ h))), ⟨(hmem _).2 ⟨Quotient.mk e _, rfl⟩, h0.trans (h0.trans (hqc _) hE1) hE⟩, ?_⟩
    rintro Λ2 ⟨hΛ2, hE2⟩
    obtain ⟨c2, rfl⟩ := (hmem _).1 hΛ2
    have hc : (Quotient.mk e c2.out) = Quotient.mk e (qc (Quotient.mk _ h)) :=
      Quotient.sound (h0.trans hE2 (h0.symm (h0.trans (h0.trans (hqc _) hE1) hE)))
    rw [Quotient.out_eq] at hc
    rw [hc]
    exact congrArg (fun q => L (hq q)) (hqcc (Quotient.mk e (Quotient.mk _ h)))
  ·
    have hrel : ∀ ρ : Quotient (dcSetoid X u hK), dc X u hK (hq ρ) (hq (qc ρ) * kq ρ) := by
      intro ρ
      refine ⟨(gq ρ)⁻¹, 1, ?_⟩
      rw [hgk ρ]
      simp only [map_inv, OneMemClass.coe_one, mul_one]
      group
    intro h
    refine ⟨Quotient.mk _ h, ?_, ?_⟩
    · have h1' : dc X u hK (hq (Quotient.mk _ h)) h := Quotient.mk_out (s := dcSetoid X u hK) h
      exact (dc_equiv X u hK).trans ((dc_equiv X u hK).symm (hrel _)) h1'
    · rintro ρ ⟨g, κ, hgk'⟩
      have h2' : dc X u hK (hq ρ) h := (dc_equiv X u hK).trans (hrel ρ) ⟨g, κ, hgk'⟩
      have : Quotient.mk (dcSetoid X u hK) (hq ρ) = Quotient.mk (dcSetoid X u hK) h := Quotient.sound h2'
      simpa [hq, Quotient.out_eq] using this

end Rows

def RowStepsC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    EqvEquiv X u ∧ LatSub X u ∧ LatRow X u ∧ LatSurj X u ∧ LatInj X u ∧ ClassFin X u hK ∧ LatCompat X u hK

def TRExistsC : Prop := ∀ (D : D7) (X : HidaSetting D), X.LevelSubgroupCharacter → ∃ TR : TypedRed X, ∀ v, TR.psi0 v ≠ 1

def FundNC : Prop :=
  ∀ (D : D7) (X : HidaSetting D), X.LevelSubgroupCharacter → ∀ u : D.what₂.Word, ∃ FN : Set X.B.I.Ginf, IsSFund X.B.I (NOinf X u) FN

def LocC : Prop :=
  ∀ D : D7, ∃ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) ∧
    ∀ (p : Formalism.MainNotions.S.LocalSplitGroups.PlF D) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal →
      δ p = (D.s.atP p).ιF (((D.host.g 0 : ℕ) : D.host.F) * ((D.host.g 1 : ℕ) : D.host.F) /
        ((D.host.g i : ℕ) : D.host.F))

/- English proof (translation)
Introduce `D X hK`. Take `⟨TR, hTR⟩` from `h1 D X hK`. Establish `h2 : ∀ u : D.what₂.Word, ∃ what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V), IsRowReps D (X.Fu u) what₂ ∧ (∀ Λ ∈ what₂, Formalism.L2.SG.Saturated.IsSplitRow D (X.Fu u) Λ) ∧ ∃ cs : ColSys X u what₂, ColReps hK cs`. Introduce `u`. Take `⟨a0, a1, a2, a3, a4, a5, a6⟩` from `hR D X hK u`.

Conclude with `rowsCols_of X u hK a0 a1 a2 a3 a4 a5 a6`. Use `choose what₂ hrows hsplit cs hcs using h2`. Use `choose Dt hDt using fun u => repsExist X u`. Use `choose FN hFN using h3 D X hK`. Take `⟨δ, M, hag, hpin⟩` from `h4 D`.

Conclude with `⟨⟨hK, TR, hTR, what₂, hrows, hsplit, cs, hcs, Dt, hDt, FN, hFN, δ, M, hag, hpin⟩⟩`.
-/
theorem fullExists_of (h1 : TRExistsC) (hR : RowStepsC) (h3 : FundNC) (h4 : LocC) : FullExists := by
  intro D X hK
  obtain ⟨TR, hTR⟩ := h1 D X hK
  have h2 : ∀ u : D.what₂.Word, ∃ what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V), IsRowReps D (X.Fu u) what₂ ∧
      (∀ Λ ∈ what₂, Formalism.L2.SG.Saturated.IsSplitRow D (X.Fu u) Λ) ∧ ∃ cs : ColSys X u what₂, ColReps hK cs := by
    intro u
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hR D X hK u
    exact rowsCols_of X u hK a0 a1 a2 a3 a4 a5 a6
  choose what₂ hrows hsplit cs hcs using h2
  choose Dt hDt using fun u => repsExist X u
  choose FN hFN using h3 D X hK
  obtain ⟨δ, M, hag, hpin⟩ := h4 D
  exact ⟨⟨hK, TR, hTR, what₂, hrows, hsplit, cs, hcs, Dt, hDt, FN, hFN, δ, M, hag, hpin⟩⟩

section R0

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨δ y, ⟨y, hy, rfl⟩, rfl⟩`.

Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`.
-/
theorem gmap_mul' (γ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (γ * δ) Λ = Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.gmap δ Λ) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨δ y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]`. Conclude with `⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩`.
-/
theorem gmap_one' (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) Λ = Λ := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨δ y, ⟨y, hy, rfl⟩, rfl⟩`.

Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`.
-/
theorem kmap_mul (γ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (W : Submodule D.host.E (VS D).V) :
    W.map ((γ * δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
      (W.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V)).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨δ y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Submodule.mem_map]`. Conclude with `⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩`.
-/
theorem kmap_one (W : Submodule D.host.E (VS D).V) :
    W.map ((1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) = W := by
  ext x
  simp only [Submodule.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

/- English proof (translation)
Establish `st_one : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D (X.Fu u)` using `⟨one_mem _, fun j => kmap_one _, rfl⟩`. Establish `st_mul : ∀ γ ∈ stabF D (X.Fu u), ∀ δ ∈ stabF D (X.Fu u), γ * δ ∈ stabF D (X.Fu u)`. Introduce `γ hγ δ hδ`. Use `⟨mul_mem hγ.1 hδ.1, fun j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[kmap_mul, hδ.2.1 j, hγ.2.1 j]`.

Use `show γ (δ (X.Fu u).z) = (X.Fu u).z`. Rewrite using `[hδ.2.2, hγ.2.2]`. Establish `st_inv : ∀ γ ∈ stabF D (X.Fu u), γ⁻¹ ∈ stabF D (X.Fu u)`. Introduce `γ hγ`. Use `⟨inv_mem hγ.1, fun j => ?_, ?_⟩` and prove the remaining obligations.

Use `conv_lhs => rw [← hγ.2.1 j]`. Rewrite using `[← kmap_mul, inv_mul_cancel, kmap_one]`. Use `show γ.symm (X.Fu u).z = (X.Fu u).z conv_lhs => rw [← hγ.2.2]`. Conclude with `γ.symm_apply_apply _`. Use `⟨fun Λ => ⟨1, st_one, gmap_one' Λ⟩, fun h => ?_, fun h1 h2 => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ, rfl⟩` from `h`. Conclude with `⟨γ⁻¹, st_inv γ hγ, by rw [← gmap_mul', inv_mul_cancel, gmap_one']⟩`. Take `⟨γ, hγ, rfl⟩` from `h1`. Take `⟨δ, hδ, rfl⟩` from `h2`. Conclude with `⟨δ * γ, st_mul δ hδ γ hγ, gmap_mul' δ γ _⟩`.
-/
theorem eqvEquiv : EqvEquiv X u := by
  have st_one : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D (X.Fu u) :=
    ⟨one_mem _, fun j => kmap_one _, rfl⟩
  have st_mul : ∀ γ ∈ stabF D (X.Fu u), ∀ δ ∈ stabF D (X.Fu u), γ * δ ∈ stabF D (X.Fu u) := by
    intro γ hγ δ hδ
    refine ⟨mul_mem hγ.1 hδ.1, fun j => ?_, ?_⟩
    · rw [kmap_mul, hδ.2.1 j, hγ.2.1 j]
    · show γ (δ (X.Fu u).z) = (X.Fu u).z
      rw [hδ.2.2, hγ.2.2]
  have st_inv : ∀ γ ∈ stabF D (X.Fu u), γ⁻¹ ∈ stabF D (X.Fu u) := by
    intro γ hγ
    refine ⟨inv_mem hγ.1, fun j => ?_, ?_⟩
    · conv_lhs => rw [← hγ.2.1 j]
      rw [← kmap_mul, inv_mul_cancel, kmap_one]
    · show γ.symm (X.Fu u).z = (X.Fu u).z
      conv_lhs => rw [← hγ.2.2]
      exact γ.symm_apply_apply _
  refine ⟨fun Λ => ⟨1, st_one, gmap_one' Λ⟩, fun h => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨γ, hγ, rfl⟩ := h
    exact ⟨γ⁻¹, st_inv γ hγ, by rw [← gmap_mul', inv_mul_cancel, gmap_one']⟩
  · obtain ⟨γ, hγ, rfl⟩ := h1
    obtain ⟨δ, hδ, rfl⟩ := h2
    exact ⟨δ * γ, st_mul δ hδ γ hγ, gmap_mul' δ γ _⟩

end R0

section R6

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def GamIsom : Prop :=
  ∀ g : Gam X u, ∃ γ : (VS D).V ≃ₗ[D.host.E] (VS D).V, γ ∈ stabF D (X.Fu u) ∧
    ∀ y, incl X.B.I (X.crd (γ y)) = X.B.I.fmat (g : X.B.I.GA).2 *ᵥ incl X.B.I (X.crd y)

/- English proof (translation)
Introduce `h g κ Λ Λ' hΛ hΛ'`. Take `⟨γ, hγ, hγc⟩` from `hG g`. Use `⟨γ, hγ, ?_⟩` and prove the remaining obligations. Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[hΛ']`.

Use extensionality with `y`. Establish `e2 : X.B.I.fmat ((g : X.B.I.GA).2)⁻¹ * X.B.I.fmat (g : X.B.I.GA).2 = 1`. Simplify using `[Formalism.MainNotions.S.AutInst.fmat]`. Establish `hinv : incl X.B.I (X.crd (γ.symm y)) = X.B.I.fmat ((g : X.B.I.GA).2)⁻¹ *ᵥ incl X.B.I (X.crd y)`. Establish `h1` using `hγc (γ.symm y)`.

Rewrite `h1` using `[γ.apply_symm_apply]`. Rewrite using `[h1, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]`. Establish `hmap : y ∈ (Formalism.HermitianLatticesTheory.gmap γ Λ : Set (VS D).V) ↔ γ.symm y ∈ Λ`. Simplify using `only [SetLike.mem_coe, Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `using hx`. Introduce `hy`. Conclude with `⟨γ.symm y, hy, by simp⟩`. Use `set k : X.B.I.Gf := (X.xu u)⁻¹ * (κ : X.B.I.Gf) * X.xu u with hkdef`.

Establish `hk : k ∈ X.B.I.Kset` using `(κ.2 : k ∈ X.K2).1`. Establish `ekk : X.B.I.fmat k * X.B.I.fmat k⁻¹ = 1` using `by simp [Formalism.MainNotions.S.AutInst.fmat]`. Establish `hkinv : ∀ w, w ∈ X.B.I.Lf ↔ X.B.I.fmat k⁻¹ *ᵥ w ∈ X.B.I.Lf` using `fun w => by`. Use `hk (X.B.I.fmat k⁻¹ *ᵥ w)` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ekk, Matrix.one_mulVec]`.

Conclude with `this.symm`. Establish `egrp : (((iotaF X u g * h * (κ : Hfin X u) : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ = k⁻¹ * ((((h : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ * ((g : X.B.I.GA).2)⁻¹)`. Rewrite using `[hkdef]`. Simplify using `only [Subgroup.coe_mul]`. Use `show ((g : X.B.I.GA).2 * (h : X.B.I.Gf) * (κ : X.B.I.Gf) * X.xu u)⁻¹ = _`.

Use `group`. Rewrite using `[hmap, ← SetLike.mem_coe, hΛ]`. Use `show X.B.I.fmat (((h : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (γ.symm y)) ∈ X.B.I.Lf ↔ X.B.I.fmat (((iotaF X u g * h * (κ : Hfin X u) : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf`. Establish `ef : ∀ a b : X.B.I.Gf, X.B.I.fmat (a * b) = X.B.I.fmat a * X.B.I.fmat b` using `fun _ _ => rfl`. Rewrite using `[hinv, egrp, ef, ← Matrix.mulVec_mulVec, ← hkinv, ef, ← Matrix.mulVec_mulVec]`.
-/
theorem latCompat_of (hK : X.LevelSubgroupCharacter) (hG : GamIsom X u) : LatCompat X u hK := by
  intro h g κ Λ Λ' hΛ hΛ'
  obtain ⟨γ, hγ, hγc⟩ := hG g
  refine ⟨γ, hγ, ?_⟩
  apply SetLike.coe_injective
  rw [hΛ']
  ext y
  have e2 : X.B.I.fmat ((g : X.B.I.GA).2)⁻¹ * X.B.I.fmat (g : X.B.I.GA).2 = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have hinv : incl X.B.I (X.crd (γ.symm y)) =
      X.B.I.fmat ((g : X.B.I.GA).2)⁻¹ *ᵥ incl X.B.I (X.crd y) := by
    have h1 := hγc (γ.symm y)
    rw [γ.apply_symm_apply] at h1
    rw [h1, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  have hmap : y ∈ (Formalism.HermitianLatticesTheory.gmap γ Λ : Set (VS D).V) ↔ γ.symm y ∈ Λ := by
    simp only [SetLike.mem_coe, Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨γ.symm y, hy, by simp⟩
  set k : X.B.I.Gf := (X.xu u)⁻¹ * (κ : X.B.I.Gf) * X.xu u with hkdef
  have hk : k ∈ X.B.I.Kset := (κ.2 : k ∈ X.K2).1
  have ekk : X.B.I.fmat k * X.B.I.fmat k⁻¹ = 1 := by simp [Formalism.MainNotions.S.AutInst.fmat]
  have hkinv : ∀ w, w ∈ X.B.I.Lf ↔ X.B.I.fmat k⁻¹ *ᵥ w ∈ X.B.I.Lf := fun w => by
    have := hk (X.B.I.fmat k⁻¹ *ᵥ w)
    rw [Matrix.mulVec_mulVec, ekk, Matrix.one_mulVec] at this
    exact this.symm
  have egrp : (((iotaF X u g * h * (κ : Hfin X u) : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ =
      k⁻¹ * ((((h : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ * ((g : X.B.I.GA).2)⁻¹) := by
    rw [hkdef]
    simp only [Subgroup.coe_mul]
    show ((g : X.B.I.GA).2 * (h : X.B.I.Gf) * (κ : X.B.I.Gf) * X.xu u)⁻¹ = _
    group
  rw [hmap, ← SetLike.mem_coe, hΛ]
  show X.B.I.fmat (((h : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (γ.symm y)) ∈ X.B.I.Lf ↔
    X.B.I.fmat (((iotaF X u g * h * (κ : Hfin X u) : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ
      incl X.B.I (X.crd y) ∈ X.B.I.Lf
  have ef : ∀ a b : X.B.I.Gf, X.B.I.fmat (a * b) = X.B.I.fmat a * X.B.I.fmat b := fun _ _ => rfl
  rw [hinv, egrp, ef, ← Matrix.mulVec_mulVec, ← hkinv, ef, ← Matrix.mulVec_mulVec]

end R6

section V1

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Assemble the required witnesses or components as `⟨inFl_mul hg.1 hh.1, fun y hy => fl_mul (fl_map_le hg.1.1 r) (hg.2 y hy) (hh.2 y hy)⟩`.
-/
theorem inN_mul {ε : Fin X.B.I.n → Bool} {r : ℕ} {e : Fin r → Fin X.B.I.n → ℂ} {z : Fin X.B.I.n → ℂ}
    {g h : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ} (hg : InN ε e z g) (hh : InN ε e z h) : InN ε e z (g * h) :=
  ⟨inFl_mul hg.1 hh.1, fun y hy => fl_mul (fl_map_le hg.1.1 r) (hg.2 y hy) (hh.2 y hy)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨inFl_inv hhg hg.1, fun y hy => fl_inv hhg (fl_le_map hg.1.1 r) (hg.2 y hy)⟩`.
-/
theorem inN_inv {ε : Fin X.B.I.n → Bool} {r : ℕ} {e : Fin r → Fin X.B.I.n → ℂ} {z : Fin X.B.I.n → ℂ}
    {g h : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ} (hhg : h * g = 1) (hg : InN ε e z g) : InN ε e z h :=
  ⟨inFl_inv hhg hg.1, fun y hy => fl_inv hhg (fl_le_map hg.1.1 r) (hg.2 y hy)⟩

/- English proof (translation)
Introduce and unpack `s ⟨γ, hγ, rfl, hγN, hγF, hγK⟩ t ⟨δ, hδ, rfl, hδN, hδF, hδK⟩`. Establish `hN` using `Formalism.L2.SG.PoincareInHH.Cut.nfinGroup_holds (X := X) (u := u)`. Use `⟨δ * γ⁻¹, (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem hδ ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).inv_mem hγ), rfl, fun v => ?_, (hN.1 _ hδF _ (hN.2 _ hγF)).1, ?_⟩` and prove the remaining obligations. Establish `e1 : uMat ((δ * γ⁻¹).1 v) = uMat (δ.1 v) * uMat (γ.1⁻¹ v)` using `by simp [uMat]`. Establish `e2 : uMat (γ.1⁻¹ v) * uMat (γ.1 v) = 1` using `by simp [uMat]`.

Rewrite using `[e1]`. Conclude with `inN_mul X (hδN v) (inN_inv X e2 (hγN v))`. Use `hK.2.1 _ hδK _ (hK.2.2.1 _ hγK)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Prod.snd_mul, Prod.snd_inv]`.

Use `group`.
-/
theorem noSub (hK : X.LevelSubgroupCharacter) : NOSub X u := by
  rintro s ⟨γ, hγ, rfl, hγN, hγF, hγK⟩ t ⟨δ, hδ, rfl, hδN, hδF, hδK⟩
  have hN := Formalism.L2.SG.PoincareInHH.Cut.nfinGroup_holds (X := X) (u := u)
  refine ⟨δ * γ⁻¹, (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem hδ ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).inv_mem hγ), rfl,
    fun v => ?_, (hN.1 _ hδF _ (hN.2 _ hγF)).1, ?_⟩
  · have e1 : uMat ((δ * γ⁻¹).1 v) = uMat (δ.1 v) * uMat (γ.1⁻¹ v) := by simp [uMat]
    have e2 : uMat (γ.1⁻¹ v) * uMat (γ.1 v) = 1 := by simp [uMat]
    rw [e1]
    exact inN_mul X (hδN v) (inN_inv X e2 (hγN v))
  · have := hK.2.1 _ hδK _ (hK.2.2.1 _ hγK)
    convert this using 1
    simp only [Prod.snd_mul, Prod.snd_inv]
    group

end V1

/- English proof (translation)
Introduce `_ X hK u` and use `noSub X u hK`.
-/
theorem noSubC : NOSubC := fun _ X hK u => noSub X u hK

def RowStepsC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    LatSub X u ∧ LatRow X u ∧ LatSurj X u ∧ LatInj X u ∧ ClassFin X u hK ∧ GamIsom X u

/- English proof (translation)
Introduce `D X hK u` and use `let ⟨a1, a2, a3, a4, a5, a6⟩ := h D X hK u ⟨eqvEquiv X u, a1, a2, a3, a4, a5, latCompat_of X u hK a6⟩`.
-/
theorem rowStepsC_of (h : RowStepsC') : RowStepsC := fun D X hK u =>
  let ⟨a1, a2, a3, a4, a5, a6⟩ := h D X hK u
  ⟨eqvEquiv X u, a1, a2, a3, a4, a5, latCompat_of X u hK a6⟩

/- English proof (translation)
The claim follows from `volPosC_of noSubC h2 h3 h4`.
-/
theorem volPosC_of' (h2 : NOCountC) (h3 : NOCofiniteC) (h4 : HFiniteC) : VolPosC :=
  volPosC_of noSubC h2 h3 h4

/- English proof (translation)
The claim follows from `fullExists_of h1 (rowStepsC_of hR) h3 h4`.
-/
theorem fullExists_of' (h1 : TRExistsC) (hR : RowStepsC') (h3 : FundNC) (h4 : LocC) : FullExists :=
  fullExists_of h1 (rowStepsC_of hR) h3 h4

section R6a

variable {D : D7} (X : HidaSetting D)

def matL (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  X.bas.equivFun.symm.toLinearMap ∘ₗ Matrix.toLin' A ∘ₗ X.bas.equivFun.toLinearMap

/- English proof (translation)
Use `show X.bas.equivFun (X.bas.equivFun.symm (Matrix.toLin' A (X.bas.equivFun y))) = _`. Rewrite using `[LinearEquiv.apply_symm_apply, Matrix.toLin'_apply]`.
-/
theorem matL_repr (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E) (y : (VS D).V) :
    X.bas.equivFun (matL X A y) = A *ᵥ X.bas.equivFun y := by
  show X.bas.equivFun (X.bas.equivFun.symm (Matrix.toLin' A (X.bas.equivFun y))) = _
  rw [LinearEquiv.apply_symm_apply, Matrix.toLin'_apply]

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Apply `X.bas.equivFun.injective` to reduce the goal to its premises. Simplify using `only [LinearMap.comp_apply, matL_repr, Matrix.mulVec_mulVec]`.
-/
theorem matL_mul (A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E) :
    matL X (A * B) = matL X A ∘ₗ matL X B := by
  apply LinearMap.ext
  intro y
  apply X.bas.equivFun.injective
  simp only [LinearMap.comp_apply, matL_repr, Matrix.mulVec_mulVec]

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Apply `X.bas.equivFun.injective` to reduce the goal to its premises. Simplify using `only [matL_repr, Matrix.one_mulVec, LinearMap.id_apply]`.
-/
theorem matL_one : matL X 1 = LinearMap.id := by
  apply LinearMap.ext
  intro y
  apply X.bas.equivFun.injective
  simp only [matL_repr, Matrix.one_mulVec, LinearMap.id_apply]

abbrev mapM : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E →+* Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E :=
  (X.ιE : X.B.I.E →+* D.host.E).mapMatrix

def matE (M : GL (Fin X.B.I.n) X.B.I.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (matL X (mapM X (M : Matrix _ _ _))) (matL X (mapM X ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix _ _ _)))
    (by rw [← matL_mul, ← map_mul, M.mul_inv, map_one, matL_one])
    (by rw [← matL_mul, ← map_mul, M.inv_mul, map_one, matL_one])

/- English proof (translation)
The claim follows from `matL_repr X _ y`.
-/
theorem matE_repr (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.bas.equivFun (matE X M y) = mapM X (M : Matrix _ _ _) *ᵥ X.bas.equivFun y :=
  matL_repr X _ y

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h` using `RingHom.map_mulVec (X.ιE.symm : D.host.E →+* X.B.I.E) (mapM X (M : Matrix _ _ _)) (X.bas.equivFun y) i`. Establish `hM : (mapM X (M : Matrix _ _ _)).map (X.ιE.symm : D.host.E →+* X.B.I.E) = (M : Matrix _ _ _)`. Use extensionality with `a b`. Simplify using `[mapM]`.

Establish `e1 : X.crd (matE X M y) i = X.ιE.symm ((mapM X (M : Matrix _ _ _) *ᵥ X.bas.equivFun y) i)`. Rewrite using `[← matE_repr]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Use `erw [h, hM]`.

Both sides reduce to the same expression.
-/
theorem matE_crd (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (matE X M y) = (M : Matrix _ _ _) *ᵥ X.crd y := by
  funext i
  have h := RingHom.map_mulVec (X.ιE.symm : D.host.E →+* X.B.I.E) (mapM X (M : Matrix _ _ _))
    (X.bas.equivFun y) i
  have hM : (mapM X (M : Matrix _ _ _)).map (X.ιE.symm : D.host.E →+* X.B.I.E) = (M : Matrix _ _ _) := by
    ext a b
    simp [mapM]
  have e1 : X.crd (matE X M y) i = X.ιE.symm ((mapM X (M : Matrix _ _ _) *ᵥ X.bas.equivFun y) i) := by
    rw [← matE_repr]
    rfl
  rw [e1]
  erw [h, hM]
  rfl

/- English proof (translation)
Rewrite using `[matE_crd]`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (M : Matrix _ _ _) (X.crd y) i`.
-/
theorem matE_incl (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    incl X.B.I (X.crd (matE X M y)) =
      (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ incl X.B.I (X.crd y) := by
  rw [matE_crd]
  funext i
  exact RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (M : Matrix _ _ _) (X.crd y) i

end R6a

section NormLeOneOfIntegral

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Use `conv_lhs => rw [← X.bas.sum_equivFun x, ← X.bas.sum_equivFun y]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_expand (x y : (VS D).V) :
    (VS D).hT x y =
      ∑ i, ∑ j, star (X.bas.equivFun x i) * (X.bas.equivFun y j * (VS D).hT (X.bas i) (X.bas j)) := by
  conv_lhs => rw [← X.bas.sum_equivFun x, ← X.bas.sum_equivFun y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mapM, RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.coe_toRingHom]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qform (a c : Fin X.B.I.n → D.host.E) :
    ∑ i, ∑ j, star (a i) * (c j * X.ιE (X.B.I.J i j)) = star a ⬝ᵥ (mapM X X.B.I.J *ᵥ c) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mapM, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingEquiv.coe_toRingHom]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `hM' : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _) * X.B.I.J * (M : Matrix _ _ _) = X.B.I.J` using `hM`. Establish `h` using `congrArg (mapM X) hM'`. Rewrite `h` using `[map_mul, map_mul]`. Establish `hA : (mapM X (M : Matrix _ _ _))ᴴ = mapM X (Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _))`. Use extensionality with `i j`.

Simplify using `only [mapM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.UG.cT, Matrix.transpose_apply, starRingEnd_apply, RingEquiv.coe_toRingHom, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]`. Rewrite using `[hA]`. Conclude with `h`.
-/
theorem mapM_unitary (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    (mapM X (M : Matrix _ _ _))ᴴ * mapM X X.B.I.J * mapM X (M : Matrix _ _ _) = mapM X X.B.I.J := by
  have hM' : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _) * X.B.I.J * (M : Matrix _ _ _) = X.B.I.J := hM
  have h := congrArg (mapM X) hM'
  rw [map_mul, map_mul] at h
  have hA : (mapM X (M : Matrix _ _ _))ᴴ = mapM X (Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _)) := by
    ext i j
    simp only [mapM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.UG.cT,
      Matrix.transpose_apply, starRingEnd_apply, RingEquiv.coe_toRingHom, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]
  rw [hA]
  exact h

/- English proof (translation)
Introduce `x y`. Rewrite using `[hT_expand X (matE X M x) (matE X M y), hT_expand X x y]`. Simplify using `only [← X.J_eq]`. Rewrite using `[qform, qform, matE_repr, matE_repr]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]`. Use `_ = star (X.bas.equivFun x) ⬝ᵥ (mapM X X.B.I.J *ᵥ X.bas.equivFun y) := by`. Rewrite using `[mapM_unitary X M hM, Matrix.dotProduct_mulVec]`.
-/
theorem matE_isom (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    matE X M ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  intro x y
  rw [hT_expand X (matE X M x) (matE X M y), hT_expand X x y]
  simp only [← X.J_eq]
  rw [qform, qform, matE_repr, matE_repr]
  calc star (mapM X (M : Matrix _ _ _) *ᵥ X.bas.equivFun x) ⬝ᵥ
        (mapM X X.B.I.J *ᵥ (mapM X (M : Matrix _ _ _) *ᵥ X.bas.equivFun y))
      = (star (X.bas.equivFun x) ᵥ* ((mapM X (M : Matrix _ _ _))ᴴ * mapM X X.B.I.J * mapM X (M : Matrix _ _ _))) ⬝ᵥ
          X.bas.equivFun y := by
        rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
          Matrix.mul_assoc]
    _ = star (X.bas.equivFun x) ⬝ᵥ (mapM X X.B.I.J *ᵥ X.bas.equivFun y) := by
        rw [mapM_unitary X M hM, Matrix.dotProduct_mulVec]

def InclInj : Prop :=
  Function.Injective (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) : X.B.I.E → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)

/- English proof (translation)
Introduce `g`. Take `⟨hGF, hH⟩` from `Subgroup.mem_inf.1 g.2`. Establish `hGF' : (g : X.B.I.GA) ∈ X.B.I.GFset` using `hGF`. Take `⟨M, hM, -, hf⟩` from `hGF'`. Establish `hfin` using `(Subgroup.mem_prod.1 hH).2`.

Establish `hincl : ∀ y, incl X.B.I (X.crd (matE X M y)) = X.B.I.fmat (g : X.B.I.GA).2 *ᵥ incl X.B.I (X.crd y)` using `fun y => by rw [matE_incl, hf]`. Establish `hfix : ∀ y, X.crd y ∈ fixSet X u → matE X M y = y`. Introduce `y hy`. Establish `h1 : incl X.B.I (X.crd (matE X M y)) = incl X.B.I (X.crd y)`. Rewrite using `[hincl]`.

Conclude with `hfin _ hy`. Apply `X.bas.equivFun.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Conclude with `X.ιE.symm.injective (hI (congrFun h1 i))`. Use `⟨matE X M, ⟨matE_isom X M hM, fun j => ?_, ?_⟩, hincl⟩` and prove the remaining obligations.

Unfold `Formalism.MainNotions.S.FlagG.Xa`. Rewrite using `[Submodule.map_span, Set.image_image]`. Use `congr 1`. Apply `Set.image_congr` to reduce the goal to its premises. Introduce `a _`.

Rewrite using `[X.Fu_e u]`. Conclude with `hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))`. Use `show matE X M (X.Fu u).z = (X.Fu u).z`. Rewrite using `[X.flagZVector u]`. Conclude with `hfix _ (Or.inr rfl)`.
-/
theorem gamIsom_of (hI : InclInj X) (u : D.what₂.Word) : GamIsom X u := by
  intro g
  obtain ⟨hGF, hH⟩ := Subgroup.mem_inf.1 g.2
  have hGF' : (g : X.B.I.GA) ∈ X.B.I.GFset := hGF
  obtain ⟨M, hM, -, hf⟩ := hGF'
  have hfin := (Subgroup.mem_prod.1 hH).2
  have hincl : ∀ y, incl X.B.I (X.crd (matE X M y)) = X.B.I.fmat (g : X.B.I.GA).2 *ᵥ incl X.B.I (X.crd y) :=
    fun y => by rw [matE_incl, hf]
  have hfix : ∀ y, X.crd y ∈ fixSet X u → matE X M y = y := by
    intro y hy
    have h1 : incl X.B.I (X.crd (matE X M y)) = incl X.B.I (X.crd y) := by
      rw [hincl]
      exact hfin _ hy
    apply X.bas.equivFun.injective
    funext i
    exact X.ιE.symm.injective (hI (congrFun h1 i))
  refine ⟨matE X M, ⟨matE_isom X M hM, fun j => ?_, ?_⟩, hincl⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro a _
    rw [X.Fu_e u]
    exact hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
  · show matE X M (X.Fu u).z = (X.Fu u).z
    rw [X.flagZVector u]
    exact hfix _ (Or.inr rfl)

end NormLeOneOfIntegral

section R1

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Introduce `h`. Establish `e0 : incl X.B.I (X.crd 0) = 0`. Use function extensionality and compare the values at `i`. Simplify using `[incl, HidaSetting.crd, crdOf]`. Establish `e1 : ∀ a b : (VS D).V, incl X.B.I (X.crd (a + b)) = incl X.B.I (X.crd a) + incl X.B.I (X.crd b)`.

Introduce `a b`. Use function extensionality and compare the values at `i`. Simplify using `[incl, HidaSetting.crd, crdOf]`. Establish `e2 : ∀ (c : 𝓞 D.host.E) (y : (VS D).V), incl X.B.I (X.crd (c • y)) = Formalism.UG.inclE (F` using `X.B.I.F) (Af X.B.I.F) (X.ιE.symm (c : D.host.E)) • incl X.B.I (X.crd y) := by`. Introduce `c y`.

Establish `hcy : c • y = (c : D.host.E) • y` using `(IsScalarTower.algebraMap_smul D.host.E c y).symm`. Use function extensionality and compare the values at `i`. Rewrite using `[hcy]`. Simplify using `only [incl, HidaSetting.crd, crdOf, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]`. Establish `hint : ∀ c : 𝓞 D.host.E, Formalism.UG.inclE (F` using `X.B.I.F) (Af X.B.I.F) (X.ιE.symm (c : D.host.E)) ∈ IntAf X.B.I.F X.B.I.E := fun c => nt_inclE_mem X.B.I _ ((NumberField.RingOfIntegers.isIntegral_coe c).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom)`.

Set `Λ : Submodule (𝓞 D.host.E) (VS D).V` to `{ carrier := latOf X u h add_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `X.B.I.fmat _ *ᵥ incl X.B.I (X.crd (a + b)) ∈ X.B.I.Lf`. Rewrite using `[e1, Matrix.mulVec_add]`. Conclude with `add_mem ha hb`. Use the proof step `zero_mem' := by`.

Express the relevant statement in the definitionally equal form `X.B.I.fmat _ *ᵥ incl X.B.I (X.crd 0) ∈ X.B.I.Lf`. Rewrite using `[e0, Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Use the proof step `smul_mem' := fun c y hy => by`. Express the relevant statement in the definitionally equal form `X.B.I.fmat _ *ᵥ incl X.B.I (X.crd (c • y)) ∈ X.B.I.Lf`.

Rewrite using `[e2, Matrix.mulVec_smul]`. Conclude with `X.B.I.Lf.smul_mem ⟨_, hint c⟩ hy }`. Conclude with `⟨Λ, rfl⟩`.
-/
theorem latSub : LatSub X u := by
  intro h
  have e0 : incl X.B.I (X.crd 0) = 0 := by
    funext i
    simp [incl, HidaSetting.crd, crdOf]
  have e1 : ∀ a b : (VS D).V, incl X.B.I (X.crd (a + b)) = incl X.B.I (X.crd a) + incl X.B.I (X.crd b) := by
    intro a b
    funext i
    simp [incl, HidaSetting.crd, crdOf]
  have e2 : ∀ (c : 𝓞 D.host.E) (y : (VS D).V), incl X.B.I (X.crd (c • y)) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (c : D.host.E)) • incl X.B.I (X.crd y) := by
    intro c y
    have hcy : c • y = (c : D.host.E) • y := (IsScalarTower.algebraMap_smul D.host.E c y).symm
    funext i
    rw [hcy]
    simp only [incl, HidaSetting.crd, crdOf, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]
  have hint : ∀ c : 𝓞 D.host.E, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (c : D.host.E)) ∈
      IntAf X.B.I.F X.B.I.E := fun c =>
    nt_inclE_mem X.B.I _
      ((NumberField.RingOfIntegers.isIntegral_coe c).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom)
  let Λ : Submodule (𝓞 D.host.E) (VS D).V :=
    { carrier := latOf X u h
      add_mem' := fun {a b} ha hb => by
        change X.B.I.fmat _ *ᵥ incl X.B.I (X.crd (a + b)) ∈ X.B.I.Lf
        rw [e1, Matrix.mulVec_add]
        exact add_mem ha hb
      zero_mem' := by
        change X.B.I.fmat _ *ᵥ incl X.B.I (X.crd 0) ∈ X.B.I.Lf
        rw [e0, Matrix.mulVec_zero]
        exact zero_mem _
      smul_mem' := fun c y hy => by
        change X.B.I.fmat _ *ᵥ incl X.B.I (X.crd (c • y)) ∈ X.B.I.Lf
        rw [e2, Matrix.mulVec_smul]
        exact X.B.I.Lf.smul_mem ⟨_, hint c⟩ hy }
  exact ⟨Λ, rfl⟩

def LatRowLat : Prop :=
  ∀ (h : Hfin X u) (Λ : Submodule (𝓞 D.host.E) (VS D).V), (Λ : Set (VS D).V) = latOf X u h →
    IsRowLat D (X.Fu u) Λ

/- English proof (translation)
Introduce `g Λ hΛ` and use `⟨h g Λ hΛ, Formalism.L2.SG.Closed.IsSplitRow_holds D u (X.Fu u) Λ (h g Λ hΛ)⟩`.
-/
theorem latRow_of (h : LatRowLat X u) : LatRow X u := fun g Λ hΛ =>
  ⟨h g Λ hΛ, Formalism.L2.SG.Closed.IsSplitRow_holds D u (X.Fu u) Λ (h g Λ hΛ)⟩

end R1

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Set `v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)` to `⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)⟩`. Use `⟨⟨0, 1, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h' : (0 : Af F) v = (1 : Af F) v` using `by rw [h]`. Conclude with `zero_ne_one (α := v.adicCompletion F) h'`.
-/
theorem af_nontriv (F : Type) [Field F] [NumberField F] : Nontrivial (Af F) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' : (0 : Af F) v = (1 : Af F) v := by rw [h]
  exact zero_ne_one (α := v.adicCompletion F) h'

/- English proof (translation)
Use `haveI := af_nontriv X.B.I.F`. Conclude with `Algebra.TensorProduct.includeLeft_injective (S := X.B.I.F) (algebraMap X.B.I.F (Af X.B.I.F)).injective`.
-/
theorem inclInj_holds {D : D7} (X : HidaSetting D) : InclInj X := by
  haveI := af_nontriv X.B.I.F
  exact Algebra.TensorProduct.includeLeft_injective (S := X.B.I.F) (algebraMap X.B.I.F (Af X.B.I.F)).injective

/- English proof (translation)
Establish `hK` using `Formalism.L2.SG.Closed.level_subgroup_is_group X`. Use `haveI := NOsub_discrete X u hK`. Establish `hc : Countable (NOsub X u hK)` using `countable_of_discrete (NOsub X u hK)`. Rewrite using `[NOCount, ← NOsub_coe X u hK]`. Conclude with `Set.countable_coe_iff.1 hc`.
-/
theorem noCount {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : NOCount X u := by
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  haveI := NOsub_discrete X u hK
  have hc : Countable (NOsub X u hK) := countable_of_discrete (NOsub X u hK)
  rw [NOCount, ← NOsub_coe X u hK]
  exact Set.countable_coe_iff.1 hc

/- English proof (translation)
Introduce `_ X u` and use `noCount X u`.
-/
theorem noCountC : NOCountC := fun _ X u => noCount X u

/- English proof (translation)
The claim follows from `volPosC_of' noCountC h3 h4`.
-/
theorem volPosC_of'' (h3 : NOCofiniteC) (h4 : HFiniteC) : VolPosC := volPosC_of' noCountC h3 h4

def RowStepsC'' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    LatRowLat X u ∧ LatSurj X u ∧ LatInj X u ∧ ClassFin X u hK

/- English proof (translation)
The claim follows from `fullExists_of' h1 (fun D X hK u => let ⟨a2, a3, a4, a5⟩ := hR D X hK u ⟨latSub X u, latRow_of X u a2, a3, a4, a5, gamIsom_of X (inclInj_holds X) u⟩) fundNC_holds h4`.
-/
theorem fullExists_of'' (h1 : TRExistsC) (hR : RowStepsC'') (h4 : LocC) : FullExists :=
  fullExists_of' h1 (fun D X hK u =>
    let ⟨a2, a3, a4, a5⟩ := hR D X hK u
    ⟨latSub X u, latRow_of X u a2, a3, a4, a5, gamIsom_of X (inclInj_holds X) u⟩) fundNC_holds h4

/- English proof (translation)
Use `haveI : Finite (Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK)) := h`. Set `f : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK) → Quotient (dcSetoid X u hK)` to `Quotient.lift (fun a => Quotient.mk (dcSetoid X u hK) a) (fun a b hab => Quotient.sound (by`. Take `⟨x, hx, k, hk, rfl⟩` from `DoubleCoset.rel_iff.1 hab`. Take `⟨g, rfl⟩` from `hx`. Conclude with `⟨g, ⟨k, hk⟩, rfl⟩))`.

Conclude with `Finite.of_surjective f (Quotient.ind fun a => ⟨Quotient.mk _ a, rfl⟩)`.
-/
theorem classFin_of {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter)
    (h : Formalism.L2.SG.PoincareInHH.Cut.ClassFin X u hK) : ClassFin X u hK := by
  haveI : Finite (Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK)) := h
  let f : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK) → Quotient (dcSetoid X u hK) :=
    Quotient.lift (fun a => Quotient.mk (dcSetoid X u hK) a) (fun a b hab => Quotient.sound (by
      obtain ⟨x, hx, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
      obtain ⟨g, rfl⟩ := hx
      exact ⟨g, ⟨k, hk⟩, rfl⟩))
  exact Finite.of_surjective f (Quotient.ind fun a => ⟨Quotient.mk _ a, rfl⟩)

def LatticeRowBijectionClassFinite : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    LatRowLat X u ∧ LatSurj X u ∧ LatInj X u ∧ Formalism.L2.SG.PoincareInHH.Cut.ClassFin X u hK

/- English proof (translation)
The claim follows from `fullExists_of'' h1 (fun D X hK u => let ⟨a2, a3, a4, a5⟩ := hR D X hK u ⟨a2, a3, a4, classFin_of X u hK a5⟩) h4`.
-/
theorem full_exists_of_lattice_steps (h1 : TRExistsC) (hR : LatticeRowBijectionClassFinite) (h4 : LocC) : FullExists :=
  fullExists_of'' h1 (fun D X hK u =>
    let ⟨a2, a3, a4, a5⟩ := hR D X hK u
    ⟨a2, a3, a4, classFin_of X u hK a5⟩) h4

end Formalism.L2.SG.Pf

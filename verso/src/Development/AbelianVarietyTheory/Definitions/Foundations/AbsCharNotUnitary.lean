import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Development.AbelianVarietyTheory.Definitions.Foundations.DiagUnitsEqLocalIdele
import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

noncomputable section

open NumberField IsDedekindDomain nonZeroDivisors

namespace GlobalTheory.Mem.Chr.CharModel

section Norm

variable (F : Type) [Field F] [NumberField F]

def infPart : Ideles F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def finPart : Ideles F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def logInf (a : (InfiniteAdeleRing F)ˣ) : ℝ :=
  ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log ‖(a : InfiniteAdeleRing F) w‖

/- English proof (translation)
Introduce `h`. Establish `h1 : (a : InfiniteAdeleRing F) w * ((a⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w = 1` using `congrFun a.mul_inv w`. Rewrite `h1` using `[h, zero_mul]`. Conclude with `zero_ne_one h1`.
-/
theorem inf_ne (a : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) : (a : InfiniteAdeleRing F) w ≠ 0 := by
  intro h
  have h1 : (a : InfiniteAdeleRing F) w * ((a⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w = 1 :=
    congrFun a.mul_inv w
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/- English proof (translation)
Unfold `logInf`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `: ((a * b : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w = (a : InfiniteAdeleRing F) w * (b : InfiniteAdeleRing F) w` using `rfl`. Rewrite using `[this, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (inf_ne F a w)) (norm_ne_zero_iff.2 (inf_ne F b w)), mul_add]`.
-/
theorem logInf_mul (a b : (InfiniteAdeleRing F)ˣ) : logInf F (a * b) = logInf F a + logInf F b := by
  unfold logInf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : ((a * b : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w =
    (a : InfiniteAdeleRing F) w * (b : InfiniteAdeleRing F) w := rfl
  rw [this, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (inf_ne F a w)) (norm_ne_zero_iff.2 (inf_ne F b w)), mul_add]

/- English proof (translation)
Use `logInf_mul F 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logInf_one : logInf F 1 = 0 := by
  have := logInf_mul F 1 1
  rw [mul_one] at this
  linarith

/- English proof (translation)
Unfold `logInf`. Use `continuous_finset_sum _ fun w _ => continuous_const.mul ?_` and prove the remaining obligations. Use `Continuous.log ?_ fun a => norm_ne_zero_iff.2 (inf_ne F a w)` and prove the remaining obligations. Establish `h : Continuous fun x : InfiniteAdeleRing F => x w` using `continuous_apply w`. Conclude with `(h.comp Units.continuous_val).norm`.
-/
theorem continuous_logInf : Continuous (logInf F) := by
  unfold logInf
  refine continuous_finset_sum _ fun w _ => continuous_const.mul ?_
  refine Continuous.log ?_ fun a => norm_ne_zero_iff.2 (inf_ne F a w)
  have h : Continuous fun x : InfiniteAdeleRing F => x w := continuous_apply w
  exact (h.comp Units.continuous_val).norm

def logFin (t : (FiniteAdeleRing (𝓞 F) F)ˣ) : ℝ :=
  Real.log ((FractionalIdeal.absNorm (GlobalTheory.Idele.idealOf t) : ℚ) : ℝ)

/- English proof (translation)
Establish `h : ∀ t : (FiniteAdeleRing (𝓞 F) F)ˣ, ((FractionalIdeal.absNorm (GlobalTheory.Idele.idealOf t) : ℚ) : ℝ) ≠ 0` using `fun t => by simpa [FractionalIdeal.absNorm_eq_zero_iff] using GlobalTheory.Idele.idealOf_ne_zero t`. Unfold `logFin`. Rewrite using `[GlobalTheory.Idele.idealOf_mul, map_mul, Rat.cast_mul, Real.log_mul (h t) (h s)]`.
-/
theorem logFin_mul (t s : (FiniteAdeleRing (𝓞 F) F)ˣ) : logFin F (t * s) = logFin F t + logFin F s := by
  have h : ∀ t : (FiniteAdeleRing (𝓞 F) F)ˣ, ((FractionalIdeal.absNorm (GlobalTheory.Idele.idealOf t) : ℚ) : ℝ) ≠ 0 :=
    fun t => by simpa [FractionalIdeal.absNorm_eq_zero_iff] using GlobalTheory.Idele.idealOf_ne_zero t
  unfold logFin
  rw [GlobalTheory.Idele.idealOf_mul, map_mul, Rat.cast_mul, Real.log_mul (h t) (h s)]

/- English proof (translation)
Use `logFin_mul F 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logFin_one : logFin F 1 = 0 := by
  have := logFin_mul F 1 1
  rw [mul_one] at this
  linarith

/- English proof (translation)
Establish `hO : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F}` using `RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)`. Establish `h1 : ∀ᶠ t : (FiniteAdeleRing (𝓞 F) F)ˣ in nhds 1, ∀ v, (t : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F` using `(hO.preimage (Units.continuous_val (M := FiniteAdeleRing (𝓞 F) F))).mem_nhds (fun v : HeightOneSpectrum (𝓞 F) => one_mem (v.adicCompletionIntegers F))`. Establish `h2 : ∀ᶠ t in nhds (1 : (FiniteAdeleRing (𝓞 F) F)ˣ), ∀ v, ((t⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F` using `(hO.preimage Units.continuous_coe_inv).mem_nhds fun v => one_mem _`. Use `filter_upwards [h1, h2] with t h1 h2`. Establish `: GlobalTheory.Idele.idealOf t = 1`.

Rewrite using `[← GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.smul_eq_self_iff t one_ne_zero]`. Introduce `v`. Establish `e` using `congrArg Valued.v (GlobalTheory.Idele.idele_apply_mul_inv t v)`. Rewrite `e` using `[map_mul, map_one]`. Establish `a1 : Valued.v ((t : FiniteAdeleRing (𝓞 F) F) v) ≤ 1` using `h1 v`.

Establish `a2 : Valued.v (((t⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) ≤ 1` using `h2 v`. Use `le_antisymm a1 ?_` and prove the remaining obligations. Rewrite using `[← e]`. Conclude with `mul_le_of_le_one_right' a2`. Simplify using `[logFin, this]`.
-/
theorem logFin_eventually : ∀ᶠ t in nhds (1 : (FiniteAdeleRing (𝓞 F) F)ˣ), logFin F t = 0 := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have h1 : ∀ᶠ t : (FiniteAdeleRing (𝓞 F) F)ˣ in nhds 1,
      ∀ v, (t : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F :=
    (hO.preimage (Units.continuous_val (M := FiniteAdeleRing (𝓞 F) F))).mem_nhds
      (fun v : HeightOneSpectrum (𝓞 F) => one_mem (v.adicCompletionIntegers F))
  have h2 : ∀ᶠ t in nhds (1 : (FiniteAdeleRing (𝓞 F) F)ˣ),
      ∀ v, ((t⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F :=
    (hO.preimage Units.continuous_coe_inv).mem_nhds fun v => one_mem _
  filter_upwards [h1, h2] with t h1 h2
  have : GlobalTheory.Idele.idealOf t = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.smul_eq_self_iff t one_ne_zero]
    intro v
    have e := congrArg Valued.v (GlobalTheory.Idele.idele_apply_mul_inv t v)
    rw [map_mul, map_one] at e
    have a1 : Valued.v ((t : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 := h1 v
    have a2 : Valued.v (((t⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 := h2 v
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  simp [logFin, this]

def logNorm (a : Ideles F) : ℝ := logInf F (infPart F a) - logFin F (finPart F a)

/- English proof (translation)
Unfold `logNorm`. Rewrite using `[map_mul, map_mul, logInf_mul, logFin_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logNorm_mul (a b : Ideles F) : logNorm F (a * b) = logNorm F a + logNorm F b := by
  unfold logNorm
  rw [map_mul, map_mul, logInf_mul, logFin_mul]
  ring

/- English proof (translation)
Rewrite using `[← InfiniteAdeleRing.coe_norm_eq_abs_norm, InfiniteAdeleRing.norm_def, Real.log_prod]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Real.log_pow]`. Both sides reduce to the same expression. Introduce `w _`.

Conclude with `pow_ne_zero _ (norm_ne_zero_iff.2 (inf_ne F (infPart F (diagUnits F x)) w))`.
-/
theorem logInf_principal (x : Fˣ) :
    logInf F (infPart F (diagUnits F x)) = Real.log ((|Algebra.norm ℚ (x : F)| : ℚ) : ℝ) := by
  rw [← InfiniteAdeleRing.coe_norm_eq_abs_norm, InfiniteAdeleRing.norm_def, Real.log_prod]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
    rfl
  · intro w _
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inf_ne F (infPart F (diagUnits F x)) w))

/- English proof (translation)
Establish `h1 : finPart F (diagUnits F x) = FiniteAdeleRing.unitEmbedding (𝓞 F) F x` using `Units.ext rfl`. Unfold `logNorm logFin`. Rewrite using `[h1, GlobalTheory.Idele.idealOf_unitEmbedding, FractionalIdeal.absNorm_span_singleton, sub_eq_zero, logInf_principal]`.
-/
theorem logNorm_principal (x : Fˣ) : logNorm F (diagUnits F x) = 0 := by
  have h1 : finPart F (diagUnits F x) = FiniteAdeleRing.unitEmbedding (𝓞 F) F x := Units.ext rfl
  unfold logNorm logFin
  rw [h1, GlobalTheory.Idele.idealOf_unitEmbedding, FractionalIdeal.absNorm_span_singleton, sub_eq_zero, logInf_principal]

def absHom (s : ℂ) : Ideles F →* ℂˣ :=
  MonoidHom.mk' (fun a => Units.mk0 (Complex.exp (s * logNorm F a)) (Complex.exp_ne_zero _)) fun a b => by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    rw [logNorm_mul, ← Complex.exp_add]; push_cast; ring_nf

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem absHom_val (s : ℂ) (a : Ideles F) : ((absHom F s a : ℂˣ) : ℂ) = Complex.exp (s * logNorm F a) := rfl

/- English proof (translation)
Set `f : Ideles F →* Multiplicative ℝ` to `MonoidHom.mk' (fun a => Multiplicative.ofAdd (logNorm F a)) fun a b => by rw [logNorm_mul]; rfl`. Establish `c1 : Continuous (infPart F)` using `Continuous.units_map _ continuous_fst`. Establish `c2 : Continuous (finPart F)` using `Continuous.units_map _ continuous_snd`. Establish `h : ∀ᶠ a in nhds (1 : Ideles F), logFin F (finPart F a) = 0`. Use `c2.continuousAt (x := 1)` as an intermediate fact.

Rewrite `this` using `[ContinuousAt, map_one]`. Conclude with `this.eventually (logFin_eventually F)`. Establish `hf : Continuous f`. Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Use `ContinuousAt.congr (f := fun a => Multiplicative.ofAdd (logInf F (infPart F a))) (continuous_ofAdd.comp ((continuous_logInf F).comp c1)).continuousAt ?_` and prove the remaining obligations.

Use `filter_upwards [h] with a ha`. Express the relevant statement in the definitionally equal form `_ = Multiplicative.ofAdd (logNorm F a)`. Rewrite using `[logNorm, ha, sub_zero]`. Conclude with `continuous_toAdd.comp hf`.
-/
theorem continuous_logNorm : Continuous (logNorm F) := by
  let f : Ideles F →* Multiplicative ℝ := MonoidHom.mk' (fun a => Multiplicative.ofAdd (logNorm F a))
    fun a b => by rw [logNorm_mul]; rfl
  have c1 : Continuous (infPart F) := Continuous.units_map _ continuous_fst
  have c2 : Continuous (finPart F) := Continuous.units_map _ continuous_snd
  have h : ∀ᶠ a in nhds (1 : Ideles F), logFin F (finPart F a) = 0 := by
    have := c2.continuousAt (x := 1)
    rw [ContinuousAt, map_one] at this
    exact this.eventually (logFin_eventually F)
  have hf : Continuous f := by
    refine continuous_of_continuousAt_one _ ?_
    refine ContinuousAt.congr (f := fun a => Multiplicative.ofAdd (logInf F (infPart F a)))
      (continuous_ofAdd.comp ((continuous_logInf F).comp c1)).continuousAt ?_
    filter_upwards [h] with a ha
    change _ = Multiplicative.ofAdd (logNorm F a)
    rw [logNorm, ha, sub_zero]
  exact continuous_toAdd.comp hf

/- English proof (translation)
Establish `h : ∀ s : ℂ, Continuous fun a : Ideles F => Complex.exp (s * logNorm F a)` using `fun s => Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_logNorm F)))`. Use `Units.continuous_iff.2 ⟨h s, ?_⟩` and prove the remaining obligations. Use `(h (-s)).congr fun a => ?_` and prove the remaining obligations. Rewrite using `[Units.val_inv_eq_inv_val, absHom_val, ← Complex.exp_neg, neg_mul]`.
-/
theorem continuous_absHom (s : ℂ) : Continuous (absHom F s) := by
  have h : ∀ s : ℂ, Continuous fun a : Ideles F => Complex.exp (s * logNorm F a) := fun s =>
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_logNorm F)))
  refine Units.continuous_iff.2 ⟨h s, ?_⟩
  refine (h (-s)).congr fun a => ?_
  rw [Units.val_inv_eq_inv_val, absHom_val, ← Complex.exp_neg, neg_mul]

def absChar (s : ℂ) : HChar F :=
  ⟨absHom F s, continuous_absHom F s, fun k => Units.ext (by rw [absHom_val, logNorm_principal]; simp)⟩

variable {F}

/- English proof (translation)
Establish `hv : (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot`. Use `GlobalTheory.Idele.eq_of_count_eq (GlobalTheory.Idele.idealOf_ne_zero _) (zpow_ne_zero _ hv) fun w => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.Idele.count_idealOf, GlobalTheory.Idele.ord_vw]`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality.

Establish `: ((finPart F (localIdele F w x) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = x` using `Model.localIdele_snd_self F w x`. Rewrite using `[this, hx, FractionalIdeal.count_zpow_self]`. Simplify using the standard rewrite rules. Establish `: ((finPart F (localIdele F v x) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = 1` using `Model.localIdele_snd_ne F v w h x`. Rewrite using `[this, FractionalIdeal.count_zpow, FractionalIdeal.count_maximal_coprime F w (Ne.symm h)]`.

Simplify using the standard rewrite rules.
-/
theorem idealOf_local (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) (n : ℤ)
    (hx : Valued.v (x : v.adicCompletion F) = WithZero.exp (-n)) :
    GlobalTheory.Idele.idealOf (finPart F (localIdele F v x)) = (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ n := by
  have hv : (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot
  refine GlobalTheory.Idele.eq_of_count_eq (GlobalTheory.Idele.idealOf_ne_zero _) (zpow_ne_zero _ hv) fun w => ?_
  rw [GlobalTheory.Idele.count_idealOf, GlobalTheory.Idele.ord_vw]
  by_cases h : w = v
  · subst h
    have : ((finPart F (localIdele F w x) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = x :=
      Model.localIdele_snd_self F w x
    rw [this, hx, FractionalIdeal.count_zpow_self]; simp
  · have : ((finPart F (localIdele F v x) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = 1 :=
      Model.localIdele_snd_ne F v w h x
    rw [this, FractionalIdeal.count_zpow, FractionalIdeal.count_maximal_coprime F w (Ne.symm h)]; simp

/- English proof (translation)
Establish `h1 : infPart F (localIdele F v x) = 1` using `Units.ext rfl`. Rewrite using `[logNorm, h1, logInf_one, logFin, idealOf_local v x n hx, map_zpow₀, FractionalIdeal.coeIdeal_absNorm]`. Use `push_cast`. Rewrite using `[Real.log_zpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logNorm_local (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) (n : ℤ)
    (hx : Valued.v (x : v.adicCompletion F) = WithZero.exp (-n)) :
    logNorm F (localIdele F v x) = -(n * Real.log (Ideal.absNorm v.asIdeal : ℕ)) := by
  have h1 : infPart F (localIdele F v x) = 1 := Units.ext rfl
  rw [logNorm, h1, logInf_one, logFin, idealOf_local v x n hx, map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rw [Real.log_zpow]; ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply `Units.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Rewrite using `[infDiag, MonoidHom.finset_prod_apply, map_prod, Units.coe_prod]`. Establish `e : (∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)) w = ∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w` using `Finset.prod_apply _ _ _`.

Rewrite using `[e, Finset.prod_eq_single w]`. Conclude with `Model.infIdele_fst_self F w _`. Introduce `u _ hu`. Conclude with `Model.infIdele_fst_ne F u w (Ne.symm hu) _`. Simplify using the standard rewrite rules.

Rewrite using `[infDiag, MonoidHom.finset_prod_apply, map_prod]`. Conclude with `Finset.prod_eq_one fun u _ => Units.ext rfl`.
-/
theorem infDiag_parts (k : Fˣ) : infPart F (infDiag k) = infPart F (diagUnits F k) ∧ finPart F (infDiag k) = 1 := by
  classical
  constructor
  · apply Units.ext
    funext w
    rw [infDiag, MonoidHom.finset_prod_apply, map_prod, Units.coe_prod]
    have e : (∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) :
        InfiniteAdeleRing F)) w = ∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) :
          (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w := Finset.prod_apply _ _ _
    rw [e, Finset.prod_eq_single w]
    · exact Model.infIdele_fst_self F w _
    · intro u _ hu
      exact Model.infIdele_fst_ne F u w (Ne.symm hu) _
    · simp
  · rw [infDiag, MonoidHom.finset_prod_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => Units.ext rfl

/- English proof (translation)
Rewrite using `[logNorm, (infDiag_parts k).1, (infDiag_parts k).2, logFin_one, sub_zero, logInf_principal, ← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 k.ne_zero))]`. Use `congr 1`. Establish `h` using `congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ (k : F))`. Simplify using `only [norm_prod] at h`. Rewrite `h` using `[← Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => ‖φ (k : F)‖) (fun σ : F →ₐ[ℚ] ℂ => ‖σ (k : F)‖) (fun _ => rfl)]`.

Rewrite using `[← h]`. Simplify using the standard rewrite rules.
-/
theorem logNorm_infDiag (k : Fˣ) : logNorm F (infDiag k) = ∑ φ : F →+* ℂ, Real.log ‖φ (k : F)‖ := by
  rw [logNorm, (infDiag_parts k).1, (infDiag_parts k).2, logFin_one, sub_zero, logInf_principal,
    ← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 k.ne_zero))]
  congr 1
  have h := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ (k : F))
  simp only [norm_prod] at h
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => ‖φ (k : F)‖)
    (fun σ : F →ₐ[ℚ] ℂ => ‖σ (k : F)‖) (fun _ => rfl)] at h
  rw [← h]
  simp

/- English proof (translation)
Use `⟨fun v x hx => Units.ext ?_, fun v => ?_, fun k => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (s * logNorm F (localIdele F v x)) = 1`. Rewrite using `[logNorm_local v x 0 (by simpa [IsUnitAt] using hx)]; simp`. Express the relevant statement in the definitionally equal form `Complex.exp (s * logNorm F (localIdele F v (atFin v (unif v)))) = _`. Establish `h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0` using `by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot`.

Rewrite using `[logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0), ← Complex.natCast_log]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `Complex.exp (s * logNorm F (infDiag k)) = _`.

Rewrite using `[logNorm_infDiag, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]`. Use `Finset.prod_congr rfl fun φ _ => ?_` and prove the remaining obligations. Establish `h0 : 0 < ‖φ (k : F)‖` using `norm_pos_iff.2 ((map_ne_zero φ).2 k.ne_zero)`. Rewrite using `[Complex.cpow_def_of_ne_zero (by exact_mod_cast h0.ne'), ← Complex.ofReal_log h0.le, mul_comm]`.
-/
theorem absChar_isAbsPow (s : ℝ) : (absChar F s).IsAbsPow s := by
  refine ⟨fun v x hx => Units.ext ?_, fun v => ?_, fun k => ?_⟩
  · change Complex.exp (s * logNorm F (localIdele F v x)) = 1
    rw [logNorm_local v x 0 (by simpa [IsUnitAt] using hx)]; simp
  · change Complex.exp (s * logNorm F (localIdele F v (atFin v (unif v)))) = _
    have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
    rw [logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
      ← Complex.natCast_log]
    congr 1; push_cast; ring
  · change Complex.exp (s * logNorm F (infDiag k)) = _
    rw [logNorm_infDiag, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun φ _ => ?_
    have h0 : 0 < ‖φ (k : F)‖ := norm_pos_iff.2 ((map_ne_zero φ).2 k.ne_zero)
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast h0.ne'), ← Complex.ofReal_log h0.le, mul_comm]

/- English proof (translation)
Introduce `h`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Set `v : HeightOneSpectrum (𝓞 F)` to `⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩`. Establish `h1` using `h (localIdele F v (atFin v (unif v)))`. Express the relevant statement in the definitionally equal form `‖Complex.exp (1 * logNorm F _)‖ = 1 at h1`.

Rewrite `h1` using `[logNorm_local v _ 1 (unif_spec v), one_mul, Complex.norm_exp_ofReal, Real.exp_eq_one_iff]`. Establish `h2 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ)` using `by exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v`. Use `Real.log_pos h2` as an intermediate fact. Move the coercions through the operations in `at h1 this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem absChar_not_unitary : ¬ (absChar F 1).IsUnitary := by
  intro h
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  have h1 := h (localIdele F v (atFin v (unif v)))
  change ‖Complex.exp (1 * logNorm F _)‖ = 1 at h1
  rw [logNorm_local v _ 1 (unif_spec v), one_mul, Complex.norm_exp_ofReal, Real.exp_eq_one_iff] at h1
  have h2 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have := Real.log_pos h2
  push_cast at h1 this
  linarith

/- English proof (translation)
Introduce `x` and use `by change ‖Complex.exp (t * Complex.I * logNorm F x)‖ = 1 rw [Complex.norm_exp]; simp`.
-/
theorem absChar_unitary (t : ℝ) : (absChar F (t * Complex.I)).IsUnitary := fun x => by
  change ‖Complex.exp (t * Complex.I * logNorm F x)‖ = 1
  rw [Complex.norm_exp]; simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, _, absChar_isAbsPow s, rfl⟩`.
-/
theorem unitaryNorm {χ : HChar F} (h : χ.IsUnitary) (s : ℝ) : χ.IsUnitaryNormOf (χ * absChar F s) s :=
  ⟨h, _, absChar_isAbsPow s, rfl⟩

/- English proof (translation)
Use `⟨top_ne_bot, fun v n => ⟨fun _ hd => ?_, fun _ => (h v).levelLe n⟩⟩` and prove the remaining obligations. Rewrite `hd` using `[Ideal.dvd_iff_le, top_le_iff]`. Conclude with `v.isPrime.ne_top (top_le_iff.1 (hd ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))`.
-/
theorem isCond_top {χ : HChar F} (h : ∀ v, χ.UnrAt v) : χ.IsCond ⊤ := by
  refine ⟨top_ne_bot, fun v n => ⟨fun _ hd => ?_, fun _ => (h v).levelLe n⟩⟩
  rw [Ideal.dvd_iff_le, top_le_iff] at hd
  exact v.isPrime.ne_top (top_le_iff.1 (hd ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))

end Norm

section Product

variable {F : Type} [Field F] [NumberField F]

open Classical in

def cut (a : FiniteAdeleRing (𝓞 F) F) (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then a v else 1, by
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    apply hw
    have h' : w ∉ T := h
    simp only [h', if_false]
    exact one_mem _⟩

/- English proof (translation)
Set `S : Set (HeightOneSpectrum (𝓞 F))` to `{v | a v ∈ v.adicCompletionIntegers F}`. Establish `hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S`. Rewrite using `[Filter.le_principal_iff]`. Conclude with `a.2`. Set `P` to `RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)`.

Set `f : Finset (HeightOneSpectrum (𝓞 F)) → P` to `fun T => ⟨fun v => if v ∈ T then a v else 1, by`. Rewrite using `[Filter.eventually_principal]`. Introduce `w hw`. Distinguish the cases in `h : w ∈ T`. Simplify using `only [h, if_true]`.

Conclude with `hw`. Simplify using `only [h, if_false]`. Conclude with `one_mem _⟩`. Set `a' : P` to `⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩`. Establish `hf : Filter.Tendsto f Filter.atTop (nhds a')`.

Rewrite using `[RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]`. Introduce `v`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT`. Establish `: v ∈ T` using `hT (Finset.mem_singleton_self v)`.

Express the relevant statement in the definitionally equal form `a v = if v ∈ T then a v else 1`. Rewrite using `[if_pos this]`. Conclude with `((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf`.
-/
theorem tendsto_cut (a : FiniteAdeleRing (𝓞 F) F) : Filter.Tendsto (cut a) Filter.atTop (nhds a) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((infPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = _`. Establish `e : ∏ v ∈ T, infPart F (localIdele F v (atFin v k)) = 1` using `Finset.prod_eq_one (fun v _ => Units.ext rfl)`. Rewrite using `[map_mul, map_prod, (infDiag_parts k).1, e, mul_one]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `((finPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = _`. Rewrite using `[map_mul, (infDiag_parts k).2, one_mul]`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, map_one]; exact Subtype.ext (funext fun v => by simp [cut]; rfl)`. Consider the case `insert u T hu ih`.

Rewrite using `[Finset.prod_insert hu, map_mul, Units.val_mul, ih]`. Use `Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((localIdele F u (atFin u k) : Ideles F) : AdeleRing (𝓞 F) F).2 v * (if v ∈ T then _ else 1) = if v ∈ insert u T then _ else 1`. Distinguish the cases in `h : v = u`. Substitute `h` using the available equality.

Rewrite using `[Model.localIdele_snd_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one]`. Both sides reduce to the same expression. Rewrite using `[Model.localIdele_snd_ne F u v h, one_mul]`. Simplify using `[h]`.
-/
theorem prod_local (k : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F) =
      (((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).1, cut ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).2 T) := by
  classical
  refine Prod.ext ?_ ?_
  · change ((infPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = _
    have e : ∏ v ∈ T, infPart F (localIdele F v (atFin v k)) = 1 := Finset.prod_eq_one (fun v _ => Units.ext rfl)
    rw [map_mul, map_prod, (infDiag_parts k).1, e, mul_one]
    rfl
  · change ((finPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = _
    rw [map_mul, (infDiag_parts k).2, one_mul]
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one]; exact Subtype.ext (funext fun v => by simp [cut]; rfl)
    | insert u T hu ih =>
      rw [Finset.prod_insert hu, map_mul, Units.val_mul, ih]
      refine Subtype.ext (funext fun v => ?_)
      change ((localIdele F u (atFin u k) : Ideles F) : AdeleRing (𝓞 F) F).2 v * (if v ∈ T then _ else 1) =
        if v ∈ insert u T then _ else 1
      by_cases h : v = u
      · subst h
        rw [Model.localIdele_snd_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one]; rfl
      · rw [Model.localIdele_snd_ne F u v h, one_mul]; simp [h]

/- English proof (translation)
Establish `h : ∀ k : Fˣ, Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F)) Filter.atTop (nhds ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F))` using `fun k => by`. Simplify using `only [prod_local]`. Conclude with `tendsto_const_nhds.prodMk_nhds (tendsto_cut _)`. Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Use `(h k).prodMk_nhds ?_` and prove the remaining obligations.

Use `(MulOpposite.continuous_op.tendsto _).comp ?_` and prove the remaining obligations. Establish `h2` using `h k⁻¹`. Simplify using `only [map_inv, Finset.prod_inv_distrib, ← mul_inv] at h2`. Conclude with `h2`.
-/
theorem tendsto_prod_local (k : Fˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
      Filter.atTop (nhds (diagUnits F k)) := by
  have h : ∀ k : Fˣ, Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F))
      Filter.atTop (nhds ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F)) := fun k => by
    simp only [prod_local]
    exact tendsto_const_nhds.prodMk_nhds (tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h k).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h k⁻¹
  simp only [map_inv, Finset.prod_inv_distrib, ← mul_inv] at h2
  exact h2

/- English proof (translation)
Establish `hu : IsUnitAt v (atFin v (k * (unif v ^ ordF v k)⁻¹))`. Establish `h2` using `unif_spec v`. Establish `hk : Valued.v ((atFin v k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = v.valuation F (k : F)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)`. Establish `h0 : v.valuation F (k : F) ≠ 0` using `by simp`. Unfold `IsUnitAt IsUnifAt at *`.

Rewrite using `[map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, h2, hk, ← WithZero.exp_zsmul, ordF]`. Simplify using `only [smul_eq_mul, mul_neg, mul_one, neg_neg]`. Rewrite using `[WithZero.exp_log h0, mul_inv_cancel₀ h0]`. Establish `h3 : χ.locK v (k * (unif v ^ ordF v k)⁻¹) = 1` using `h _ hu`. Rewrite `h3` using `[map_mul, map_inv, map_zpow, mul_inv_eq_one]`.

Conclude with `h3`.
-/
theorem locK_unr (χ : HChar F) {v : HeightOneSpectrum (𝓞 F)} (h : χ.UnrAt v) (k : Fˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  have hu : IsUnitAt v (atFin v (k * (unif v ^ ordF v k)⁻¹)) := by
    have h2 := unif_spec v
    have hk : Valued.v ((atFin v k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = v.valuation F (k : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
    have h0 : v.valuation F (k : F) ≠ 0 := by simp
    unfold IsUnitAt IsUnifAt at *
    rw [map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, hk, ← WithZero.exp_zsmul, ordF]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 : χ.locK v (k * (unif v ^ ordF v k)⁻¹) = 1 := h _ hu
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

/- English proof (translation)
Establish `h` using `Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (FiniteAdeleRing.unitEmbedding (𝓞 F) F k))`. Use `h.subset fun v hv h0 => hv ?_` and prove the remaining obligations. Establish `hk : Valued.v (((FiniteAdeleRing.unitEmbedding (𝓞 F) F k : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = v.valuation F (k : F)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)`. Rewrite `h0` using `[GlobalTheory.Idele.ord_vw, hk]`. Conclude with `h0`.
-/
theorem finite_ordF (k : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordF v k ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (FiniteAdeleRing.unitEmbedding (𝓞 F) F k))
  refine h.subset fun v hv h0 => hv ?_
  have hk : Valued.v (((FiniteAdeleRing.unitEmbedding (𝓞 F) F k : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v) = v.valuation F (k : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
  rw [GlobalTheory.Idele.ord_vw, hk] at h0
  exact h0

/- English proof (translation)
Introduce `S hS k`. Establish `h1` using `(χ.2.1.tendsto _).comp (tendsto_prod_local k)`. Rewrite `h1` using `[χ.2.2 k]`. Use `tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h1` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop (S ∪ (finite_ordF k).toFinset)] with T hT`.

Establish `hST : S ⊆ T` using `Finset.subset_union_left.trans hT`. Express the relevant statement in the definitionally equal form `_ = χ.1 (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))`. Rewrite using `[map_mul, map_prod, mul_assoc, ← Finset.prod_sdiff hST, mul_comm (∏ v ∈ T \ S, _)]`. Use `congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl ?_)` and prove the remaining obligations. Rewrite using `[finprod_cond_eq_prod_of_cond_iff (fun v => χ.val v ^ ordF v k) (p := fun v => v ∉ S) (t := T \ S)]`.

Conclude with `Finset.prod_congr rfl fun v hv => (locK_unr χ (hS v (Finset.mem_sdiff.1 hv).2) k).symm`. Introduce `v hv`. Rewrite using `[Finset.mem_sdiff]`. Use `⟨fun h => ⟨hT (Finset.mem_union_right _ ?_), h⟩, fun h => h.2⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`.

Introduce `h0`. Conclude with `hv (by rw [h0, zpow_zero])`.
-/
theorem productRule (χ : HChar F) : χ.ProductRule := by
  classical
  intro S hS k
  have h1 := (χ.2.1.tendsto _).comp (tendsto_prod_local k)
  rw [χ.2.2 k] at h1
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h1
  filter_upwards [Filter.eventually_ge_atTop (S ∪ (finite_ordF k).toFinset)] with T hT
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  change _ = χ.1 (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
  rw [map_mul, map_prod, mul_assoc, ← Finset.prod_sdiff hST, mul_comm (∏ v ∈ T \ S, _)]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl ?_)
  rw [finprod_cond_eq_prod_of_cond_iff (fun v => χ.val v ^ ordF v k) (p := fun v => v ∉ S) (t := T \ S)]
  · exact Finset.prod_congr rfl fun v hv => (locK_unr χ (hS v (Finset.mem_sdiff.1 hv).2) k).symm
  · intro v hv
    rw [Finset.mem_sdiff]
    refine ⟨fun h => ⟨hT (Finset.mem_union_right _ ?_), h⟩, fun h => h.2⟩
    rw [Set.Finite.mem_toFinset]
    intro h0
    exact hv (by rw [h0, zpow_zero])

/- English proof (translation)
Use `productRule χ ∅ (fun v _ => h v) k` as an intermediate fact. Simplify using `only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at this`. Conclude with `(eq_inv_of_mul_eq_one_right this)`.
-/
theorem principal_unr (χ : HChar F) (h : ∀ v, χ.UnrAt v) (k : Fˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), χ.val v ^ ordF v k = (χ.inf k)⁻¹ := by
  have := productRule χ ∅ (fun v _ => h v) k
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at this
  exact (eq_inv_of_mul_eq_one_right this)

end Product

section HostData

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

/- English proof (translation)
Establish `hnu : ¬ IsUnit ((p : ℕ) : 𝓞 K)`. Introduce `hu`. Establish `h2` using `hu.map (Algebra.norm ℤ)`. Establish `e : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ)` using `by simp`. Rewrite `h2` using `[e, Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq]`.

Conclude with `hp.ne_one (by simpa using h2)`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 K)}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hle (Ideal.mem_span_singleton_self _)⟩`.
-/
theorem exists_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 K) := by
    intro hu
    have h2 := hu.map (Algebra.norm ℤ)
    have e : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq] at h2
    exact hp.ne_one (by simpa using h2)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 K)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩,
    hle (Ideal.mem_span_singleton_self _)⟩

/- English proof (translation)
Use `choose f hf using fun k : Fin 2 => exists_over H.K (H.g_prime k)`. Conclude with `⟨⟨f, hf⟩⟩`.
-/
theorem nonempty_piBar : Nonempty (PiBar H) := by
  choose f hf using fun k : Fin 2 => exists_over H.K (H.g_prime k)
  exact ⟨⟨f, hf⟩⟩

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hn : Nat.card (ZMod p)ˣ ≠ 0` using `Nat.card_pos.ne'`. Use `haveI : NeZero (Nat.card (ZMod p)ˣ) := ⟨hn⟩`. Establish `hc : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ)`. Rewrite using `[Complex.card_rootsOfUnity]`.

Conclude with `⟨(rootsOfUnity _ ℂ).subtype.comp (mulEquivOfCyclicCardEq hc).toMonoidHom, Subtype.val_injective.comp (mulEquivOfCyclicCardEq hc).injective⟩`.
-/
theorem exists_faithful {p : ℕ} (hp : p.Prime) : ∃ ω : (ZMod p)ˣ →* ℂˣ, Function.Injective ω := by
  haveI := Fact.mk hp
  have hn : Nat.card (ZMod p)ˣ ≠ 0 := Nat.card_pos.ne'
  haveI : NeZero (Nat.card (ZMod p)ˣ) := ⟨hn⟩
  have hc : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ) := by
    rw [Complex.card_rootsOfUnity]
  exact ⟨(rootsOfUnity _ ℂ).subtype.comp (mulEquivOfCyclicCardEq hc).toMonoidHom,
    Subtype.val_injective.comp (mulEquivOfCyclicCardEq hc).injective⟩

/- English proof (translation)
Use `choose f hf using fun k : Fin 2 => exists_faithful (H.g_prime k)`. Conclude with `⟨⟨f, hf⟩⟩`.
-/
theorem nonempty_omg : Nonempty (Omg H) := by
  choose f hf using fun k : Fin 2 => exists_faithful (H.g_prime k)
  exact ⟨⟨f, hf⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨χ, h, unitaryNorm h.unitary _⟩`.
-/
theorem isEtaAlg_of {χ : HChar H.E} (h : IsEtaT H χ) : IsEtaAlg H (χ * absChar H.E ((1 / 2 : ℝ) : ℂ)) :=
  ⟨χ, h, unitaryNorm h.unitary _⟩

/- English proof (translation)
Take `⟨η, hη, -, ν, hν, rfl⟩` from `h`. Rewrite using `[HChar.inf_mul, Units.val_mul, hη.inf k, hν.2.2 k, mul_right_comm, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun g _ => ?_` and prove the remaining obligations. Establish `h0 : ((‖embPsi H g (k : H.E)‖ : ℝ) : ℂ) ≠ 0`.

Conclude with `norm_ne_zero_iff.2 ((map_ne_zero _).2 k.ne_zero)` after adjusting the coercions. Rewrite using `[zpow_one, div_mul_cancel₀ _ h0]`.
-/
theorem isEtaAlg_inf {χ : HChar H.E} (h : IsEtaAlg H χ) (k : H.Eˣ) :
    ((χ.inf k : ℂˣ) : ℂ) * ∏ g : R.Psi, ((‖embPsi H g (k : H.E)‖ : ℝ) : ℂ) =
      (∏ g : R.Psi, embPsi H g (k : H.E)) * ∏ φ : H.E →+* ℂ, ((‖φ (k : H.E)‖ : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
  obtain ⟨η, hη, -, ν, hν, rfl⟩ := h
  rw [HChar.inf_mul, Units.val_mul, hη.inf k, hν.2.2 k, mul_right_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun g _ => ?_
  have h0 : ((‖embPsi H g (k : H.E)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.2 ((map_ne_zero _).2 k.ne_zero)
  rw [zpow_one, div_mul_cancel₀ _ h0]

/- English proof (translation)
Introduce `h`. Take `⟨v, hv⟩` from `exists_over H.E hp`. Use `(h.ine v hv 1).1 fun x _ => by simp` as an intermediate fact. Evaluate the numerical expressions using `at this`.
-/
theorem not_isDelta_one {p : ℕ} (hp : p.Prime) : ¬ IsDelta (H := H) p 1 := by
  intro h
  obtain ⟨v, hv⟩ := exists_over H.E hp
  have := (h.ine v hv 1).1 fun x _ => by simp
  norm_num at this

/- English proof (translation)
Introduce `h`. Take `⟨w⟩ : Nonempty (InfinitePlace H.F)` from `inferInstance`. Establish `h1` using `h.res.2 w (-1)`. Rewrite `h1` using `[isClsF_one.triv.2, etaInf, if_pos (by simp)]`. Establish `h2` using `congrArg (fun z : ℂˣ => (z : ℂ)) h1`.

Evaluate the numerical expressions using `at h2`.
-/
theorem not_isEtaT_one : ¬ IsEtaT H 1 := by
  intro h
  obtain ⟨w⟩ : Nonempty (InfinitePlace H.F) := inferInstance
  have h1 := h.res.2 w (-1)
  rw [isClsF_one.triv.2, etaInf, if_pos (by simp)] at h1
  have h2 := congrArg (fun z : ℂˣ => (z : ℂ)) h1
  norm_num at h2

end HostData

end GlobalTheory.Mem.Chr.CharModel

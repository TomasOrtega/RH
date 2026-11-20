import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.ModelChar

def argU : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem argU_val (z : ℂˣ) : ((argU z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

/- English proof (translation)
Rewrite using `[argU_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]`.
-/
theorem norm_argU (z : ℂˣ) : ‖((argU z : ℂˣ) : ℂ)‖ = 1 := by
  rw [argU_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

/- English proof (translation)
Rewrite using `[Units.isEmbedding_val₀.continuous_iff]`. Conclude with `Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm) fun z => by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero`.
-/
theorem continuous_argU : Continuous argU := by
  rw [Units.isEmbedding_val₀.continuous_iff]
  exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero

variable {L : Type} [Field L] [NumberField L]

def finEv (v : HeightOneSpectrum (𝓞 L)) : AdeleRing (𝓞 L) L →* v.adicCompletion L where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infEv (w : InfinitePlace L) : AdeleRing (𝓞 L) L →* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
The claim follows from `(RestrictedProduct.continuous_eval v).comp continuous_snd`.
-/
theorem continuous_finEv (v : HeightOneSpectrum (𝓞 L)) : Continuous (finEv v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

/- English proof (translation)
The claim follows from `(continuous_apply w).comp continuous_fst`.
-/
theorem continuous_infEv (w : InfinitePlace L) : Continuous (infEv w) :=
  (continuous_apply w).comp continuous_fst

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `Function.update_self v (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))`.
-/
theorem finEv_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    Units.map (finEv v) (localIdele L v x) = x := by
  classical
  apply Units.ext
  exact Function.update_self v (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `Function.update_of_ne h (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))`.
-/
theorem finEv_local_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    Units.map (finEv w) (localIdele L v x) = 1 := by
  classical
  apply Units.ext
  exact Function.update_of_ne h (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem infEv_local (w : InfinitePlace L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    Units.map (infEv w) (localIdele L v x) = 1 := Units.ext rfl

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem finEv_inf (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    Units.map (finEv v) (infIdele L w x) = 1 := Units.ext rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `Pi.mulSingle_eq_same (M := fun w : InfinitePlace L => w.Completion) w (x : w.Completion)`.
-/
theorem infEv_inf_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    Units.map (infEv w) (infIdele L w x) = x := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_same (M := fun w : InfinitePlace L => w.Completion) w (x : w.Completion)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace L => w.Completion) h (x : w.Completion)`.
-/
theorem infEv_inf_ne {w u : InfinitePlace L} (h : u ≠ w) (x : (w.Completion)ˣ) :
    Units.map (infEv u) (infIdele L w x) = 1 := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace L => w.Completion) h (x : w.Completion)

/- English proof (translation)
Unfold `infDiag`. Rewrite using `[MonoidHom.finsetProd_apply, map_prod, Finset.prod_eq_single w]`. Conclude with `infEv_inf_self w _`. Introduce `u _ hu`. Conclude with `infEv_inf_ne hu.symm _`.

Simplify using the standard rewrite rules.
-/
theorem infEv_infDiag (w : InfinitePlace L) (k : Lˣ) : Units.map (infEv w) (infDiag k) = atInf w k := by
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod, Finset.prod_eq_single w]
  · exact infEv_inf_self w _
  · intro u _ hu
    exact infEv_inf_ne hu.symm _
  · simp

/- English proof (translation)
Unfold `infDiag`. Rewrite using `[MonoidHom.finsetProd_apply, map_prod]`. Conclude with `Finset.prod_eq_one fun w _ => finEv_inf v w _`.
-/
theorem finEv_infDiag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : Units.map (finEv v) (infDiag k) = 1 := by
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => finEv_inf v w _

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem infEv_diag (w : InfinitePlace L) (k : Lˣ) : Units.map (infEv w) (diagUnits L k) = atInf w k := Units.ext rfl

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem finEv_diag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : Units.map (finEv v) (diagUnits L k) = atFin v k :=
  Units.ext rfl

/- English proof (translation)
Use `continuous_of_continuousAt_one θ ?_` and prove the remaining obligations. Establish `hc : Continuous fun x : (v.adicCompletion L)ˣ => (x : v.adicCompletion L) - 1` using `Units.continuous_val.sub continuous_const`. Establish `ho : IsOpen {y : v.adicCompletion L | Valued.v y < 1}`. Use `Valued.isOpen_ball (v.adicCompletion L) 1` as an intermediate fact. Simplify `this` using `only [Valuation.restrict_lt_one_iff]`.

Establish `hn : {x : (v.adicCompletion L)ˣ | Valued.v ((x : v.adicCompletion L) - 1) < 1} ∈ nhds (1 : (v.adicCompletion L)ˣ)` using `(ho.preimage hc).mem_nhds (by simp)`. Use `(continuousAt_const (y := (1 : ℂˣ))).congr ?_` and prove the remaining obligations. Use `filter_upwards [hn] with x hx`. Use `(h.2 x ?_ ?_).symm` and prove the remaining obligations. Use `Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hx` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Use `(WithZero.lt_mul_exp_iff_le (x := Valued.v ((x : v.adicCompletion L) - 1)) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero).1` as an intermediate fact. Apply `this` to reduce the goal to its premises. Rewrite using `[← WithZero.exp_add]`. Simplify using `using hx`.
-/
theorem continuous_of_tameLoc {v : HeightOneSpectrum (𝓞 L)} {θ : (v.adicCompletion L)ˣ →* ℂˣ} (h : TameLoc v θ) :
    Continuous θ := by
  refine continuous_of_continuousAt_one θ ?_
  have hc : Continuous fun x : (v.adicCompletion L)ˣ => (x : v.adicCompletion L) - 1 :=
    Units.continuous_val.sub continuous_const
  have ho : IsOpen {y : v.adicCompletion L | Valued.v y < 1} := by
    have := Valued.isOpen_ball (v.adicCompletion L) 1
    simpa only [Valuation.restrict_lt_one_iff] using this
  have hn : {x : (v.adicCompletion L)ˣ | Valued.v ((x : v.adicCompletion L) - 1) < 1} ∈ nhds (1 : (v.adicCompletion L)ˣ) :=
    (ho.preimage hc).mem_nhds (by simp)
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [hn] with x hx
  refine (h.2 x ?_ ?_).symm
  · have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hx
    rwa [add_sub_cancel] at this
  · have := (WithZero.lt_mul_exp_iff_le (x := Valued.v ((x : v.adicCompletion L) - 1)) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero).1
    apply this
    rw [← WithZero.exp_add]
    simpa using hx

open Classical in

/- English proof (translation)
Introduce `L _ _ I _ φ hφ n S θ hθ`. Use `choose e hec he using fun i => GlobalTheory.InfTypeLocal.exists_ext (φ i)`. Take `⟨ψ, hψ⟩ : ∃ ψ : Ideles L →* ℂˣ, ∀ a, ψ a = (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) * ∏ v ∈ S, θ v (Units.map (finEv v) a)` from `⟨{ toFun := fun a => (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) * ∏ v ∈ S, θ v (Units.map (finEv v) a) map_one' := by simp only [map_one, one_zpow, Finset.prod_const_one, mul_one] map_mul' := fun a b => by`. Simplify using `only [map_mul, mul_zpow, Finset.prod_mul_distrib]`. Rewrite using `[mul_mul_mul_comm] }, fun _ => rfl⟩`.

Use `⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show (ψ : Ideles L → ℂˣ) = _ from funext hψ]`. Use `Continuous.mul (continuous_finsetProd _ fun i _ => ?_) (continuous_finsetProd _ fun v hv => ?_)` and prove the remaining obligations. Conclude with `(continuous_argU.comp ((Continuous.units_map _ (hec i)).comp (Continuous.units_map _ (continuous_infEv _)))).zpow _`. Conclude with `(continuous_of_tameLoc (hθ v hv)).comp (Continuous.units_map _ (continuous_finEv v))`.

Introduce `x`. Rewrite using `[hψ, Units.val_mul, Units.coe_prod, Units.coe_prod, norm_mul, norm_prod, norm_prod, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]`. Conclude with `fun v hv => (hθ v hv).1 _`. Introduce `i _`. Rewrite using `[Units.val_zpow_eq_zpow_val, norm_zpow, norm_argU, one_zpow]`.

Introduce `i k`. Rewrite using `[hψ, Finset.prod_eq_one (s := S), mul_one, Finset.prod_eq_single i, infEv_inf_self, Units.val_zpow_eq_zpow_val, argU_val, ← he i k]`. Both sides reduce to the same expression. Introduce `j _ hj`. Rewrite using `[infEv_inf_ne (fun hh => hj (hφ.1 hh)), map_one, map_one, one_zpow]`.

Simplify using the standard rewrite rules. Introduce `v _`. Rewrite using `[finEv_inf, map_one]`. Introduce `v hv x`. Rewrite using `[hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_single_of_mem v hv, finEv_local_self]`.

Introduce `w _ hw`. Rewrite using `[finEv_local_ne hw, map_one]`. Introduce `i _`. Rewrite using `[infEv_local, map_one, map_one, one_zpow]`. Introduce `v hv x`.

Rewrite using `[hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_one]`. Introduce `w hw`. Establish `hne : w ≠ v` using `fun hh => hv (hh ▸ hw)`. Rewrite using `[finEv_local_ne hne, map_one]`. Introduce `i _`.

Rewrite using `[infEv_local, map_one, map_one, one_zpow]`. Introduce `k`. Rewrite using `[hψ, hψ]`. Simplify using `only [infEv_diag, finEv_diag, infEv_infDiag, finEv_infDiag, map_one, Finset.prod_const_one, mul_one]`.
-/
theorem exists_modelChar : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (n : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ →* ℂˣ), (∀ v ∈ S, TameLoc v (θ v)) → ∃ ψ : Ideles L →* ℂˣ, Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ i (k : Lˣ), ((ψ (infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ∧ (∀ v ∈ S, ∀ x, ψ (localIdele L v x) = θ v x) ∧ (∀ v ∉ S, ∀ x, ψ (localIdele L v x) = 1) ∧ ∀ k : Lˣ, ψ (diagUnits L k) = ψ (infDiag k) * ∏ v ∈ S, θ v (atFin v k) := by
  intro L _ _ I _ φ hφ n S θ hθ
  choose e hec he using fun i => GlobalTheory.InfTypeLocal.exists_ext (φ i)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Ideles L →* ℂˣ, ∀ a, ψ a =
      (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) *
        ∏ v ∈ S, θ v (Units.map (finEv v) a) :=
    ⟨{ toFun := fun a =>
        (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) *
          ∏ v ∈ S, θ v (Units.map (finEv v) a)
       map_one' := by simp only [map_one, one_zpow, Finset.prod_const_one, mul_one]
       map_mul' := fun a b => by
        simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]
        rw [mul_mul_mul_comm] }, fun _ => rfl⟩
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (ψ : Ideles L → ℂˣ) = _ from funext hψ]
    refine Continuous.mul (continuous_finsetProd _ fun i _ => ?_) (continuous_finsetProd _ fun v hv => ?_)
    · exact (continuous_argU.comp ((Continuous.units_map _ (hec i)).comp
        (Continuous.units_map _ (continuous_infEv _)))).zpow _
    · exact (continuous_of_tameLoc (hθ v hv)).comp (Continuous.units_map _ (continuous_finEv v))
  · intro x
    rw [hψ, Units.val_mul, Units.coe_prod, Units.coe_prod, norm_mul, norm_prod, norm_prod,
      Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
    · exact fun v hv => (hθ v hv).1 _
    · intro i _
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, norm_argU, one_zpow]
  · intro i k
    rw [hψ, Finset.prod_eq_one (s := S), mul_one, Finset.prod_eq_single i, infEv_inf_self,
      Units.val_zpow_eq_zpow_val, argU_val, ← he i k]
    · rfl
    · intro j _ hj
      rw [infEv_inf_ne (fun hh => hj (hφ.1 hh)), map_one, map_one, one_zpow]
    · simp
    · intro v _
      rw [finEv_inf, map_one]
  · intro v hv x
    rw [hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_single_of_mem v hv, finEv_local_self]
    · intro w _ hw
      rw [finEv_local_ne hw, map_one]
    · intro i _
      rw [infEv_local, map_one, map_one, one_zpow]
  · intro v hv x
    rw [hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_one]
    · intro w hw
      have hne : w ≠ v := fun hh => hv (hh ▸ hw)
      rw [finEv_local_ne hne, map_one]
    · intro i _
      rw [infEv_local, map_one, map_one, one_zpow]
  · intro k
    rw [hψ, hψ]
    simp only [infEv_diag, finEv_diag, infEv_infDiag, finEv_infDiag, map_one, Finset.prod_const_one, mul_one]

end GlobalTheory.ModelChar

import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.ReductionMahler
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction Formalism.L2.Host

section SlopeTestRemainingChoices

open Filter Topology

variable {K : Type} [Field K] [NumberField K]

private noncomputable def zf (y : FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K :=
  ((0, y) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

private noncomputable def zi (y : InfiniteAdeleRing K) : AdeleRing (𝓞 K) K :=
  ((y, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

/- English proof (translation)
The claim follows from `(continuous_const.prodMk continuous_id : Continuous fun y : FiniteAdeleRing (𝓞 K) K => ((0, y) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))`.
-/
private theorem continuous_zf : Continuous (zf (K := K)) :=
  (continuous_const.prodMk continuous_id :
    Continuous fun y : FiniteAdeleRing (𝓞 K) K => ((0, y) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

/- English proof (translation)
The claim follows from `(continuous_id.prodMk continuous_const : Continuous fun y : InfiniteAdeleRing K => ((y, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))`.
-/
private theorem continuous_zi : Continuous (zi (K := K)) :=
  (continuous_id.prodMk continuous_const :
    Continuous fun y : InfiniteAdeleRing K => ((y, 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

omit [NumberField K] in
/- English proof (translation)
Rewrite using `[← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_natCast, Complex.norm_natCast]`.
-/
private theorem norm_nat (w : InfinitePlace K) (n : ℕ) : ‖(n : w.Completion)‖ = n := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_natCast,
    Complex.norm_natCast]

/- English proof (translation)
Take `⟨C, hC⟩` from `((GroundTheory.Global.isCompact_integralFiniteAdeles K).image (hf.comp continuous_zf)).isBounded.exists_norm_le`. Assume the negation of the conclusion as `h0`. Establish `hp : 0 < ‖f (zf 1)‖` using `norm_pos_iff.2 h0`. Take `⟨n, hn⟩` from `exists_nat_gt (C / ‖f (zf 1)‖)`. Establish `h2` using `hC _ ⟨(n : FiniteAdeleRing (𝓞 K) K), natCast_mem _ n, rfl⟩`.

Establish `e : zf (n : FiniteAdeleRing (𝓞 K) K) = (n : AdeleRing (𝓞 K) K) * zf 1` using `Prod.ext (mul_zero _).symm (mul_one _).symm`. Rewrite `h2` using `[Function.comp_apply, e, map_mul, map_natCast, norm_mul, norm_nat]`. Rewrite `hn` using `[div_lt_iff₀ hp]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem inf_kill (w : InfinitePlace K) (f : AdeleRing (𝓞 K) K →+* w.Completion) (hf : Continuous f) :
    f (zf 1) = 0 := by
  obtain ⟨C, hC⟩ :=
    ((GroundTheory.Global.isCompact_integralFiniteAdeles K).image (hf.comp continuous_zf)).isBounded.exists_norm_le
  by_contra h0
  have hp : 0 < ‖f (zf 1)‖ := norm_pos_iff.2 h0
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖f (zf 1)‖)
  have h2 := hC _ ⟨(n : FiniteAdeleRing (𝓞 K) K), natCast_mem _ n, rfl⟩
  have e : zf (n : FiniteAdeleRing (𝓞 K) K) = (n : AdeleRing (𝓞 K) K) * zf 1 :=
    Prod.ext (mul_zero _).symm (mul_one _).symm
  rw [Function.comp_apply, e, map_mul, map_natCast, norm_mul, norm_nat] at h2
  rw [div_lt_iff₀ hp] at hn
  linarith

/- English proof (translation)
Set `a : ℕ → InfiniteAdeleRing K` to `fun n w => ((n + 1 : ℕ) : w.Completion)⁻¹`. Establish `ha : Tendsto a atTop (𝓝 0)`. Use `tendsto_pi_nhds.2 fun w => ?_` and prove the remaining obligations. Use `tendsto_zero_iff_norm_tendsto_zero.2 ?_` and prove the remaining obligations. Simplify using `only [a, norm_inv, norm_nat]`.

Conclude with `(tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)`. Establish `h1 : Tendsto (fun n => ‖f (zi (a n))‖) atTop (𝓝 0)`. Use `((hf.comp continuous_zi).tendsto 0).comp ha` as an intermediate fact. Establish `e : (f ∘ zi) 0 = 0` using `map_zero f`. Rewrite `this` using `[e]`.

Conclude with `tendsto_zero_iff_norm_tendsto_zero.1 this`. Establish `h2 : ∀ n, ‖f (zi 1)‖ ≤ ‖f (zi (a n))‖` using `fun n => by`. Establish `e : zi (1 : InfiniteAdeleRing K) = ((n + 1 : ℕ) : AdeleRing (𝓞 K) K) * zi (a n)`. Use `Prod.ext (funext fun w => ?_) (mul_zero _).symm` and prove the remaining obligations. Establish `h0 : ((n + 1 : ℕ) : w.Completion) ≠ 0`.

Rewrite using `[← norm_ne_zero_iff, norm_nat]`. Check the signs of the components of the expression. Conclude with `(mul_inv_cancel₀ h0).symm`. Establish `hn : ‖((n + 1 : ℕ) : v.adicCompletion K)‖ ≤ 1` using `Valued.toNormedField.norm_le_one_iff.2 (natCast_mem (v.adicCompletionIntegers K) (n + 1))`. Rewrite using `[e, map_mul, map_natCast, norm_mul]`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) hn`. Conclude with `norm_le_zero_iff.1 (ge_of_tendsto' h1 h2)`.
-/
private theorem fin_kill (v : HeightOneSpectrum (𝓞 K)) (f : AdeleRing (𝓞 K) K →+* v.adicCompletion K)
    (hf : Continuous f) : f (zi 1) = 0 := by
  let a : ℕ → InfiniteAdeleRing K := fun n w => ((n + 1 : ℕ) : w.Completion)⁻¹
  have ha : Tendsto a atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun w => ?_
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    simp only [a, norm_inv, norm_nat]
    exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have h1 : Tendsto (fun n => ‖f (zi (a n))‖) atTop (𝓝 0) := by
    have := ((hf.comp continuous_zi).tendsto 0).comp ha
    have e : (f ∘ zi) 0 = 0 := map_zero f
    rw [e] at this
    exact tendsto_zero_iff_norm_tendsto_zero.1 this
  have h2 : ∀ n, ‖f (zi 1)‖ ≤ ‖f (zi (a n))‖ := fun n => by
    have e : zi (1 : InfiniteAdeleRing K) = ((n + 1 : ℕ) : AdeleRing (𝓞 K) K) * zi (a n) := by
      refine Prod.ext (funext fun w => ?_) (mul_zero _).symm
      have h0 : ((n + 1 : ℕ) : w.Completion) ≠ 0 := by
        rw [← norm_ne_zero_iff, norm_nat]
        positivity
      exact (mul_inv_cancel₀ h0).symm
    have hn : ‖((n + 1 : ℕ) : v.adicCompletion K)‖ ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.2 (natCast_mem (v.adicCompletionIntegers K) (n + 1))
    rw [e, map_mul, map_natCast, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hn
  exact norm_le_zero_iff.1 (ge_of_tendsto' h1 h2)

/- English proof (translation)
Establish `h1 : (s (zi 1)).2 = 0` using `FiniteAdeleRing.ext _ fun v => fin_kill v (((RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)).comp s) (((RestrictedProduct.continuous_eval v).comp continuous_snd).comp hs)`. Establish `h2 : (s (zf 1)).1 = 0` using `funext fun w => inf_kill w (((Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).comp (RingHom.fst _ _)).comp s) (((continuous_apply w).comp continuous_fst).comp hs)`. Establish `e : zi 1 + zf 1 = (1 : AdeleRing (𝓞 K) K)` using `Prod.ext (add_zero _) (zero_add _)`. Establish `h3 : s (zi 1) + s (zf 1) = 1` using `by rw [← map_add, e, map_one]`. Establish `h4 : (s (zi 1)).1 + (s (zf 1)).1 = 1` using `congrArg Prod.fst h3`.

Establish `h5 : (s (zi 1)).2 + (s (zf 1)).2 = 1` using `congrArg Prod.snd h3`. Rewrite `h4` using `[h2, add_zero]`. Rewrite `h5` using `[h1, zero_add]`. Conclude with `⟨Prod.ext h4 h1, Prod.ext h2 h5⟩`.
-/
private theorem map_idem (s : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 K) K) (hs : Continuous s) :
    s (zi 1) = zi 1 ∧ s (zf 1) = zf 1 := by
  have h1 : (s (zi 1)).2 = 0 := FiniteAdeleRing.ext _ fun v =>
    fin_kill v (((RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)).comp s)
      (((RestrictedProduct.continuous_eval v).comp continuous_snd).comp hs)
  have h2 : (s (zf 1)).1 = 0 := funext fun w =>
    inf_kill w (((Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).comp (RingHom.fst _ _)).comp s)
      (((continuous_apply w).comp continuous_fst).comp hs)
  have e : zi 1 + zf 1 = (1 : AdeleRing (𝓞 K) K) := Prod.ext (add_zero _) (zero_add _)
  have h3 : s (zi 1) + s (zf 1) = 1 := by rw [← map_add, e, map_one]
  have h4 : (s (zi 1)).1 + (s (zf 1)).1 = 1 := congrArg Prod.fst h3
  have h5 : (s (zi 1)).2 + (s (zf 1)).2 = 1 := congrArg Prod.snd h3
  rw [h2, add_zero] at h4
  rw [h1, zero_add] at h5
  exact ⟨Prod.ext h4 h1, Prod.ext h2 h5⟩

/- English proof (translation)
Establish `: T2Space (InfiniteAdeleRing K)` using `inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))`. Establish `: T2Space (FiniteAdeleRing (𝓞 K) K)` using `inferInstance`. Establish `: T2Space (AdeleRing (𝓞 K) K)` using `inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))`. Establish `hi : s ∘ zi = t ∘ zi` using `(InfiniteAdeleRing.denseRange_algebraMap K).equalizer (hs.comp continuous_zi) (ht.comp continuous_zi) (funext fun k => by`. Establish `e : zi (algebraMap K (InfiniteAdeleRing K) k) = algebraMap K (AdeleRing (𝓞 K) K) k * zi 1` using `Prod.ext (mul_one _).symm (mul_zero _).symm`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[e, map_mul, map_mul, h, (map_idem s hs).1, (map_idem t ht).1])`. Establish `hf : s ∘ zf = t ∘ zf` using `(GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing K).equalizer (hs.comp continuous_zf) (ht.comp continuous_zf) (funext fun k => by`. Establish `e : zf (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) = algebraMap K (AdeleRing (𝓞 K) K) k * zf 1` using `Prod.ext (mul_zero _).symm (mul_one _).symm`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[e, map_mul, map_mul, h, (map_idem s hs).2, (map_idem t ht).2])`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Establish `e : x = zi x.1 + zf x.2` using `Prod.ext (add_zero _).symm (zero_add _).symm`. Rewrite using `[e, map_add, map_add]`. Conclude with `congrArg₂ (· + ·) (congrFun hi x.1) (congrFun hf x.2)`.
-/
private theorem ext_of_field (s t : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 K) K) (hs : Continuous s)
    (ht : Continuous t) (h : ∀ x : K, s (algebraMap K _ x) = t (algebraMap K _ x)) : s = t := by
  have : T2Space (InfiniteAdeleRing K) := inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))
  have : T2Space (FiniteAdeleRing (𝓞 K) K) := inferInstance
  have : T2Space (AdeleRing (𝓞 K) K) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
  have hi : s ∘ zi = t ∘ zi := (InfiniteAdeleRing.denseRange_algebraMap K).equalizer
    (hs.comp continuous_zi) (ht.comp continuous_zi) (funext fun k => by
      have e : zi (algebraMap K (InfiniteAdeleRing K) k) = algebraMap K (AdeleRing (𝓞 K) K) k * zi 1 :=
        Prod.ext (mul_one _).symm (mul_zero _).symm
      simp only [Function.comp_apply]
      rw [e, map_mul, map_mul, h, (map_idem s hs).1, (map_idem t ht).1])
  have hf : s ∘ zf = t ∘ zf := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing K).equalizer
    (hs.comp continuous_zf) (ht.comp continuous_zf) (funext fun k => by
      have e : zf (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) = algebraMap K (AdeleRing (𝓞 K) K) k * zf 1 :=
        Prod.ext (mul_zero _).symm (mul_one _).symm
      simp only [Function.comp_apply]
      rw [e, map_mul, map_mul, h, (map_idem s hs).2, (map_idem t ht).2])
  refine RingHom.ext fun x => ?_
  have e : x = zi x.1 + zf x.2 := Prod.ext (add_zero _).symm (zero_add _).symm
  rw [e, map_add, map_add]
  exact congrArg₂ (· + ·) (congrFun hi x.1) (congrFun hf x.2)

/- English proof (translation)
Apply `Prod.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `u`. Conclude with `CT.infEquiv_algebraMap σ u x`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `v`.

Use `show (CT.compEquiv σ.symm v).symm (algebraMap K ((CT.plMap σ.symm v).adicCompletion K) x) = _`. Establish `h` using `CT.compEquiv_symm_algebraMap σ.symm v (σ x)`. Rewrite `h` using `[RingEquiv.symm_apply_apply]`. Conclude with `h`.
-/
private theorem adMap_algebraMap (σ : K ≃+* K) (x : K) :
    CT.adMap σ (algebraMap K _ x) = algebraMap K _ (σ x) := by
  apply Prod.ext
  · funext u
    exact CT.infEquiv_algebraMap σ u x
  · apply RestrictedProduct.ext
    intro v
    show (CT.compEquiv σ.symm v).symm (algebraMap K ((CT.plMap σ.symm v).adicCompletion K) x) = _
    have h := CT.compEquiv_symm_algebraMap σ.symm v (σ x)
    rw [RingEquiv.symm_apply_apply] at h
    exact h

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `K _ _ σ s hs h`. Conclude with `ext_of_field s _ hs (CT.continuous_adMap σ) fun x => (h x).trans (adMap_algebraMap σ x).symm`.
-/
theorem UpperTheory.ConvolutionTheory.K.adUnique :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K ≃+* K) (s : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 K) K), Continuous s →
      (∀ x : K, s (algebraMap K _ x) = algebraMap K _ (σ x)) → s = CT.adMap σ := by
  intro K _ _ σ s hs h
  exact ext_of_field s _ hs (CT.continuous_adMap σ) fun x => (h x).trans (adMap_algebraMap σ x).symm

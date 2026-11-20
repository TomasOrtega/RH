import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf

noncomputable section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
open Filter Topology

namespace GlobalTheory.HeckeSplit

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `h : ∀ v : HeightOneSpectrum (𝓞 L), ∃ x : (v.adicCompletion L)ˣ, Valued.v (x : v.adicCompletion L) = 1 ∧ (‖((χ (localIdele L v x) : ℂˣ) : ℂ) - 1‖ < 1 / 2 → UnrAt χ v)` using `fun v => by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `(hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]`.

Use `(hc _ ?_).1` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, hx, one_pow]`. Use `choose x hx hx' using h`. Establish `hc : Continuous fun a : Ideles L => ‖((χ a : ℂˣ) : ℂ) - 1‖` using `((Units.continuous_val.comp hχ).sub continuous_const).norm`. Establish `h0 : Tendsto (fun v => localIdele L v (x v)) cofinite (𝓝 1)` using `GlobalTheory.Mem.UnrAe.tendsto_localIdele x hx`.

Establish `h1` using `(hc.tendsto 1).comp h0`. Establish `h2` using `h1.eventually_lt_const (u := 1 / 2) (by simp)`. Conclude with `h2.mono fun v hv => hx' v hv`.
-/
theorem eventually_unrAt (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) :
    ∀ᶠ v in Filter.cofinite, UnrAt χ v := by
  have h : ∀ v : HeightOneSpectrum (𝓞 L), ∃ x : (v.adicCompletion L)ˣ,
      Valued.v (x : v.adicCompletion L) = 1 ∧
      (‖((χ (localIdele L v x) : ℂˣ) : ℂ) - 1‖ < 1 / 2 → UnrAt χ v) := fun v => by
    by_contra hc
    push Not at hc
    refine (hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
    refine (hc _ ?_).1
    rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  choose x hx hx' using h
  have hc : Continuous fun a : Ideles L => ‖((χ a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp hχ).sub continuous_const).norm
  have h0 : Tendsto (fun v => localIdele L v (x v)) cofinite (𝓝 1) :=
    GlobalTheory.Mem.UnrAe.tendsto_localIdele x hx
  have h1 := (hc.tendsto 1).comp h0
  have h2 := h1.eventually_lt_const (u := 1 / 2) (by simp)
  exact h2.mono fun v hv => hx' v hv

/- English proof (translation)
Establish `hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖` using `((Units.continuous_val.comp (hχ.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele v))).sub continuous_const).norm`. Establish `h0 : {a : (v.adicCompletion L)ˣ | ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1` using `(isOpen_lt hc continuous_const).mem_nhds (by simp)`. Rewrite `h0` using `[Units.isEmbedding_val₀.nhds_eq_comap, mem_comap]`. Take `⟨t, ht, hsub⟩` from `h0`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds.mp ht`.

Establish `hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0` using `by simp`. Use `⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat + 1, fun x hx1 => ?_⟩` and prove the remaining obligations. Establish `hlt : Valued.v ((x : v.adicCompletion L) - 1) < 1`. Use `hx1.trans_lt ?_` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero]`.

Conclude with `WithZero.exp_lt_exp.mpr (by omega)`. Establish `hx' : Valued.v (x : v.adicCompletion L) = 1`. Use `Valuation.map_one_add_of_lt _ hlt` as an intermediate fact. Simplify using `using this`. Use `Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)` and prove the remaining obligations.

Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]`. Apply `hsub` to reduce the goal to its premises. Apply `hγ` to reduce the goal to its premises. Simplify using `only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]`. Establish `h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1)`.

Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1)` using `by ring`. Rewrite using `[e]`.

Use `Valuation.map_add_le _ ?_ ih` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hx', one_pow, one_mul]`. Use `(h1.trans hx1).trans_lt ?_` and prove the remaining obligations. Use `conv_rhs => rw [← WithZero.exp_log hγ0]`. Conclude with `WithZero.exp_lt_exp.mpr (by omega)`.
-/
theorem exists_level (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 L)) :
    ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ,
      Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1 := by
  have hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp (hχ.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele v))).sub
      continuous_const).norm
  have h0 : {a : (v.adicCompletion L)ˣ | ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat + 1, fun x hx1 => ?_⟩
  have hlt : Valued.v ((x : v.adicCompletion L) - 1) < 1 := by
    refine hx1.trans_lt ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := by
    have := Valuation.map_one_add_of_lt _ hlt
    simpa using this
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1) := by ring
      rw [e]
      refine Valuation.map_add_le _ ?_ ih
      rw [map_mul, map_pow, hx', one_pow, one_mul]
  refine (h1.trans hx1).trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)

def truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) : Ideles L :=
  infIdele L (infPart L x) * ∏ v ∈ T, localIdele L v (finPart L v x)

/- English proof (translation)
Simplify using `only [truncIdele, map_inv, Finset.prod_inv_distrib, ← mul_inv]`.
-/
theorem truncIdele_inv (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    truncIdele x⁻¹ T = (truncIdele x T)⁻¹ := by
  simp only [truncIdele, map_inv, Finset.prod_inv_distrib, ← mul_inv]

open Classical in
/- English proof (translation)
Rewrite using `[truncIdele, map_mul, finPart_infIdele, one_mul, map_prod]`. Use `split_ifs with h`. Rewrite using `[Finset.prod_eq_single_of_mem v h fun w _ hw => finPart_localIdele_ne L hw.symm _, finPart_localIdele]`. Conclude with `Finset.prod_eq_one fun w hw => finPart_localIdele_ne L (v := w) (w := v) (fun e => h (by rw [e]; exact hw)) _`.
-/
theorem finPart_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (v : HeightOneSpectrum (𝓞 L)) :
    finPart L v (truncIdele x T) = if v ∈ T then finPart L v x else 1 := by
  rw [truncIdele, map_mul, finPart_infIdele, one_mul, map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem v h fun w _ hw => finPart_localIdele_ne L hw.symm _,
      finPart_localIdele]
  · exact Finset.prod_eq_one fun w hw => finPart_localIdele_ne L (v := w) (w := v) (fun e => h (by rw [e]; exact hw)) _

/- English proof (translation)
Rewrite using `[truncIdele, map_mul, infPart_infIdele, map_prod, Finset.prod_eq_one fun v _ => infPart_localIdele L v _, mul_one]`.
-/
theorem infPart_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    infPart L (truncIdele x T) = infPart L x := by
  rw [truncIdele, map_mul, infPart_infIdele, map_prod,
    Finset.prod_eq_one fun v _ => infPart_localIdele L v _, mul_one]

/- English proof (translation)
Use `Prod.ext ?_ (Subtype.ext (funext fun v => ?_))` and prove the remaining obligations. Conclude with `congrArg (fun u : (InfiniteAdeleRing L)ˣ => (u : InfiniteAdeleRing L)) (infPart_truncIdele x T)`. Establish `h` using `congrArg (fun u : (v.adicCompletion L)ˣ => (u : v.adicCompletion L)) (finPart_truncIdele x T v)`. Use `h.trans ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ T`.

Simplify using `only [hv, if_true]`. Conclude with `(if_pos hv).symm`. Simplify using `only [hv, if_false]`. Conclude with `(if_neg hv).symm`.
-/
theorem coe_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L) =
      ((x : AdeleRing (𝓞 L) L).1, GlobalTheory.HeckeProduct.cut (x : AdeleRing (𝓞 L) L).2 T) := by
  classical
  refine Prod.ext ?_ (Subtype.ext (funext fun v => ?_))
  · exact congrArg (fun u : (InfiniteAdeleRing L)ˣ => (u : InfiniteAdeleRing L)) (infPart_truncIdele x T)
  · have h := congrArg (fun u : (v.adicCompletion L)ˣ => (u : v.adicCompletion L))
      (finPart_truncIdele x T v)
    refine h.trans ?_
    by_cases hv : v ∈ T
    · simp only [hv, if_true]; exact (if_pos hv).symm
    · simp only [hv, if_false]; exact (if_neg hv).symm

/- English proof (translation)
Establish `h : ∀ x : Ideles L, Tendsto (fun T => ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L)) atTop (𝓝 (x : AdeleRing (𝓞 L) L))` using `fun x => by`. Simplify using `only [coe_truncIdele]`. Conclude with `tendsto_const_nhds.prodMk_nhds (GlobalTheory.HeckeProduct.tendsto_cut _)`. Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Use `(h x).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)` and prove the remaining obligations.

Establish `h2` using `h x⁻¹`. Simplify using `only [truncIdele_inv] at h2`. Conclude with `h2`.
-/
theorem tendsto_truncIdele (x : Ideles L) :
    Tendsto (truncIdele x) atTop (𝓝 x) := by
  have h : ∀ x : Ideles L, Tendsto (fun T => ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L))
      atTop (𝓝 (x : AdeleRing (𝓞 L) L)) := fun x => by
    simp only [coe_truncIdele]
    exact tendsto_const_nhds.prodMk_nhds (GlobalTheory.HeckeProduct.tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h x).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
  have h2 := h x⁻¹
  simp only [truncIdele_inv] at h2
  exact h2

/- English proof (translation)
Establish `h1` using `(hχ.tendsto x).comp (tendsto_truncIdele x)`. Use `tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop S] with T hT`. Express the relevant statement in the definitionally equal form `_ = χ (truncIdele x T)`. Rewrite using `[truncIdele, map_mul, map_prod]`.

Use `congr 1`. Conclude with `Finset.prod_subset hT fun v _ hv => hS v hv`.
-/
theorem char_eq_prod_local (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) (x : Ideles L)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) :
    χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) := by
  classical
  have h1 := (hχ.tendsto x).comp (tendsto_truncIdele x)
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop S] with T hT
  change _ = χ (truncIdele x T)
  rw [truncIdele, map_mul, map_prod]
  congr 1
  exact Finset.prod_subset hT fun v _ hv => hS v hv

/- English proof (translation)
Introduce `_ _ _ χ hχ` and use `⟨eventually_unrAt χ hχ, exists_level χ hχ, fun x S hS => char_eq_prod_local χ hχ x S hS⟩`.
-/
theorem continuous_char_factor : ∀ (L : Type) [Field L] [NumberField L] (χ : Ideles L →* ℂˣ), Continuous χ → (∀ᶠ v in Filter.cofinite, UnrAt χ v) ∧ (∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ, Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1) ∧ ∀ (x : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) → χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) :=
  fun _ _ _ χ hχ => ⟨eventually_unrAt χ hχ, exists_level χ hχ, fun x S hS => char_eq_prod_local χ hχ x S hS⟩

end GlobalTheory.HeckeSplit

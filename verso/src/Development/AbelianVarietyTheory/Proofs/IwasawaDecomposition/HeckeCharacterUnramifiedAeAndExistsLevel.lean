import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Filter Topology

namespace GlobalTheory.Mem.UnrAe

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _)`. Rewrite using `[Filter.le_principal_iff]`. Conclude with `(Set.finite_singleton v).compl_mem_cofinite`. Set `f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _))` to `fun x => ⟨Function.update (fun _ => 1) v x, by`. Rewrite using `[Filter.eventually_principal]`.

Introduce `w hw`. Establish `h' : w ≠ v` using `hw`. Rewrite using `[Function.update_of_ne h']`. Conclude with `one_mem _⟩`. Establish `hf : Continuous f`.

Rewrite using `[RestrictedProduct.continuous_rng_of_principal]`. Conclude with `continuous_const.update v continuous_id`. Use `(RestrictedProduct.continuous_inclusion hle).comp hf` as an intermediate fact. Conclude with `this`.
-/
theorem continuous_finSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (Neutral.B1.finiteSingle L v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Function.update (fun _ => 1) v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Function.update_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_const.update v continuous_id
  have := (RestrictedProduct.continuous_inclusion hle).comp hf
  exact this

/- English proof (translation)
Apply `Continuous.units_map` to reduce the goal to its premises. Conclude with `Continuous.prodMk continuous_const (continuous_finSingle v)`.
-/
theorem continuous_localIdele (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finSingle v)

/- English proof (translation)
Set `A : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L)` to `fun w => w.adicCompletionIntegers L`. Set `o : ∀ w, A w` to `fun w => ⟨1, one_mem (w.adicCompletionIntegers L)⟩`. Set `g : HeightOneSpectrum (𝓞 L) → ∀ w, A w` to `fun v => Function.update o v ⟨y v, hy v⟩`. Establish `hg : Tendsto g cofinite (𝓝 o)`. Rewrite using `[tendsto_pi_nhds]`.

Introduce `w`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with v hv`. Establish `h' : w ≠ v` using `fun h => hv h.symm`. Conclude with `(Function.update_of_ne h' _ _).symm`.

Establish `h2` using `((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg`. Use `Tendsto.congr (fun v => ?_) h2` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Use `show (g v w : w.adicCompletion L) = Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) v (y v) w`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using `[g]`. Simplify using `[g, o, Function.update_of_ne hw]`.
-/
theorem tendsto_finSingle (y : ∀ v : HeightOneSpectrum (𝓞 L), v.adicCompletion L) (hy : ∀ v, Valued.v (y v) ≤ 1) :
    Tendsto (fun v => Neutral.B1.finiteSingle L v (y v)) cofinite (𝓝 1) := by
  classical
  let A : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w => w.adicCompletionIntegers L
  let o : ∀ w, A w := fun w => ⟨1, one_mem (w.adicCompletionIntegers L)⟩
  let g : HeightOneSpectrum (𝓞 L) → ∀ w, A w := fun v => Function.update o v ⟨y v, hy v⟩
  have hg : Tendsto g cofinite (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with v hv
    have h' : w ≠ v := fun h => hv h.symm
    exact (Function.update_of_ne h' _ _).symm
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  refine Tendsto.congr (fun v => ?_) h2
  apply Subtype.ext
  funext w
  show (g v w : w.adicCompletion L) = Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) v (y v) w
  by_cases hw : w = v
  · subst hw; simp [g]
  · simp [g, o, Function.update_of_ne hw]

/- English proof (translation)
Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Establish `h1` using `tendsto_finSingle (fun v => (x v : v.adicCompletion L)) fun v => (hx v).le`. Establish `h2` using `tendsto_finSingle (fun v => (((x v)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L)) fun v => by`. Establish `h : Valued.v (x v : v.adicCompletion L) = 1` using `hx v`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]`.

Establish `h3 : Tendsto (fun v => ((localIdele L v (x v) : Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1)` using `(tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h1`. Establish `h4 : Tendsto (fun v => (((localIdele L v (x v))⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1)` using `(tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h2`. Conclude with `h3.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h4)`.
-/
theorem tendsto_localIdele (x : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ) (hx : ∀ v, IsUnitAt v (x v)) :
    Tendsto (fun v => localIdele L v (x v)) cofinite (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  have h1 := tendsto_finSingle (fun v => (x v : v.adicCompletion L)) fun v => (hx v).le
  have h2 := tendsto_finSingle (fun v => (((x v)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L)) fun v => by
    have h : Valued.v (x v : v.adicCompletion L) = 1 := hx v
    rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]
  have h3 : Tendsto (fun v => ((localIdele L v (x v) : Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h1
  have h4 : Tendsto (fun v => (((localIdele L v (x v))⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h2
  exact h3.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h4)

/- English proof (translation)
Unfold `IsUnitAt at *`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, hx, one_pow]`.
-/
theorem isUnitAt_pow {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) (m : ℕ) :
    IsUnitAt v (x ^ m) := by
  unfold IsUnitAt at *
  rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]

/- English proof (translation)
Establish `h : ∀ v, ∃ x : (v.adicCompletion L)ˣ, IsUnitAt v x ∧ (‖((χ.loc v x : ℂˣ) : ℂ) - 1‖ < 1 / 2 → χ.UnrAt v)` using `fun v => by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `(hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow]`.

Conclude with `(hc _ (isUnitAt_pow hx m)).1`. Use `choose x hx hx' using h`. Establish `hc : Continuous fun a : Ideles L => ‖((χ.1 a : ℂˣ) : ℂ) - 1‖` using `((Units.continuous_val.comp χ.2.1).sub continuous_const).norm`. Establish `h1` using `(hc.tendsto 1).comp (tendsto_localIdele x hx)`. Establish `h2` using `h1.eventually_lt_const (u := 1 / 2) (by simp)`.

Conclude with `eventually_cofinite.1 (h2.mono fun v hv => hx' v hv)`.
-/
theorem finite_ramified (χ : HChar L) : {v | ¬ χ.UnrAt v}.Finite := by
  have h : ∀ v, ∃ x : (v.adicCompletion L)ˣ, IsUnitAt v x ∧
      (‖((χ.loc v x : ℂˣ) : ℂ) - 1‖ < 1 / 2 → χ.UnrAt v) := fun v => by
    by_contra hc
    push Not at hc
    refine (hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    exact (hc _ (isUnitAt_pow hx m)).1
  choose x hx hx' using h
  have hc : Continuous fun a : Ideles L => ‖((χ.1 a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp χ.2.1).sub continuous_const).norm
  have h1 := (hc.tendsto 1).comp (tendsto_localIdele x hx)
  have h2 := h1.eventually_lt_const (u := 1 / 2) (by simp)
  exact eventually_cofinite.1 (h2.mono fun v hv => hx' v hv)

/- English proof (translation)
Establish `hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖` using `((Units.continuous_val.comp (χ.2.1.comp (continuous_localIdele v))).sub continuous_const).norm`. Establish `h0 : {a : (v.adicCompletion L)ˣ | ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1` using `(isOpen_lt hc continuous_const).mem_nhds (by simp)`. Rewrite `h0` using `[Units.isEmbedding_val₀.nhds_eq_comap, mem_comap]`. Take `⟨t, ht, hsub⟩` from `h0`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds.mp ht`.

Establish `hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0` using `by simp`. Use `⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat, fun x hx hx1 => ?_⟩` and prove the remaining obligations. Use `Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow]`. Apply `hsub` to reduce the goal to its premises.

Apply `hγ` to reduce the goal to its premises. Simplify using `only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]`. Establish `hx' : Valued.v (x : v.adicCompletion L) = 1` using `hx`. Establish `h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1)`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1)` using `by ring`. Rewrite using `[e]`. Use `Valuation.map_add_le _ ?_ ih` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, hx', one_pow, one_mul]`. Use `(h1.trans hx1).trans_lt ?_` and prove the remaining obligations. Use `conv_rhs => rw [← WithZero.exp_log hγ0]`. Conclude with `WithZero.exp_lt_exp.mpr (by omega)`.
-/
theorem exists_levelLe (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : ∃ n, χ.LevelLe v n := by
  have hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp (χ.2.1.comp (continuous_localIdele v))).sub continuous_const).norm
  have h0 : {a : (v.adicCompletion L)ˣ | ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat, fun x hx hx1 => ?_⟩
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
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

open Classical in

/- English proof (translation)
Introduce `_ _ _ χ` and use `⟨finite_ramified χ, exists_levelLe χ⟩`.
-/
theorem unr_ae_and_level : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), {v | ¬ χ.UnrAt v}.Finite ∧ ∀ v, ∃ n, χ.LevelLe v n :=
  fun _ _ _ χ => ⟨finite_ramified χ, exists_levelLe χ⟩

end GlobalTheory.Mem.UnrAe

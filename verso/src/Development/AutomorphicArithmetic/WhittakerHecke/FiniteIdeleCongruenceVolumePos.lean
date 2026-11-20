import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Use `le_antisymm ha ?_` and prove the remaining obligations. Use `mul_le_mul' (le_refl a) hb` as an intermediate fact. Rewrite `this` using `[h, mul_one]`. Then use the resulting hypothesis.
-/
private lemma eq_one_of_mul'' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private noncomputable def ef (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (A ℚ)ˣ := (IdeleGroup.prodEquiv ℚ).symm (1, x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma ef_fst (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ((ef x : (A ℚ)ˣ) : A ℚ).1 = 1 := rfl

/- English proof (translation)
Rewrite using `[← map_mul]`. Establish `h` using `congrArg (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v) (Units.inv_mul x)`. Establish `h' : ((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v * (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1` using `h`. Rewrite using `[h', map_one]`.
-/
private lemma inv_mul_at (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : H.P ℚ) :
    Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) *
      Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
  rw [← map_mul]
  have h := congrArg (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v) (Units.inv_mul x)
  have h' : ((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
      (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
  rw [h', map_one]

/- English proof (translation)
Conclude with `hL.ne'` after adjusting the coercions.
-/
private lemma natCast_ne (L : ℕ) (hL : 0 < L) (v : H.P ℚ) : (L : H.Kv v) ≠ 0 := by
  exact_mod_cast hL.ne'

/- English proof (translation)
Establish `h2` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (L : 𝓞 ℚ)`. Rewrite `h2` using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h]`. Conclude with `h2` after adjusting the coercions.
-/
private lemma v_natCast_of_not_bad (L : ℕ) (v : H.P ℚ) (h : ¬ Bad L v) : Valued.v (L : H.Kv v) = 1 := by
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (L : 𝓞 ℚ)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h] at h2
  exact_mod_cast h2

/- English proof (translation)
Establish `hne : Ideal.span {(L : 𝓞 ℚ)} ≠ 0`. Simplify `hL.ne'` using `[Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Use `(Ideal.finite_factors hne).subset fun v hv => ?_` and prove the remaining obligations. Conclude with `Ideal.dvd_span_singleton.2 hv`.
-/
private lemma finite_bad (L : ℕ) (hL : 0 < L) : {v : H.P ℚ | Bad L v}.Finite := by
  have hne : Ideal.span {(L : 𝓞 ℚ)} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hL.ne'
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

/- English proof (translation)
Establish `hB : IsOpen {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)}`. Establish `: {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} = {y | Valued.v.restrict y ≤ Valued.v.restrict (L : H.Kv v)}`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Valuation.restrict_le_iff]`. Rewrite using `[this]`.

Conclude with `Valued.isOpen_closedBall _ (by simp [natCast_ne L hL v])`. Establish `he : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v` using `RestrictedProduct.continuous_eval v`. Establish `hf : Continuous fun x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ => (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1` using `(he.comp Units.continuous_val).sub continuous_const`. Use `(hB.preimage hf).mem_nhds ?_` and prove the remaining obligations. Establish `h0 : ((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 = 0` using `sub_self _`.

Express the relevant statement in the definitionally equal form `Valued.v (((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ _`. Rewrite using `[h0, map_zero]`. Conclude with `zero_le'`.
-/
private lemma nhds_cong (L : ℕ) (hL : 0 < L) (v : H.P ℚ) :
    {x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ | Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ Valued.v (L : H.Kv v)} ∈
      𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
  have hB : IsOpen {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} := by
    have : {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} =
        {y | Valued.v.restrict y ≤ Valued.v.restrict (L : H.Kv v)} := by
      ext y
      simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff]
    rw [this]
    exact Valued.isOpen_closedBall _ (by simp [natCast_ne L hL v])
  have he : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v := RestrictedProduct.continuous_eval v
  have hf : Continuous fun x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ => (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 :=
    (he.comp Units.continuous_val).sub continuous_const
  refine (hB.preimage hf).mem_nhds ?_
  have h0 : ((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 = 0 := sub_self _
  change Valued.v (((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ _
  rw [h0, map_zero]
  exact zero_le'

/- English proof (translation)
Introduce `L hL`. Use `set S : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (fun u => (IdeleGroup.prodEquiv ℚ).symm (1, u)) ⁻¹' TT L with hS`. Establish `hcT : cT L = (finiteIdeleMeasure ℚ S).toReal` using `rfl`. Establish `hsub : S ⊆ (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)`. Introduce `x hx`.

Establish `hu : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1` using `fun v => hx.1.2 v`. Use `(mem_finiteIntegralUnits ℚ).2 fun v => ?_` and prove the remaining obligations. Establish `hi` using `inv_mul_at x v`. Rewrite `hi` using `[hu v, mul_one]`. Conclude with `⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hu v).le, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩`.

Establish `hnhds : S ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)`. Establish `h1 : (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)` using `(isOpen_finiteIntegralUnits ℚ).mem_nhds (one_mem _)`. Establish `h2` using `(Filter.biInter_mem (finite_bad L hL)).2 fun v (_ : Bad L v) => nhds_cong L hL v`. Use `filter_upwards [h1, h2] with x hx hc`. Take `hxi` from `(mem_finiteIntegralUnits ℚ).1 hx`.

Establish `hle : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1` using `fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).1`. Establish `hle' : ∀ v : H.P ℚ, Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1` using `fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).2`. Use `⟨⟨ef_fst x, fun v => ?_⟩, fun v => ?_⟩` and prove the remaining obligations. Conclude with `eq_one_of_mul'' (hle v) (hle' v) (by rw [mul_comm]; exact inv_mul_at x v)`. Establish `hcp : H.cp v ((ef x : (A ℚ)ˣ) : A ℚ) - 1 = (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1` using `rfl`.

Express the relevant statement in the definitionally equal form `Valued.v (H.cp v (((ef x : (A ℚ)ˣ) : A ℚ) - 1)) ≤ _`. Rewrite using `[map_sub, map_one, hcp]`. Distinguish the cases in `hb : Bad L v`. Conclude with `Set.mem_iInter₂.1 hc v hb`. Rewrite using `[v_natCast_of_not_bad L v hb]`.

Use `(Valuation.map_sub _ _ _).trans (max_le (hle v) ?_)` and prove the remaining obligations. Rewrite using `[map_one]`. Rewrite using `[hcT]`. Use `ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds _ hnhds).ne' ?_` and prove the remaining obligations. Use `((measure_mono hsub).trans_lt ?_).ne` and prove the remaining obligations.

Rewrite using `[finiteIdeleMeasure_finiteIntegralUnits]`. Conclude with `ENNReal.one_lt_top`.
-/
theorem UpperTheory.finiteIdele_congruenceVolume_pos :
    ∀ L : ℕ, 0 < L → 0 < cT L := by
  intro L hL
  set S : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (fun u => (IdeleGroup.prodEquiv ℚ).symm (1, u)) ⁻¹' TT L with hS
  have hcT : cT L = (finiteIdeleMeasure ℚ S).toReal := rfl
  have hsub : S ⊆ (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    intro x hx
    have hu : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := fun v => hx.1.2 v
    refine (mem_finiteIntegralUnits ℚ).2 fun v => ?_
    have hi := inv_mul_at x v
    rw [hu v, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hu v).le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  have hnhds : S ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    have h1 : (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
      (isOpen_finiteIntegralUnits ℚ).mem_nhds (one_mem _)
    have h2 := (Filter.biInter_mem (finite_bad L hL)).2 fun v (_ : Bad L v) => nhds_cong L hL v
    filter_upwards [h1, h2] with x hx hc
    obtain hxi := (mem_finiteIntegralUnits ℚ).1 hx
    have hle : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 := fun v =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).1
    have hle' : ∀ v : H.P ℚ, Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 :=
      fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).2
    refine ⟨⟨ef_fst x, fun v => ?_⟩, fun v => ?_⟩
    · exact eq_one_of_mul'' (hle v) (hle' v) (by rw [mul_comm]; exact inv_mul_at x v)
    · have hcp : H.cp v ((ef x : (A ℚ)ˣ) : A ℚ) - 1 = (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 := rfl
      change Valued.v (H.cp v (((ef x : (A ℚ)ˣ) : A ℚ) - 1)) ≤ _
      rw [map_sub, map_one, hcp]
      by_cases hb : Bad L v
      · exact Set.mem_iInter₂.1 hc v hb
      · rw [v_natCast_of_not_bad L v hb]
        refine (Valuation.map_sub _ _ _).trans (max_le (hle v) ?_)
        rw [map_one]
  rw [hcT]
  refine ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds _ hnhds).ne' ?_
  refine ((measure_mono hsub).trans_lt ?_).ne
  rw [finiteIdeleMeasure_finiteIntegralUnits]
  exact ENNReal.one_lt_top

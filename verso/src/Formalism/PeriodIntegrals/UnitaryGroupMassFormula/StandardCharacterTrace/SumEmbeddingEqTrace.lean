import Mathlib
import Formalism.PeriodIntegrals.StdCharTR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInter
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInterAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IsOpenIntSub

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes InfinitePlace.Completion

namespace PI.StdCharTRWork

variable (F : Type) [Field F] [NumberField F]

def Lre : Ainf F →+ ℝ where
  toFun a := ∑ w : InfinitePlace F, (extensionEmbedding w (a w)).re
  map_zero' := by
    show ∑ w : InfinitePlace F, (extensionEmbedding w ((0 : ∀ v : InfinitePlace F, v.Completion) w)).re = 0
    simp
  map_add' a b :=
    (Finset.sum_congr rfl fun w _ => (congrArg Complex.re (map_add (extensionEmbedding w) (a w) (b w))).trans
      (Complex.add_re _ _)).trans Finset.sum_add_distrib

/- English proof (translation)
Use `show Continuous (fun a : Ainf F => ∑ w : InfinitePlace F, (extensionEmbedding w (a w)).re)`. Conclude with `continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ((isometry_extensionEmbedding w).continuous.comp (continuous_apply w))`.
-/
theorem continuous_Lre : Continuous (Lre F) := by
  show Continuous (fun a : Ainf F => ∑ w : InfinitePlace F, (extensionEmbedding w (a w)).re)
  exact continuous_finset_sum _ fun w _ =>
    Complex.continuous_re.comp ((isometry_extensionEmbedding w).continuous.comp (continuous_apply w))

/- English proof (translation)
Establish `hreal : ∀ φ : F →+* ℂ, NumberField.ComplexEmbedding.IsReal φ` using `fun φ => InfinitePlace.isReal_mk_iff.1 (NumberField.IsTotallyReal.isReal _)`. Establish `e1 : ∀ φ : F →+* ℂ, (InfinitePlace.mk φ).embedding = φ` using `fun φ => InfinitePlace.embedding_mk_eq_of_isReal (hreal φ)`. Set `eqv : (F →ₐ[ℚ] ℂ) ≃ InfinitePlace F` to `{ toFun := fun σ => InfinitePlace.mk σ.toRingHom invFun := fun w => w.embedding.toRatAlgHom left_inv := fun σ => by`. Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `x`.

Simplify using `[e1]`. Use `right_inv := fun w => by simp [InfinitePlace.mk_embedding] }`. Rewrite using `[trace_eq_sum_embeddings ℂ]`. Conclude with `(Fintype.sum_equiv eqv _ _ fun σ => by simp [eqv, e1]).symm`.
-/
theorem sum_embedding_eq_trace [IsTotallyReal F] (y : F) :
    ∑ v : InfinitePlace F, v.embedding y = algebraMap ℚ ℂ (Algebra.trace ℚ F y) := by
  have hreal : ∀ φ : F →+* ℂ, NumberField.ComplexEmbedding.IsReal φ := fun φ =>
    InfinitePlace.isReal_mk_iff.1 (NumberField.IsTotallyReal.isReal _)
  have e1 : ∀ φ : F →+* ℂ, (InfinitePlace.mk φ).embedding = φ := fun φ =>
    InfinitePlace.embedding_mk_eq_of_isReal (hreal φ)
  let eqv : (F →ₐ[ℚ] ℂ) ≃ InfinitePlace F :=
    { toFun := fun σ => InfinitePlace.mk σ.toRingHom
      invFun := fun w => w.embedding.toRatAlgHom
      left_inv := fun σ => by
        apply AlgHom.ext
        intro x
        simp [e1]
      right_inv := fun w => by simp [InfinitePlace.mk_embedding] }
  rw [trace_eq_sum_embeddings ℂ]
  exact (Fintype.sum_equiv eqv _ _ fun σ => by simp [eqv, e1]).symm

/- English proof (translation)
Use `show ∑ w : InfinitePlace F, (extensionEmbedding w (algebraMap F (Ainf F) b w)).re = _`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `first`.

Consider the case `exact extensionEmbedding_coe w b`. Consider the case `simp [InfiniteAdeleRing.algebraMap_apply, extensionEmbedding_coe]`.
-/
theorem Lre_algebraMap (b : F) :
    Lre F (algebraMap F (Ainf F) b) = (∑ v : InfinitePlace F, v.embedding b).re := by
  show ∑ w : InfinitePlace F, (extensionEmbedding w (algebraMap F (Ainf F) b w)).re = _
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  first
    | exact extensionEmbedding_coe w b
    | simp [InfiniteAdeleRing.algebraMap_apply, extensionEmbedding_coe]

/- English proof (translation)
Rewrite using `[Lre_algebraMap, sum_embedding_eq_trace]`. Establish `hint : IsIntegral ℤ (Algebra.trace ℚ F (b : F))` using `Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe b)`. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn]`.

Simplify using the standard rewrite rules.
-/
theorem Lre_int [IsTotallyReal F] (b : 𝓞 F) : ∃ n : ℤ, Lre F (algebraMap F (Ainf F) (b : F)) = n := by
  rw [Lre_algebraMap, sum_embedding_eq_trace]
  have hint : IsIntegral ℤ (Algebra.trace ℚ F (b : F)) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe b)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨n, ?_⟩
  rw [← hn]
  simp

/- English proof (translation)
Establish `hn : 0 < Fintype.card (InfinitePlace F)` using `Fintype.card_pos`. Use `⟨algebraMap F (Ainf F) ((1 : F) / (2 * (Fintype.card (InfinitePlace F) : F))), ?_⟩` and prove the remaining obligations. Rewrite using `[Lre_algebraMap]`. Simplify using `only [map_div₀, map_one, map_mul, map_ofNat, map_natCast]`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Establish `hn' : (Fintype.card (InfinitePlace F) : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Rewrite using `[show ((Fintype.card (InfinitePlace F) : ℂ) * (1 / (2 * (Fintype.card (InfinitePlace F) : ℂ)))) = 1 / 2 by field_simp]`. Evaluate the numerical expressions.
-/
theorem exists_Lre_half [IsTotallyReal F] : ∃ t : Ainf F, Lre F t = 1 / 2 := by
  have hn : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  refine ⟨algebraMap F (Ainf F) ((1 : F) / (2 * (Fintype.card (InfinitePlace F) : F))), ?_⟩
  rw [Lre_algebraMap]
  simp only [map_div₀, map_one, map_mul, map_ofNat, map_natCast]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn' : (Fintype.card (InfinitePlace F) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show ((Fintype.card (InfinitePlace F) : ℂ) * (1 / (2 * (Fintype.card (InfinitePlace F) : ℂ)))) = 1 / 2 by
    field_simp]
  norm_num

/- English proof (translation)
Introduce `F _ _ hTR`. Set `mk1 : ℝ →+ AddCircle (1 : ℝ)` to `QuotientAddGroup.mk' _`. Set `g : AF F →+ AddCircle (1 : ℝ)` to `mk1.comp ((Lre F).comp (AddMonoidHom.fst (Ainf F) (Af F)))`. Establish `hg : Continuous g` using `(continuous_quotient_mk').comp ((continuous_Lre F).comp continuous_fst)`. Set `K : AddSubgroup (AF F)` to `(algebraMap F (AF F)).toAddMonoidHom.range`.

Establish `hU : IsOpen (PI.GaugeCharW.intSub F : Set (AF F))` using `PI.GaugeCharW.isOpen_intSub F PI.GaugeCharW.openInt`. Establish `hKU : ∀ x ∈ K, x ∈ PI.GaugeCharW.intSub F → g x = 0`. Introduce and unpack `_ ⟨a, rfl⟩ hx`. Establish `hx' : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), sndA F (algebraMap F (AF F) a) v ∈ v.adicCompletionIntegers F` using `hx`. Take `⟨b, hb⟩` from `PI.GaugeCharW.intInter F a (fun v => hx' v)`.

Take `⟨n, hn⟩` from `Lre_int F b`. Use `show ((Lre F (algebraMap F (Ainf F) a) : ℝ) : AddCircle (1 : ℝ)) = 0`. Rewrite using `[← hb, hn]`. Conclude with `(QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples_iff.2 ⟨n, by simp⟩)`. Take `⟨h, hcont, hK, hUeq⟩` from `PI.GaugeCharW.extChar (AF F) K _ hU g hg hKU`.

Set `ψ : AddChar (AF F) ℂ` to `{ toFun := fun x => ((AddCircle.toCircle (h x) : Circle) : ℂ) map_zero_eq_one' := by simp [AddCircle.toCircle_zero] map_add_eq_mul' := fun a b => by simp [map_add, AddCircle.toCircle_add] }`. Establish `hψ : ∀ x, ψ x = ((AddCircle.toCircle (h x) : Circle) : ℂ)` using `fun _ => rfl`. Establish `hpair : ∀ x : Ainf F, pairA F x 0 ∈ PI.GaugeCharW.intSub F`. Introduce `x`. Use `show ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), sndA F (pairA F x 0) v ∈ v.adicCompletionIntegers F`.

Introduce `v`. Establish `e : sndA F (pairA F x 0) = 0` using `rfl`. Rewrite using `[e]`. Conclude with `zero_mem _`. Establish `hval : ∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((Lre F x : ℝ) : ℂ))`.

Introduce `x`. Rewrite using `[hψ, hUeq _ (hpair x)]`. Use `show ((AddCircle.toCircle ((Lre F x : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ) = _`. Rewrite using `[AddCircle.toCircle_apply_mk, Circle.coe_exp]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨ψ, ⟨?_, ?_, ?_, ?_⟩, fun x => hval x⟩` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp hcont)`. Introduce `x`.

Rewrite using `[hψ]`. Use `first`. Consider the case `exact Circle.norm_coe _`. Consider the case `exact Circle.abs_coe _`. Consider the case `simp [Circle.norm_coe]`.

Introduce `a`. Establish `e : h (algebraMap F (AF F) a) = 0` using `hK _ ⟨a, rfl⟩`. Rewrite using `[hψ, e, AddCircle.toCircle_zero]`. Both sides reduce to the same expression. Take `⟨t, ht⟩` from `exists_Lre_half F`.

Use `⟨pairA F t 0, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, ht]`. Establish `e : Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1`. Rewrite using `[show 2 * (Real.pi : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) = Real.pi * Complex.I by push_cast; ring]`. Conclude with `Complex.exp_pi_mul_I`.

Rewrite using `[e]`. Evaluate the numerical expressions.
-/
theorem stdCharTR_main : PI.StdCharTR.Target := by
  intro F _ _ hTR
  let mk1 : ℝ →+ AddCircle (1 : ℝ) := QuotientAddGroup.mk' _
  let g : AF F →+ AddCircle (1 : ℝ) := mk1.comp ((Lre F).comp (AddMonoidHom.fst (Ainf F) (Af F)))
  have hg : Continuous g :=
    (continuous_quotient_mk').comp ((continuous_Lre F).comp continuous_fst)
  let K : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range
  have hU : IsOpen (PI.GaugeCharW.intSub F : Set (AF F)) :=
    PI.GaugeCharW.isOpen_intSub F PI.GaugeCharW.openInt
  have hKU : ∀ x ∈ K, x ∈ PI.GaugeCharW.intSub F → g x = 0 := by
    rintro _ ⟨a, rfl⟩ hx
    have hx' : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        sndA F (algebraMap F (AF F) a) v ∈ v.adicCompletionIntegers F := hx
    obtain ⟨b, hb⟩ := PI.GaugeCharW.intInter F a (fun v => hx' v)
    obtain ⟨n, hn⟩ := Lre_int F b
    show ((Lre F (algebraMap F (Ainf F) a) : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [← hb, hn]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples_iff.2 ⟨n, by simp⟩)
  obtain ⟨h, hcont, hK, hUeq⟩ := PI.GaugeCharW.extChar (AF F) K _ hU g hg hKU
  let ψ : AddChar (AF F) ℂ :=
    { toFun := fun x => ((AddCircle.toCircle (h x) : Circle) : ℂ)
      map_zero_eq_one' := by simp [AddCircle.toCircle_zero]
      map_add_eq_mul' := fun a b => by simp [map_add, AddCircle.toCircle_add] }
  have hψ : ∀ x, ψ x = ((AddCircle.toCircle (h x) : Circle) : ℂ) := fun _ => rfl
  have hpair : ∀ x : Ainf F, pairA F x 0 ∈ PI.GaugeCharW.intSub F := by
    intro x
    show ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), sndA F (pairA F x 0) v ∈ v.adicCompletionIntegers F
    intro v
    have e : sndA F (pairA F x 0) = 0 := rfl
    rw [e]
    exact zero_mem _
  have hval : ∀ x : Ainf F, ψ (pairA F x 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Lre F x : ℝ) : ℂ)) := by
    intro x
    rw [hψ, hUeq _ (hpair x)]
    show ((AddCircle.toCircle ((Lre F x : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ) = _
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 1
    push_cast
    ring
  refine ⟨ψ, ⟨?_, ?_, ?_, ?_⟩, fun x => hval x⟩
  · exact continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp hcont)
  · intro x
    rw [hψ]
    first
      | exact Circle.norm_coe _
      | exact Circle.abs_coe _
      | simp [Circle.norm_coe]
  · intro a
    have e : h (algebraMap F (AF F) a) = 0 := hK _ ⟨a, rfl⟩
    rw [hψ, e, AddCircle.toCircle_zero]
    rfl
  · obtain ⟨t, ht⟩ := exists_Lre_half F
    refine ⟨pairA F t 0, ?_⟩
    rw [hval, ht]
    have e : Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) = Real.pi * Complex.I by push_cast; ring]
      exact Complex.exp_pi_mul_I
    rw [e]
    norm_num

end PI.StdCharTRWork

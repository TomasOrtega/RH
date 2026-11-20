import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.StatementG
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

namespace GlobalTheory.InertConj

/- English proof (translation)
Establish `h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = P.asIdeal` using `h`. Establish `key : P.asIdeal ≤ Ideal.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) P.asIdeal` using `by conv_lhs => rw [← h']`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `s hs`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap]`.

Express the relevant statement in the definitionally equal form `IsCMField.ringOfIntegersComplexConj E _ ∈ _`. Rewrite using `[AlgEquiv.commutes, ← h']`. Conclude with `Ideal.mem_map_of_mem _ hs`. Conclude with `key hx`.
-/
theorem conj_mem_of_inert {E : Type} [Field E] [NumberField E] [IsCMField E]
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {P : HeightOneSpectrum (𝓞 E)}
    (h : IsInertAt (maximalRealSubfield E) E v P) {x : 𝓞 E} (hx : x ∈ P.asIdeal) :
    IsCMField.ringOfIntegersComplexConj E x ∈ P.asIdeal := by
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have key : P.asIdeal ≤ Ideal.comap
      (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) P.asIdeal := by
    conv_lhs => rw [← h']
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change IsCMField.ringOfIntegersComplexConj E _ ∈ _
    rw [AlgEquiv.commutes, ← h']
    exact Ideal.mem_map_of_mem _ hs
  exact key hx

/- English proof (translation)
Introduce `E _ _ _ _ v P h`. Establish `h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = P.asIdeal` using `h`. Establish `hc : Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv P P`. Rewrite using `[Mem.Chr.conjPl_iff_mem]`. Introduce `x y hxy`.

Establish `e : y = IsCMField.ringOfIntegersComplexConj E x` using `RingOfIntegers.ext hxy`. Rewrite using `[e]`. Use `⟨conj_mem_of_inert h, fun hx => ?_⟩` and prove the remaining obligations. Establish `h2` using `conj_mem_of_inert h hx`. Establish `e2 : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E x) = x` using `by ext; simp`.

Rewrite `h2` using `[e2]`. Then use the resulting hypothesis. Take `⟨σ, σ1, σ2, σ3⟩` from `UnramCompletion.exists_ringEquiv P _ hc`. Establish `σ2' : ∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)` using `σ2`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, hs2⟩ : ∃ s ∈ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∉ P.asIdeal ^ 2 := by`. Assume the negation of the conclusion as `hn`.

Use `push Not at hn`. Establish `h1 : P.asIdeal ≤ P.asIdeal ^ 2` using `by conv_lhs => rw [← h']`. Conclude with `Ideal.map_le_iff_le_comap.2 hn`. Conclude with `(Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl).not_ge h1`. Establish `hs1 : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∈ P.asIdeal` using `h' ▸ Ideal.mem_map_of_mem _ hs`.

Establish `hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (a : E)) = P.valuation E (algebraMap (𝓞 E) E a)` using `fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _`. Use `⟨σ, algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E), σ2', ?_, σ3, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Use `congrFun (UnramCompletion.ringHom_ext_of_continuous P (f := fun x => σ (σ x)) (σ1.comp σ1) continuous_id fun k => ?_) x` and prove the remaining obligations. Simplify using `[σ2', ReciprocityTheory.ChartRestriction.G.FD.cc]`.

Take `⟨x, hx⟩` from `exists_sub_conj_notMem P.asIdeal P.isPrime.ne_top`. Use `⟨algebraMap E _ (x : E), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`. Conclude with `P.valuation_le_one x`. Express the relevant statement in the definitionally equal form `Valued.v (σ _ - _) = 1`.

Rewrite using `[Valuation.map_sub_swap, σ2', ← map_sub]`. Conclude with `(hval (x - IsCMField.ringOfIntegersComplexConj E x)).trans ((HeightOneSpectrum.valuation_eq_one_iff_notMem P).2 hx)`. Express the relevant statement in the definitionally equal form `σ _ = _`. Rewrite using `[σ2', cc_algebraMap]`. Unfold `IsUnifV`.

Rewrite using `[hval, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `UnramCompletion.intValuation_eq_of_notMem_sq P hs1 hs2`.
-/
theorem exists_conj_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∃ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E), (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) ∧ (∀ x, σ (σ x) = x) ∧ (∀ x, Valued.v (σ x) = Valued.v x) ∧ (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) ∧ σ ϖ = ϖ ∧ IsUnifV E P ϖ := by
  intro E _ _ _ _ v P h
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have hc : Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv P P := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = IsCMField.ringOfIntegersComplexConj E x := RingOfIntegers.ext hxy
    rw [e]
    refine ⟨conj_mem_of_inert h, fun hx => ?_⟩
    have h2 := conj_mem_of_inert h hx
    have e2 : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E x) = x := by
      ext; simp
    rwa [e2] at h2
  obtain ⟨σ, σ1, σ2, σ3⟩ := UnramCompletion.exists_ringEquiv P _ hc
  have σ2' : ∀ x : E, σ (algebraMap E (P.adicCompletion E) x) =
      algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x) := σ2
  obtain ⟨s, hs, hs2⟩ : ∃ s ∈ v.asIdeal,
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∉ P.asIdeal ^ 2 := by
    by_contra hn
    push Not at hn
    have h1 : P.asIdeal ≤ P.asIdeal ^ 2 := by
      conv_lhs => rw [← h']
      exact Ideal.map_le_iff_le_comap.2 hn
    exact (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl).not_ge h1
  have hs1 : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∈ P.asIdeal :=
    h' ▸ Ideal.mem_map_of_mem _ hs
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (a : E)) =
      P.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  refine ⟨σ, algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E), σ2', ?_, σ3,
    ?_, ?_, ?_⟩
  · intro x
    refine congrFun (UnramCompletion.ringHom_ext_of_continuous P (f := fun x => σ (σ x))
      (σ1.comp σ1) continuous_id fun k => ?_) x
    simp [σ2', ReciprocityTheory.ChartRestriction.G.FD.cc]
  · obtain ⟨x, hx⟩ := exists_sub_conj_notMem P.asIdeal P.isPrime.ne_top
    refine ⟨algebraMap E _ (x : E), ?_, ?_⟩
    · rw [hval]; exact P.valuation_le_one x
    · change Valued.v (σ _ - _) = 1
      rw [Valuation.map_sub_swap, σ2', ← map_sub]
      exact (hval (x - IsCMField.ringOfIntegersComplexConj E x)).trans
        ((HeightOneSpectrum.valuation_eq_one_iff_notMem P).2 hx)
  · change σ _ = _
    rw [σ2', cc_algebraMap]
  · unfold IsUnifV
    rw [hval, HeightOneSpectrum.valuation_of_algebraMap]
    exact UnramCompletion.intValuation_eq_of_notMem_sq P hs1 hs2

end GlobalTheory.InertConj

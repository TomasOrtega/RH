import Mathlib

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.AdeleDiscrete

/- English proof (translation)
Introduce `F _ _`. Establish `hU : IsOpen (X` using `InfiniteAdeleRing F) (Set.pi Set.univ fun v : InfinitePlace F => Metric.ball (0 : v.Completion) 1) := isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball`. Establish `hV : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F}` using `RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)`. Use `⟨_, (hU.prod hV).mem_nhds ⟨fun v _ => Metric.mem_ball_self one_pos, fun v => zero_mem _⟩, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hx`.

Take `⟨a, rfl⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v => by`. Establish `h` using `h2 v`. Rewrite `h` using `[AdeleRing.algebraMap_snd_apply, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `h`. Establish `hlt : ∀ w : InfinitePlace F, w (algebraMap (𝓞 F) F a) < 1` using `fun w => by`.

Establish `h` using `h1 w trivial`. Rewrite `h` using `[mem_ball_zero_iff, AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.norm_coe]`. Conclude with `h`. Assume the negation of the conclusion as `h0`. Establish `ha : a ≠ 0` using `fun h => h0 (by rw [h, map_zero])`.

Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Conclude with `absurd (InfinitePlace.one_le_of_lt_one (w := w) ha fun z _ => hlt z) (not_le.2 (hlt w))`.
-/
theorem exists_nhds_zero_principal_eq_zero : ∀ (F : Type) [Field F] [NumberField F], ∃ U ∈ nhds (0 : AdeleRing (𝓞 F) F), ∀ x : F, algebraMap F (AdeleRing (𝓞 F) F) x ∈ U → x = 0 := by
  intro F _ _
  have hU : IsOpen (X := InfiniteAdeleRing F)
      (Set.pi Set.univ fun v : InfinitePlace F => Metric.ball (0 : v.Completion) 1) :=
    isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  have hV : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  refine ⟨_, (hU.prod hV).mem_nhds ⟨fun v _ => Metric.mem_ball_self one_pos,
    fun v => zero_mem _⟩, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v => by
    have h := h2 v
    rw [AdeleRing.algebraMap_snd_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  have hlt : ∀ w : InfinitePlace F, w (algebraMap (𝓞 F) F a) < 1 := fun w => by
    have h := h1 w trivial
    rw [mem_ball_zero_iff, AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.norm_coe] at h
    exact h
  by_contra h0
  have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one (w := w) ha fun z _ => hlt z) (not_le.2 (hlt w))

end GlobalTheory.AdeleDiscrete

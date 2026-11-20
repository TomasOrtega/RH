import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

noncomputable section

namespace PositivityTheory.ThK

open NumberField IsDedekindDomain GlobalTheory.AdelicU

/- English proof (translation)
Use `haveI := v.isMaximal`. Take `⟨P, hP⟩` from `Set.ncard_eq_one.1 h`. Establish `hm : P ∈ v.asIdeal.primesOver (𝓞 E)` using `hP ▸ rfl`. Use `haveI := hm.1`. Use `haveI := hm.2`.

Establish `h0 : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P`. Use `⟨⟨P, hm.1, h0⟩, ?_⟩` and prove the remaining obligations. Establish `e : P.ramificationIdx (𝓞 F) = 1` using `P.ramificationIdx_eq_one (𝓞 F)`. Use `Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 E) v.ne_bot` as an intermediate fact. Rewrite using `[this]`.

Simplify using `[hP, e]`.
-/
theorem map_eq_of_ncard_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.Unramified (𝓞 F) (𝓞 E)] (v : HeightOneSpectrum (𝓞 F)) (h : (v.asIdeal.primesOver (𝓞 E)).ncard = 1) :
    ∃ w : HeightOneSpectrum (𝓞 E), Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := by
  classical
  haveI := v.isMaximal
  obtain ⟨P, hP⟩ := Set.ncard_eq_one.1 h
  have hm : P ∈ v.asIdeal.primesOver (𝓞 E) := hP ▸ rfl
  haveI := hm.1
  haveI := hm.2
  have h0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  refine ⟨⟨P, hm.1, h0⟩, ?_⟩
  have e : P.ramificationIdx (𝓞 F) = 1 := P.ramificationIdx_eq_one (𝓞 F)
  have := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 E) v.ne_bot
  rw [this]
  simp [hP, e]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB v he`. Use `haveI := hB.unram`. Use `haveI := v.isMaximal`. Establish `h1` using `ncard_primesOver_le_two hB.cm v`. Establish `h2 : (v.asIdeal.primesOver (𝓞 E)).ncard ≠ 2` using `fun h => not_nonempty_iff.2 he ((nonempty_split_iff hB.cm).2 h)`.

Establish `h3 : 0 < (v.asIdeal.primesOver (𝓞 E)).ncard` using `Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero _ _)`. Conclude with `map_eq_of_ncard_eq_one v (by omega)`.
-/
theorem inert_of_local : InertOf := by
  intro F E _ _ _ _ _ σ B hB v he
  haveI := hB.unram
  haveI := v.isMaximal
  have h1 := ncard_primesOver_le_two hB.cm v
  have h2 : (v.asIdeal.primesOver (𝓞 E)).ncard ≠ 2 := fun h =>
    not_nonempty_iff.2 he ((nonempty_split_iff hB.cm).2 h)
  have h3 : 0 < (v.asIdeal.primesOver (𝓞 E)).ncard := Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero _ _)
  exact map_eq_of_ncard_eq_one v (by omega)

end PositivityTheory.ThK

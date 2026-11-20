import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame

noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain

namespace PI.UnitaryDimensionFormula

section
variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `map_natCast (Formalism.UG.evalV F v) g`.
-/
theorem adAd_natCast_apply (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (g : FiniteAdeleRing (𝓞 F) F) v = (g : v.adicCompletion F) :=
  map_natCast (Formalism.UG.evalV F v) g

/- English proof (translation)
Establish `e1 : (g : v.adicCompletion F) = ((g : F) : v.adicCompletion F)`. Conclude with `(map_natCast (algebraMap F (v.adicCompletion F)) g).symm`. Rewrite using `[e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Establish `e2 : (g : F) = algebraMap (𝓞 F) F (g : 𝓞 F)` using `(map_natCast _ g).symm`. Rewrite using `[e2, HeightOneSpectrum.valuation_of_algebraMap]`.
-/
theorem adAd_val_g (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (g : v.adicCompletion F) = v.intValuation (g : 𝓞 F) := by
  have e1 : (g : v.adicCompletion F) = ((g : F) : v.adicCompletion F) := by
    exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have e2 : (g : F) = algebraMap (𝓞 F) F (g : 𝓞 F) := (map_natCast _ g).symm
  rw [e2, HeightOneSpectrum.valuation_of_algebraMap]

/- English proof (translation)
Rewrite using `[adAd_val_g]`. Conclude with `(v.intValuation_lt_one_iff_mem _).2 h`.
-/
theorem adAd_val_lt (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : (g : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) < 1 := by
  rw [adAd_val_g]; exact (v.intValuation_lt_one_iff_mem _).2 h

/- English proof (translation)
Rewrite using `[adAd_val_g]`. Conclude with `(v.intValuation_eq_one_iff_mem_primeCompl _).2 h`.
-/
theorem adAd_val_one (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : (g : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) = 1 := by
  rw [adAd_val_g]
  exact (v.intValuation_eq_one_iff_mem_primeCompl _).2 h

def adOfInt (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨f, Filter.Eventually.of_forall hf⟩

/- English proof (translation)
The claim follows from `hf`.
-/
theorem adOfInt_int (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : adOfInt f hf ∈ Formalism.UG.intAd F := hf

end

/- English proof (translation)
Introduce `F _ _ g`. Set `P : HeightOneSpectrum (𝓞 F) → Prop` to `fun v => (g : 𝓞 F) ∈ v.asIdeal`. Establish `h01 : ∀ v : HeightOneSpectrum (𝓞 F), (if P v then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F`. Introduce `v`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Set `e` to `adOfInt (fun v => if P v then (1 : v.adicCompletion F) else 0) h01`. Use `⟨e, adOfInt_int _ _, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine FiniteAdeleRing.ext _ fun v => ?_ show (if P v then (1 : v.adicCompletion F) else 0) * (if P v then 1 else 0) = if P v then 1 else 0 split_ifs <;> simp`.

Establish `ht : ∀ v : HeightOneSpectrum (𝓞 F), (if P v then (0 : v.adicCompletion F) else (g : v.adicCompletion F)⁻¹) ∈ v.adicCompletionIntegers F`. Introduce `v`. Use `split_ifs with hv`. Conclude with `zero_mem _`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, adAd_val_one g v hv, inv_one]`.

Use `⟨adOfInt _ ht, adOfInt_int _ _, ?_⟩` and prove the remaining obligations. Use `FiniteAdeleRing.ext _ fun v => ?_` and prove the remaining obligations. Use `show (1 : v.adicCompletion F) - (if P v then 1 else 0) = (g : FiniteAdeleRing (𝓞 F) F) v * (if P v then 0 else (g : v.adicCompletion F)⁻¹)`. Rewrite using `[adAd_natCast_apply]`. Use `split_ifs with hv`.

Simplify using the standard rewrite rules. Establish `hne : (g : v.adicCompletion F) ≠ 0`. Introduce `h0`. Use `adAd_val_one g v hv` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`.

Conclude with `zero_ne_one this`. Rewrite using `[sub_zero, mul_inv_cancel₀ hne]`. Introduce `c hc`. Establish `hu : ∀ v : HeightOneSpectrum (𝓞 F), P v → Valued.v (1 + (g : v.adicCompletion F) * c v) = 1`. Introduce `v hv`.

Establish `hlt : Valued.v ((g : v.adicCompletion F) * c v) < 1`. Rewrite using `[map_mul]`. Establish `hcv : Valued.v (c v) ≤ 1` using `hc v`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hlt), map_one]`.

Establish `hy : ∀ v : HeightOneSpectrum (𝓞 F), (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) ∈ v.adicCompletionIntegers F`. Introduce `v`. Use `split_ifs with hv`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu v hv, inv_one]`. Conclude with `zero_mem _`.

Use `⟨adOfInt _ hy, adOfInt_int _ _, ?_⟩` and prove the remaining obligations. Use `FiniteAdeleRing.ext _ fun v => ?_` and prove the remaining obligations. Use `show (if P v then (1 : v.adicCompletion F) else 0) * (1 + (g : FiniteAdeleRing (𝓞 F) F) v * c v) * (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) = if P v then 1 else 0`. Rewrite using `[adAd_natCast_apply]`. Use `split_ifs with hv`.

Establish `hne : (1 + (g : v.adicCompletion F) * c v) ≠ 0`. Introduce `h0`. Use `hu v hv` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `zero_ne_one this`.

Rewrite using `[one_mul, mul_inv_cancel₀ hne]`. Simplify using the standard rewrite rules.
-/
theorem idxDAd : IdxDAd := by
  intro F _ _ g
  let P : HeightOneSpectrum (𝓞 F) → Prop := fun v => (g : 𝓞 F) ∈ v.asIdeal
  have h01 : ∀ v : HeightOneSpectrum (𝓞 F),
      (if P v then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F := by
    intro v; split_ifs
    · exact one_mem _
    · exact zero_mem _
  let e := adOfInt (fun v => if P v then (1 : v.adicCompletion F) else 0) h01
  refine ⟨e, adOfInt_int _ _, ?_, ?_, ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show (if P v then (1 : v.adicCompletion F) else 0) * (if P v then 1 else 0) = if P v then 1 else 0
    split_ifs <;> simp
  · have ht : ∀ v : HeightOneSpectrum (𝓞 F),
        (if P v then (0 : v.adicCompletion F) else (g : v.adicCompletion F)⁻¹) ∈ v.adicCompletionIntegers F := by
      intro v
      split_ifs with hv
      · exact zero_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, adAd_val_one g v hv, inv_one]
    refine ⟨adOfInt _ ht, adOfInt_int _ _, ?_⟩
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (1 : v.adicCompletion F) - (if P v then 1 else 0) =
      (g : FiniteAdeleRing (𝓞 F) F) v * (if P v then 0 else (g : v.adicCompletion F)⁻¹)
    rw [adAd_natCast_apply]
    split_ifs with hv
    · simp
    · have hne : (g : v.adicCompletion F) ≠ 0 := by
        intro h0
        have := adAd_val_one g v hv
        rw [h0, map_zero] at this
        exact zero_ne_one this
      rw [sub_zero, mul_inv_cancel₀ hne]
  · intro c hc
    have hu : ∀ v : HeightOneSpectrum (𝓞 F), P v →
        Valued.v (1 + (g : v.adicCompletion F) * c v) = 1 := by
      intro v hv
      have hlt : Valued.v ((g : v.adicCompletion F) * c v) < 1 := by
        rw [map_mul]
        have hcv : Valued.v (c v) ≤ 1 := hc v
        calc Valued.v (g : v.adicCompletion F) * Valued.v (c v) ≤ Valued.v (g : v.adicCompletion F) * 1 :=
              mul_le_mul' le_rfl hcv
          _ < 1 := by rw [mul_one]; exact adAd_val_lt g v hv
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hlt), map_one]
    have hy : ∀ v : HeightOneSpectrum (𝓞 F),
        (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) ∈ v.adicCompletionIntegers F := by
      intro v
      split_ifs with hv
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu v hv, inv_one]
      · exact zero_mem _
    refine ⟨adOfInt _ hy, adOfInt_int _ _, ?_⟩
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (if P v then (1 : v.adicCompletion F) else 0) * (1 + (g : FiniteAdeleRing (𝓞 F) F) v * c v) *
      (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) = if P v then 1 else 0
    rw [adAd_natCast_apply]
    split_ifs with hv
    · have hne : (1 + (g : v.adicCompletion F) * c v) ≠ 0 := by
        intro h0
        have := hu v hv
        rw [h0, map_zero] at this
        exact zero_ne_one this
      rw [one_mul, mul_inv_cancel₀ hne]
    · simp

end PI.UnitaryDimensionFormula

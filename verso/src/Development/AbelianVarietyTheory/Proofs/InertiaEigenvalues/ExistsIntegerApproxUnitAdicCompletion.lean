import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

noncomputable section

namespace GlobalTheory

open IsDedekindDomain.HeightOneSpectrum

/- English proof (translation)
Introduce `E' _ _ w' u hu`. Establish `hvF : ∀ z : E', Valued.v (algebraMap E' (w'.adicCompletion E') z) = w'.valuation E' z` using `fun z => valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' z`. Use `set x : w'.adicCompletion E' := (u : w'.adicCompletion E') with hxdef`. Establish `hx1 : Valued.v x ≤ 1`. Establish `: Valued.v x = 1` using `hu`.

Conclude with `this.le`. Establish `hopen : IsOpen {z : w'.adicCompletion E' | Valued.v (z - x) < 1}`. Establish `h1` using `Valued.isOpen_ball (w'.adicCompletion E') 1`. Establish `h2 : {z : w'.adicCompletion E' | Valued.v (z - x) < 1} = (fun z => z - x) ⁻¹' {w | Valued.v.restrict w < 1}`. Use extensionality with `z`.

Simplify using `[Valuation.restrict_lt_one_iff]`. Rewrite using `[h2]`. Conclude with `h1.preimage (continuous_id.sub continuous_const)`. Take `⟨k, hk⟩` from `(denseRange_algebraMap (R := 𝓞 E') (K := E') w').exists_mem_open hopen ⟨x, by simp⟩`. Simplify using `only [Set.mem_setOf_eq] at hk`.

Establish `hk1 : Valued.v (algebraMap E' (w'.adicCompletion E') k) ≤ 1`. Establish `: algebraMap E' (w'.adicCompletion E') k = (algebraMap E' (w'.adicCompletion E') k - x) + x` using `by ring`. Rewrite using `[this]`. Conclude with `Valuation.map_add_le _ hk.le hx1`. Establish `hk1' : w'.valuation E' k ≤ 1`.

Rewrite using `[← hvF]`. Conclude with `hk1`. Take `⟨a, ha⟩` from `exists_valuation_sub_lt_of_integer (K := E') w' hk1' 1`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `e1 : x - algebraMap E' (w'.adicCompletion E') (a : E') = (x - algebraMap E' (w'.adicCompletion E') k) + (algebraMap E' (w'.adicCompletion E') k - algebraMap E' (w'.adicCompletion E') (a : E'))`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[← Valuation.map_neg, neg_sub]`. Conclude with `hk`.

Rewrite using `[← map_sub, hvF]`. Establish `: w'.valuation E' ((a : E') - k) < 1` using `by simpa using ha`. Rewrite using `[← Valuation.map_neg, neg_sub]`. Conclude with `this`.
-/
theorem unit_completion_approx_integer : ∀ {E' : Type} [Field E'] [NumberField E'] (w' : HeightOneSpectrum (𝓞 E'))
    (u : (w'.adicCompletion E')ˣ) (hu : IsUnitAt w' u),
    ∃ x : 𝓞 E', Valued.v ((u : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  intro E' _ _ w' u hu
  have hvF : ∀ z : E', Valued.v (algebraMap E' (w'.adicCompletion E') z) = w'.valuation E' z :=
    fun z => valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' z
  set x : w'.adicCompletion E' := (u : w'.adicCompletion E') with hxdef
  have hx1 : Valued.v x ≤ 1 := by
    have : Valued.v x = 1 := hu
    exact this.le
  have hopen : IsOpen {z : w'.adicCompletion E' | Valued.v (z - x) < 1} := by
    have h1 := Valued.isOpen_ball (w'.adicCompletion E') 1
    have h2 : {z : w'.adicCompletion E' | Valued.v (z - x) < 1} =
        (fun z => z - x) ⁻¹' {w | Valued.v.restrict w < 1} := by
      ext z; simp [Valuation.restrict_lt_one_iff]
    rw [h2]
    exact h1.preimage (continuous_id.sub continuous_const)
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (R := 𝓞 E') (K := E') w').exists_mem_open hopen
    ⟨x, by simp⟩
  simp only [Set.mem_setOf_eq] at hk
  have hk1 : Valued.v (algebraMap E' (w'.adicCompletion E') k) ≤ 1 := by
    have : algebraMap E' (w'.adicCompletion E') k =
        (algebraMap E' (w'.adicCompletion E') k - x) + x := by ring
    rw [this]
    exact Valuation.map_add_le _ hk.le hx1
  have hk1' : w'.valuation E' k ≤ 1 := by
    rw [← hvF]; exact hk1
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer (K := E') w' hk1' 1
  refine ⟨a, ?_⟩
  have e1 : x - algebraMap E' (w'.adicCompletion E') (a : E') =
      (x - algebraMap E' (w'.adicCompletion E') k) +
      (algebraMap E' (w'.adicCompletion E') k - algebraMap E' (w'.adicCompletion E') (a : E')) := by
    ring
  rw [e1]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [← Valuation.map_neg, neg_sub]; exact hk
  · rw [← map_sub, hvF]
    have : w'.valuation E' ((a : E') - k) < 1 := by simpa using ha
    rw [← Valuation.map_neg, neg_sub]; exact this

end GlobalTheory

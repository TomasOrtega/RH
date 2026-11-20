import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `h2` using `Valued.tendsto_zero_pow_of_v_lt_one hy`. Establish `h3` using `(hj.tendsto 0).comp h2`. Rewrite `h3` using `[map_zero]`. Rewrite using `[← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]`. Use `h3.congr (fun n => ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
private theorem norm_lt_one_of_valuation_lt {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {p : ℕ} [Fact p.Prime]
    (j : w.adicCompletion F →+* Qbar p) (hj : Continuous j) (y : w.adicCompletion F) (hy : Valued.v y < 1) :
    ‖j y‖ < 1 := by
  have h2 := Valued.tendsto_zero_pow_of_v_lt_one hy
  have h3 := (hj.tendsto 0).comp h2
  rw [map_zero] at h3
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  refine h3.congr (fun n => ?_)
  simp

/- English proof (translation)
Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot`. Use `set t := algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a) with ht`. Establish `h1 : Valued.v t < 1`. Establish `: Valued.v t = w.valuation F (algebraMap (𝓞 F) F a)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _`. Rewrite using `[this]`.

Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha`. Establish `ht0 : t ≠ 0`. Rewrite using `[ht, map_ne_zero]`. Conclude with `fun h => ha0 (by simpa using h)`. Establish `hpos : 0 < ‖j t‖` using `norm_pos_iff.mpr ((map_ne_zero j).mpr ht0)`.

Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (‖j t‖⁻¹) hlt`. Establish `h4 : Valued.v (t * y ^ n) < 1`. Rewrite using `[map_mul, map_pow]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_one' hy n`. Use `_ < 1 := by rwa [mul_one]`. Establish `h5` using `norm_lt_one_of_valuation_lt j hj _ h4`. Rewrite `h5` using `[map_mul, map_pow, norm_mul, norm_pow]`.

Rewrite `hn` using `[inv_lt_iff_one_lt_mul₀' hpos]`. Conclude with `absurd (hn.trans h5) (lt_irrefl _)`.
-/
private theorem norm_le_one_of_valuation_le {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {p : ℕ} [Fact p.Prime]
    (j : w.adicCompletion F →+* Qbar p) (hj : Continuous j) (y : w.adicCompletion F) (hy : Valued.v y ≤ 1) :
    ‖j y‖ ≤ 1 := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  set t := algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a) with ht
  have h1 : Valued.v t < 1 := by
    have : Valued.v t = w.valuation F (algebraMap (𝓞 F) F a) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [this]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha
  have ht0 : t ≠ 0 := by
    rw [ht, map_ne_zero]
    exact fun h => ha0 (by simpa using h)
  have hpos : 0 < ‖j t‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr ht0)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖j t‖⁻¹) hlt
  have h4 : Valued.v (t * y ^ n) < 1 := by
    rw [map_mul, map_pow]
    calc Valued.v t * Valued.v y ^ n ≤ Valued.v t * 1 := by
          gcongr
          exact pow_le_one' hy n
      _ < 1 := by rwa [mul_one]
  have h5 := norm_lt_one_of_valuation_lt j hj _ h4
  rw [map_mul, map_pow, norm_mul, norm_pow] at h5
  rw [inv_lt_iff_one_lt_mul₀' hpos] at hn
  exact absurd (hn.trans h5) (lt_irrefl _)

/- English proof (translation)
Introduce `F _ _ w p _ ι M u h`. Establish `hv : Valued.v (u - 1) ≤ Valued.v (M : w.adicCompletion F)` using `((Valuation.Compatible.vle_iff_le (v := valuation (w.adicCompletion F)) _ _).mpr h :)`. Establish `hM1 : ‖(M : Qbar p)‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one _ M`. Establish `key : ∀ j : w.adicCompletion F →+* Qbar p, Continuous j → ‖j u - 1‖ ≤ ‖(M : Qbar p)‖`. Introduce `j hj`.

Distinguish the cases in `hM : (M : w.adicCompletion F) = 0`. Rewrite `hv` using `[hM, map_zero, le_zero_iff, map_eq_zero, sub_eq_zero]`. Simplify using `[hv]`. Establish `hx : Valued.v ((u - 1) / (M : w.adicCompletion F)) ≤ 1`. Rewrite using `[map_div₀]`.

Conclude with `div_le_one_of_le₀ hv zero_le`. Establish `h1` using `norm_le_one_of_valuation_le j hj _ hx`. Establish `hM' : (M : Qbar p) ≠ 0`. Rewrite using `[← map_natCast j]`. Conclude with `(map_ne_zero j).mpr hM`.

Rewrite `h1` using `[map_div₀, map_sub, map_one, map_natCast, norm_div, div_le_one (norm_pos_iff.mpr hM')]`. Conclude with `h1`. Unfold `GlobalTheory.HeckeGal.locPow`. Use `finprod_induction (fun z : Qbar p => ‖z - 1‖ ≤ ‖(M : Qbar p)‖) (by simp) ?_ ?_` and prove the remaining obligations. Introduce `x y hx hy`.

Establish `hx1 : ‖x‖ ≤ 1`. Use `IsUltrametricDist.norm_add_le_max (x - 1) 1` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one]`. Conclude with `this.trans (max_le (hx.trans hM1) le_rfl)`. Establish `e : x * y - 1 = x * (y - 1) + (x - 1)` using `by ring`.

Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hx1).trans hy`. Introduce `j`.

Rewrite using `[zpow_one]`. Conclude with `key j.1 j.2`.
-/
theorem UpperTheory.norm_locPow_sub_one_le_of_valuation_sub_one_le :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (M : ℕ)
    (u : w.adicCompletion F), valuation (w.adicCompletion F) (u - 1) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) →
    ‖GlobalTheory.HeckeGal.locPow ι (fun _ => 1) w u - 1‖ ≤ ‖(M : Qbar p)‖ := by
  intro F _ _ w p _ ι M u h
  have hv : Valued.v (u - 1) ≤ Valued.v (M : w.adicCompletion F) :=
    ((Valuation.Compatible.vle_iff_le (v := valuation (w.adicCompletion F)) _ _).mpr h :)
  have hM1 : ‖(M : Qbar p)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ M
  have key : ∀ j : w.adicCompletion F →+* Qbar p, Continuous j → ‖j u - 1‖ ≤ ‖(M : Qbar p)‖ := by
    intro j hj
    by_cases hM : (M : w.adicCompletion F) = 0
    · rw [hM, map_zero, le_zero_iff, map_eq_zero, sub_eq_zero] at hv
      simp [hv]
    · have hx : Valued.v ((u - 1) / (M : w.adicCompletion F)) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ hv zero_le
      have h1 := norm_le_one_of_valuation_le j hj _ hx
      have hM' : (M : Qbar p) ≠ 0 := by
        rw [← map_natCast j]
        exact (map_ne_zero j).mpr hM
      rw [map_div₀, map_sub, map_one, map_natCast, norm_div, div_le_one (norm_pos_iff.mpr hM')] at h1
      exact h1
  unfold GlobalTheory.HeckeGal.locPow
  refine finprod_induction (fun z : Qbar p => ‖z - 1‖ ≤ ‖(M : Qbar p)‖) (by simp) ?_ ?_
  · intro x y hx hy
    have hx1 : ‖x‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (x - 1) 1
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le (hx.trans hM1) le_rfl)
    have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hx1).trans hy
  · intro j
    rw [zpow_one]
    exact key j.1 j.2

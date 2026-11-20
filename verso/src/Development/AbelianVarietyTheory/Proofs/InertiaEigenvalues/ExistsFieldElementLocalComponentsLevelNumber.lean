import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelFieldApprox

open Formalism.L2.Host

/- English proof (translation)
Establish `e : y = (y - 1) + 1` using `by ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])]`. Conclude with `map_one _`.
-/
theorem val_eq_one_of_close {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} {y : E}
    (h : v.valuation E (y - 1) < 1) : v.valuation E y = 1 := by
  have e : y = (y - 1) + 1 := by ring
  rw [e, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])]
  exact map_one _

/- English proof (translation)
Establish `hlt : v.valuation E ((y : E) - 1) < 1` using `lt_of_le_of_lt h (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)`. Establish `hv` using `val_eq_one_of_close hlt`. Establish `e1 : ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (y : E)` using `rfl`. Establish `hval : ∀ x : E, Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x` using `fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x`. Use `⟨?_, hv⟩` and prove the remaining obligations.

Use `show χ.loc v (atFin v y) = 1`. Use `hn _ ?_ ?_` and prove the remaining obligations. Use `show Valued.v ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1`. Rewrite using `[e1, hval, hv]`. Rewrite using `[e1, ← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, hval]`.

Conclude with `h.trans (WithZero.exp_le_exp.mpr (by omega))`.
-/
theorem locK_eq_one {E : Type} [Field E] [NumberField E] (χ : HChar E) (v : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (hn : χ.LevelLe v n) (y : Eˣ) (h : v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) :
    χ.locK v y = 1 ∧ v.valuation E (y : E) = 1 := by
  have hlt : v.valuation E ((y : E) - 1) < 1 :=
    lt_of_le_of_lt h (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hv := val_eq_one_of_close hlt
  have e1 : ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (y : E) := rfl
  have hval : ∀ x : E, Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  refine ⟨?_, hv⟩
  show χ.loc v (atFin v y) = 1
  refine hn _ ?_ ?_
  · show Valued.v ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
    rw [e1, hval, hv]
  · rw [e1, ← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, hval]
    exact h.trans (WithZero.exp_le_exp.mpr (by omega))

/- English proof (translation)
Introduce `E _ _ χ M₀ u hu T`. Establish `hM0 : M₀ ≠ 0`. Introduce and unpack `rfl`. Conclude with `u.ne_zero (by rw [hu]; simp)`. Establish `hM : ((M₀ : ℕ) : 𝓞 E) ≠ 0` using `by exact_mod_cast hM0`.

Establish `hMe : ((M₀ : ℕ) : E) ≠ 0` using `by exact_mod_cast hM0`. Establish `hfin : {v : HeightOneSpectrum (𝓞 E) | ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite`. Use `(Ideal.finite_factors (I := Ideal.span {((M₀ : ℕ) : 𝓞 E)}) ?_).subset fun v hv => ?_` and prove the remaining obligations. Rewrite using `[ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Conclude with `Ideal.dvd_span_singleton.2 hv`.

Use `set S : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hfin.toFinset with hS`. Use `choose n hn using GlobalTheory.Mem.UnrAe.exists_levelLe χ`. Establish `hm : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, v.intValuation ((M₀ : ℕ) : 𝓞 E) = WithZero.exp (-(m : ℤ))` using `fun v => ⟨_, v.intValuation_if_neg hM⟩`. Use `choose m hm using hm`. Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun v => if v ∈ T then m v + n v + 1 else n v + 1) (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if (v : HeightOneSpectrum (𝓞 E)) ∈ T then ((M₀ : ℕ) : 𝓞 E) else 1)`.

Establish `hvz : ∀ v : HeightOneSpectrum (𝓞 E), ∀ z : 𝓞 E, v.valuation E (z : E) = v.intValuation z` using `fun v z => HeightOneSpectrum.valuation_of_algebraMap (K := E) v z`. Establish `hT : ∀ v ∈ T, v.valuation E ((y : E) - ((M₀ : ℕ) : E)) ≤ WithZero.exp (-((m v : ℤ) + n v + 1))`. Introduce `v hv`. Establish `h1` using `(v.intValuation_le_pow_iff_mem _ _).2 (hy v (Finset.mem_union_left _ hv))`. Simplify using `only [hv, if_true] at h1`.

Establish `e : (y : E) - ((M₀ : ℕ) : E) = ((y - ((M₀ : ℕ) : 𝓞 E) : 𝓞 E) : E)` using `by push_cast; rfl`. Rewrite using `[e, hvz]`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hO : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n v : ℤ) + 1))`. Introduce `v hv hvT`. Establish `h1` using `(v.intValuation_le_pow_iff_mem _ _).2 (hy v (Finset.mem_union_right _ (hfin.mem_toFinset.2 hv)))`. Simplify using `only [hvT, if_false] at h1`. Establish `e : (y : E) - 1 = ((y - 1 : 𝓞 E) : E)` using `by push_cast; rfl`.

Rewrite using `[e, hvz]`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hMv : ∀ v, v.valuation E ((M₀ : ℕ) : E) = WithZero.exp (-(m v : ℤ))`.

Introduce `v`. Rewrite using `[← hm v, ← hvz]`. Simplify using the standard rewrite rules. Establish `hTv : ∀ v ∈ T, v.valuation E (y : E) = v.valuation E ((M₀ : ℕ) : E)`. Introduce `v hv`.

Establish `e : (y : E) = ((y : E) - ((M₀ : ℕ) : E)) + ((M₀ : ℕ) : E)` using `by ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_right]`. Rewrite using `[hMv]`. Conclude with `lt_of_le_of_lt (hT v hv) (WithZero.exp_lt_exp.mpr (by omega))`. Establish `hOv : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → v.valuation E (y : E) = 1` using `fun v hv hvT => val_eq_one_of_close (lt_of_le_of_lt (hO v hv hvT) (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))`.

Distinguish the cases in `hy0 : (y : E) = 0`. Use `⟨1, by simpa using isIntegral_one, fun v hv => ?_, fun v hv hvT => ?_⟩` and prove the remaining obligations. Conclude with `absurd (hTv v hv) (by rw [hy0, map_zero, hMv]; exact (WithZero.exp_ne_zero).symm)`. Conclude with `absurd (hOv v hv hvT) (by rw [hy0, map_zero]; exact zero_ne_one)`. Use `set a : Eˣ := Units.mk0 (y : E) hy0 with ha`.

Use `⟨a, y.isIntegral_coe, fun v hv => ?_, fun v hv hvT => ?_⟩` and prove the remaining obligations. Establish `hw` using `(locK_eq_one χ v (hn v) (a * u⁻¹) ?_).1`. Use `⟨?_, hTv v hv⟩` and prove the remaining obligations. Establish `: a = (a * u⁻¹) * u` using `by group`. Rewrite using `[this, map_mul, hw, one_mul]`.

Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, hu, ha, Units.val_mk0]`. Establish `e : (y : E) * ((M₀ : ℕ) : E)⁻¹ - 1 = ((y : E) - ((M₀ : ℕ) : E)) / ((M₀ : ℕ) : E)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, map_div₀, hMv]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `locK_eq_one χ v (hn v) a (by rw [ha, Units.val_mk0]; exact hO v hv hvT)`.
-/
theorem exists_approx : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ : ℕ) (u : Eˣ), (u : E) = ((M₀ : ℕ) : E) → ∀ (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ a : Eˣ, IsIntegral ℤ (a : E) ∧ (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) ∧ ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1 := by
  intro E _ _ χ M₀ u hu T
  classical
  have hM0 : M₀ ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hu]; simp)
  have hM : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hM0
  have hMe : ((M₀ : ℕ) : E) ≠ 0 := by exact_mod_cast hM0
  have hfin : {v : HeightOneSpectrum (𝓞 E) | ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((M₀ : ℕ) : 𝓞 E)}) ?_).subset fun v hv => ?_
    · rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_span_singleton.2 hv
  set S : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hfin.toFinset with hS
  choose n hn using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  have hm : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, v.intValuation ((M₀ : ℕ) : 𝓞 E) = WithZero.exp (-(m : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg hM⟩
  choose m hm using hm
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => if v ∈ T then m v + n v + 1 else n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h'))
    (fun v => if (v : HeightOneSpectrum (𝓞 E)) ∈ T then ((M₀ : ℕ) : 𝓞 E) else 1)
  have hvz : ∀ v : HeightOneSpectrum (𝓞 E), ∀ z : 𝓞 E, v.valuation E (z : E) = v.intValuation z :=
    fun v z => HeightOneSpectrum.valuation_of_algebraMap (K := E) v z
  have hT : ∀ v ∈ T, v.valuation E ((y : E) - ((M₀ : ℕ) : E)) ≤ WithZero.exp (-((m v : ℤ) + n v + 1)) := by
    intro v hv
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v (Finset.mem_union_left _ hv))
    simp only [hv, if_true] at h1
    have e : (y : E) - ((M₀ : ℕ) : E) = ((y - ((M₀ : ℕ) : 𝓞 E) : 𝓞 E) : E) := by push_cast; rfl
    rw [e, hvz]
    convert h1 using 2
    push_cast; ring
  have hO : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T →
      v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n v : ℤ) + 1)) := by
    intro v hv hvT
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2
      (hy v (Finset.mem_union_right _ (hfin.mem_toFinset.2 hv)))
    simp only [hvT, if_false] at h1
    have e : (y : E) - 1 = ((y - 1 : 𝓞 E) : E) := by push_cast; rfl
    rw [e, hvz]
    convert h1 using 2
    push_cast; ring
  have hMv : ∀ v, v.valuation E ((M₀ : ℕ) : E) = WithZero.exp (-(m v : ℤ)) := by
    intro v
    rw [← hm v, ← hvz]; simp
  have hTv : ∀ v ∈ T, v.valuation E (y : E) = v.valuation E ((M₀ : ℕ) : E) := by
    intro v hv
    have e : (y : E) = ((y : E) - ((M₀ : ℕ) : E)) + ((M₀ : ℕ) : E) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    rw [hMv]
    exact lt_of_le_of_lt (hT v hv) (WithZero.exp_lt_exp.mpr (by omega))
  have hOv : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → v.valuation E (y : E) = 1 :=
    fun v hv hvT => val_eq_one_of_close (lt_of_le_of_lt (hO v hv hvT)
      (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))
  by_cases hy0 : (y : E) = 0
  · refine ⟨1, by simpa using isIntegral_one, fun v hv => ?_, fun v hv hvT => ?_⟩
    · exact absurd (hTv v hv) (by rw [hy0, map_zero, hMv]; exact (WithZero.exp_ne_zero).symm)
    · exact absurd (hOv v hv hvT) (by rw [hy0, map_zero]; exact zero_ne_one)
  set a : Eˣ := Units.mk0 (y : E) hy0 with ha
  refine ⟨a, y.isIntegral_coe, fun v hv => ?_, fun v hv hvT => ?_⟩
  · have hw := (locK_eq_one χ v (hn v) (a * u⁻¹) ?_).1
    · refine ⟨?_, hTv v hv⟩
      have : a = (a * u⁻¹) * u := by group
      rw [this, map_mul, hw, one_mul]
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, hu, ha, Units.val_mk0]
      have e : (y : E) * ((M₀ : ℕ) : E)⁻¹ - 1 = ((y : E) - ((M₀ : ℕ) : E)) / ((M₀ : ℕ) : E) := by
        field_simp
      rw [e, map_div₀, hMv]
      calc _ ≤ WithZero.exp (-((m v : ℤ) + n v + 1)) / WithZero.exp (-(m v : ℤ)) :=
            div_le_div_of_nonneg_right (hT v hv) zero_le'
        _ = _ := by rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; ring
  · exact locK_eq_one χ v (hn v) a (by rw [ha, Units.val_mk0]; exact hO v hv hvT)

end GlobalTheory.LevelFieldApprox

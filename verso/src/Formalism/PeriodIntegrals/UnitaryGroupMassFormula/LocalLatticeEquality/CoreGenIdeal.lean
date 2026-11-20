import Mathlib
import Formalism.PeriodIntegrals.LocLatEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Development

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Distinguish the cases in `h𝔞 : 𝔞 = ⊥`. Use `⟨0, 𝔞.zero_mem, fun b hb => ⟨1, ?_, 0, ?_⟩⟩` and prove the remaining obligations. Conclude with `fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)`. Rewrite `hb` using `[h𝔞, Ideal.mem_bot]`. Simplify using `[hb]`.

Establish `h𝔞0 : 𝔞 ≠ 0` using `h𝔞`. Establish `hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E))` using `FaithfulSMul.algebraMap_injective _ _`. Establish `hpE0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hinj]`. Conclude with `p.ne_bot`.

Establish `hle : 𝔞 * Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≤ 𝔞` using `Ideal.mul_le_inf.trans inf_le_left`. Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq hle (mul_ne_zero h𝔞0 hpE0)`. Establish `haa : a ∈ 𝔞` using `ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)`. Take `⟨𝔠, h𝔠⟩ : 𝔞 ∣ Ideal.span {a}` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haa)`. Establish `hav : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ¬ 𝔠 ≤ P.asIdeal`.

Introduce `P hP hcP`. Establish `h1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≤ P.asIdeal` using `Ideal.map_le_iff_le_comap.mpr hP.ge`. Establish `h2 : 𝔞 ≤ 𝔞 * P.asIdeal` using `by conv_lhs => rw [← ha]`. Use `sup_le (Ideal.mul_mono_right h1) ?_` and prove the remaining obligations. Rewrite using `[h𝔠]`.

Conclude with `Ideal.mul_mono_right hcP`. Establish `h3 : 𝔞 * P.asIdeal ∣ 𝔞 * 1`. Rewrite using `[mul_one]`. Conclude with `Ideal.dvd_iff_le.mpr h2`. Establish `h4` using `(mul_dvd_mul_iff_left h𝔞0).mp h3`.

Conclude with `P.isPrime.ne_top (Ideal.isUnit_iff.mp (isUnit_of_dvd_one h4))`. Take `⟨d, hdp, hd⟩` from `hA F E p 𝔠 hav`. Use `⟨a, haa, fun b hb => ⟨d, hdp, ?_⟩⟩` and prove the remaining obligations. Establish `hmem : algebraMap (𝓞 F) (𝓞 E) d * b ∈ Ideal.span {a}`. Rewrite using `[h𝔠, mul_comm (algebraMap (𝓞 F) (𝓞 E) d) b]`.

Conclude with `Ideal.mul_mem_mul hb hd`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.mp hmem`. Conclude with `⟨r, hr.symm⟩`.
-/
theorem core_gen_ideal (hA : AvoidP) (p : HeightOneSpectrum (𝓞 F)) (𝔞 : Ideal (𝓞 E)) :
    ∃ a ∈ 𝔞, ∀ b ∈ 𝔞, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ r : 𝓞 E,
      algebraMap (𝓞 F) (𝓞 E) d * b = r * a := by
  classical
  by_cases h𝔞 : 𝔞 = ⊥
  · refine ⟨0, 𝔞.zero_mem, fun b hb => ⟨1, ?_, 0, ?_⟩⟩
    · exact fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    · rw [h𝔞, Ideal.mem_bot] at hb
      simp [hb]
  have h𝔞0 : 𝔞 ≠ 0 := h𝔞
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hpE0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hinj]
    exact p.ne_bot
  have hle : 𝔞 * Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≤ 𝔞 :=
    Ideal.mul_le_inf.trans inf_le_left
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle (mul_ne_zero h𝔞0 hpE0)
  have haa : a ∈ 𝔞 := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨𝔠, h𝔠⟩ : 𝔞 ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haa)
  have hav : ∀ P : HeightOneSpectrum (𝓞 E),
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ¬ 𝔠 ≤ P.asIdeal := by
    intro P hP hcP
    have h1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal ≤ P.asIdeal :=
      Ideal.map_le_iff_le_comap.mpr hP.ge
    have h2 : 𝔞 ≤ 𝔞 * P.asIdeal := by
      conv_lhs => rw [← ha]
      refine sup_le (Ideal.mul_mono_right h1) ?_
      rw [h𝔠]
      exact Ideal.mul_mono_right hcP
    have h3 : 𝔞 * P.asIdeal ∣ 𝔞 * 1 := by
      rw [mul_one]
      exact Ideal.dvd_iff_le.mpr h2
    have h4 := (mul_dvd_mul_iff_left h𝔞0).mp h3
    exact P.isPrime.ne_top (Ideal.isUnit_iff.mp (isUnit_of_dvd_one h4))
  obtain ⟨d, hdp, hd⟩ := hA F E p 𝔠 hav
  refine ⟨a, haa, fun b hb => ⟨d, hdp, ?_⟩⟩
  have hmem : algebraMap (𝓞 F) (𝓞 E) d * b ∈ Ideal.span {a} := by
    rw [h𝔠, mul_comm (algebraMap (𝓞 F) (𝓞 E) d) b]
    exact Ideal.mul_mem_mul hb hd
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨r, hr.symm⟩

/- English proof (translation)
Take `⟨S, rfl⟩` from `hI`. Take `⟨c, hc⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) S`. Establish `hc0 : algebraMap (𝓞 E) E (c : 𝓞 E) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr (nonZeroDivisors.coe_ne_zero c)`. Establish `hint : ∀ x ∈ Submodule.span (𝓞 E) (S : Set E), ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (c : 𝓞 E) • x`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy⟩` from `hc x hx`. Conclude with `⟨y, hy⟩`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add x z _ _ hx hz`. Take `⟨y1, h1⟩` from `hx`. Take `⟨y2, h2⟩` from `hz`. Conclude with `⟨y1 + y2, by rw [map_add, h1, h2, smul_add]⟩`. Consider the case `smul r x _ hx`.

Take `⟨y, h⟩` from `hx`. Use `⟨r * y, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, h]`. Simplify using `only [Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨a0, ha0, hgen⟩` from `core_gen_ideal (F := F) hA p ((Submodule.span (𝓞 E) (S : Set E)).comap (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹))`. Rewrite `ha0` using `[Submodule.mem_comap, LinearMap.toSpanSingleton_apply]`. Use `⟨a0 • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹, ha0, fun b hb => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hint b hb`. Establish `hyb : y • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹ = b`.

Rewrite using `[Algebra.smul_def, hy, Algebra.smul_def, mul_comm, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]`. Establish `hy𝔞 : y ∈ (Submodule.span (𝓞 E) (S : Set E)).comap (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹)`. Rewrite using `[Submodule.mem_comap, LinearMap.toSpanSingleton_apply, hyb]`. Conclude with `hb`. Take `⟨d, hd, r, hr⟩` from `hgen y hy𝔞`.

Use `⟨d, hd, r, ?_⟩` and prove the remaining obligations. Rewrite using `[← hyb, smul_smul, smul_smul, hr]`.
-/
theorem core_gen (hA : AvoidP) (p : HeightOneSpectrum (𝓞 F)) (I : Submodule (𝓞 E) E)
    (hI : I.FG) : ∃ a ∈ I, ∀ b ∈ I, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ r : 𝓞 E,
      algebraMap (𝓞 F) (𝓞 E) d • b = r • a := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) S
  have hc0 : algebraMap (𝓞 E) E (c : 𝓞 E) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr (nonZeroDivisors.coe_ne_zero c)
  have hint : ∀ x ∈ Submodule.span (𝓞 E) (S : Set E),
      ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (c : 𝓞 E) • x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy⟩ := hc x hx
      exact ⟨y, hy⟩
    | zero => exact ⟨0, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨y1, h1⟩ := hx
      obtain ⟨y2, h2⟩ := hz
      exact ⟨y1 + y2, by rw [map_add, h1, h2, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨y, h⟩ := hx
      refine ⟨r * y, ?_⟩
      rw [map_mul, h]
      simp only [Algebra.smul_def]
      ring
  obtain ⟨a0, ha0, hgen⟩ := core_gen_ideal (F := F) hA p
    ((Submodule.span (𝓞 E) (S : Set E)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹))
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply] at ha0
  refine ⟨a0 • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹, ha0, fun b hb => ?_⟩
  obtain ⟨y, hy⟩ := hint b hb
  have hyb : y • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹ = b := by
    rw [Algebra.smul_def, hy, Algebra.smul_def, mul_comm, ← mul_assoc, inv_mul_cancel₀ hc0,
      one_mul]
  have hy𝔞 : y ∈ (Submodule.span (𝓞 E) (S : Set E)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹) := by
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, hyb]
    exact hb
  obtain ⟨d, hd, r, hr⟩ := hgen y hy𝔞
  refine ⟨d, hd, r, ?_⟩
  rw [← hyb, smul_smul, smul_smul, hr]

end PI.LocLatEq.W

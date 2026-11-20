import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.EntriesLat

noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Topology Filter

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _`.
-/
theorem isOpen_intAd (F : Type) [Field F] [NumberField F] :
    IsOpen ((Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))) :=
  RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _

/- English proof (translation)
Introduce `F _ _ N hN`. Establish `hNF : (N : F) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `hu : IsUnit (N : FiniteAdeleRing (𝓞 F) F)`. Establish `: (N : FiniteAdeleRing (𝓞 F) F) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `(IsUnit.mk0 _ hNF).map _`. Take `⟨u, hu⟩` from `hu`. Establish `hcont : Continuous (fun a : FiniteAdeleRing (𝓞 F) F => ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * a)` using `continuous_const.mul continuous_id`. Use `Filter.mem_of_superset (((isOpen_intAd F).preimage hcont).mem_nhds ?_) ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, mul_zero, SetLike.mem_coe]`. Conclude with `zero_mem _`. Introduce `a ha`. Use `⟨_, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu, ← mul_assoc, Units.mul_inv, one_mul]`.
-/
theorem finite_neighbourhood_first : FinNhdA := by
  intro F _ _ N hN
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hu : IsUnit (N : FiniteAdeleRing (𝓞 F) F) := by
    have : (N : FiniteAdeleRing (𝓞 F) F) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F) := by
      simp
    rw [this]
    exact (IsUnit.mk0 _ hNF).map _
  obtain ⟨u, hu⟩ := hu
  have hcont : Continuous (fun a : FiniteAdeleRing (𝓞 F) F => ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) * a) := continuous_const.mul continuous_id
  refine Filter.mem_of_superset (((isOpen_intAd F).preimage hcont).mem_nhds ?_) ?_
  · simp only [Set.mem_preimage, mul_zero, SetLike.mem_coe]
    exact zero_mem _
  · intro a ha
    refine ⟨_, ha, ?_⟩
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Rewrite using `[Nat.cast_zero, Nat.cast_zero]`. Both sides reduce to the same expression. Consider the case `succ n ih`.

Rewrite using `[Nat.cast_succ, Nat.cast_succ, ← ih]`. Both sides reduce to the same expression.
-/
theorem natCast_apply (F : Type) [Field F] [NumberField F] (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (N : FiniteAdeleRing (𝓞 F) F) v = (N : v.adicCompletion F) := by
  induction N with
  | zero =>
    rw [Nat.cast_zero, Nat.cast_zero]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← ih]
    rfl

/- English proof (translation)
Rewrite using `[← natCast_apply F N v]`. Both sides reduce to the same expression.
-/
theorem natCast_mul_apply (F : Type) [Field F] [NumberField F] (N : ℕ)
    (z : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((N : FiniteAdeleRing (𝓞 F) F) * z) v = (N : v.adicCompletion F) * z v := by
  rw [← natCast_apply F N v]
  rfl

/- English proof (translation)
Establish `hmem : (c : 𝓞 F) ∈ v.asIdeal`. Take `⟨k, hk⟩` from `hc`. Rewrite using `[hk, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)`. Establish `hval` using `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (c : 𝓞 F)).2 hmem`.

Rewrite using `[Valued.toNormedField.norm_lt_one_iff]`. Establish `e : (c : v.adicCompletion F) = (((algebraMap (𝓞 F) F (c : 𝓞 F)) : F) : v.adicCompletion F)`. Rewrite using `[map_natCast]`. Rewrite using `[show (((c : F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (c : F) from rfl, map_natCast]`. Rewrite using `[e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.

Conclude with `hval`.
-/
theorem norm_natCast_lt_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) : ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e : (c : v.adicCompletion F) = (((algebraMap (𝓞 F) F (c : 𝓞 F)) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    rw [show (((c : F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (c : F) from rfl,
      map_natCast]
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hval

/- English proof (translation)
Introduce `F _ _ U hU`. Establish `hAopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))` using `fun _ => Valued.isOpen_valuationSubring _`. Establish `hU' : U ∈ Filter.map (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) (𝓝 (fun v => ⟨0, zero_mem (v.adicCompletionIntegers F)⟩))`. Rewrite using `[← RestrictedProduct.nhds_eq_map_structureMap hAopen]`. Conclude with `hU`.

Establish `hU2 : (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) ⁻¹' (U : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicComp …` using `hU'`. Rewrite `hU2` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, t, ht, hIt⟩` from `hU2`. Establish `hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > (0 : ℝ), ∀ y : (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ‖(y : v.adicCompletion F)‖ < ε → y ∈ t v`. Introduce `v`.

Take `⟨u, hu, hut⟩` from `(mem_nhds_subtype _ _ _).1 (ht v)`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hu`. Use `⟨ε, hε, fun y hy => hut (hball ?_)⟩` and prove the remaining obligations. Simplify `hy` using `[Metric.mem_ball, dist_zero_right]`. Use `choose ε hεpos hεt using hε`.

Use `set c : ℕ := ∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal with hcdef`. Establish `hc0 : c ≠ 0`. Rewrite using `[hcdef, Finset.prod_ne_zero_iff]`. Introduce `v _`. Conclude with `(lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'`.

Establish `hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1` using `fun v hv => norm_natCast_lt_one F v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))`. Establish `hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v` using `fun v hv => (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually (Iio_mem_nhds (hεpos v))`. Take `⟨k, hk⟩` from `((Filter.eventually_all_finite hI).2 hev).exists`. Use `⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun z hz => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ v, (((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))`.

Introduce `v`. Rewrite using `[natCast_mul_apply]`. Conclude with `mul_mem (natCast_mem _ _) (hz v)`. Establish `hx : ((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z = RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite (fun v => ⟨_, hmem v⟩)`. Use extensionality with `v`.

Both sides reduce to the same expression. Rewrite using `[hx]`. Apply `hIt` to reduce the goal to its premises. Introduce `v hv`. Apply `hεt` to reduce the goal to its premises.

Use `show ‖(((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v‖ < ε v`. Rewrite using `[natCast_mul_apply, norm_mul, Nat.cast_pow, norm_pow]`. Establish `hz1 : ‖z v‖ ≤ 1`. Rewrite using `[Valued.toNormedField.norm_le_one_iff]`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem finite_neighbourhood_second : FinNhdB := by
  intro F _ _ U hU
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun _ => Valued.isOpen_valuationSubring _
  have hU' : U ∈ Filter.map (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
      (𝓝 (fun v => ⟨0, zero_mem (v.adicCompletionIntegers F)⟩)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hAopen]
    exact hU
  have hU2 : (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) ⁻¹'
      (U : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)) ∈
      𝓝 (fun v : HeightOneSpectrum (𝓞 F) => (⟨0, zero_mem (v.adicCompletionIntegers F)⟩ :
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := hU'
  rw [nhds_pi, Filter.mem_pi] at hU2
  obtain ⟨I, hI, t, ht, hIt⟩ := hU2
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > (0 : ℝ),
      ∀ y : (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        ‖(y : v.adicCompletion F)‖ < ε → y ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨ε, hε, fun y hy => hut (hball ?_)⟩
    simpa [Metric.mem_ball, dist_zero_right] using hy
  choose ε hεpos hεt using hε
  set c : ℕ := ∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one F v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))
  have hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v := fun v hv =>
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually
      (Iio_mem_nhds (hεpos v))
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hI).2 hev).exists
  refine ⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun z hz => ?_⟩
  have hmem : ∀ v, (((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v ∈
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    rw [natCast_mul_apply]
    exact mul_mem (natCast_mem _ _) (hz v)
  have hx : ((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z = RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
      (fun v => ⟨_, hmem v⟩) := by
    ext v
    rfl
  rw [hx]
  apply hIt
  intro v hv
  apply hεt
  show ‖(((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v‖ < ε v
  rw [natCast_mul_apply, norm_mul, Nat.cast_pow, norm_pow]
  have hz1 : ‖z v‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v)
  calc ‖(c : v.adicCompletion F)‖ ^ k * ‖z v‖ ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 :=
        mul_le_mul_of_nonneg_left hz1 (pow_nonneg (norm_nonneg _) _)
    _ < ε v := by rw [mul_one]; exact hk v hv

end PI.InvTopW

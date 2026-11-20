import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableAbsNormRpowInv

open Topology Filter NumberField IsDedekindDomain WithZero FractionalIdeal Function Ideal
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

section Factored

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext (associated_iff_eq.1 ((HeightOneSpectrum.prime w).associated_of_dvd (HeightOneSpectrum.prime v) h))`.
-/
theorem heightOneSpectrum_eq_of_dvd {v w : HeightOneSpectrum R} (h : w.asIdeal ∣ v.asIdeal) :
    w = v :=
  HeightOneSpectrum.ext (associated_iff_eq.1
    ((HeightOneSpectrum.prime w).associated_of_dvd (HeightOneSpectrum.prime v) h))

/- English proof (translation)
The claim follows from `heightOneSpectrum_eq_of_dvd ((HeightOneSpectrum.prime w).dvd_of_dvd_pow h)`.
-/
theorem heightOneSpectrum_eq_of_dvd_pow {v w : HeightOneSpectrum R} {k : ℕ}
    (h : w.asIdeal ∣ v.asIdeal ^ k) : w = v :=
  heightOneSpectrum_eq_of_dvd ((HeightOneSpectrum.prime w).dvd_of_dvd_pow h)

/- English proof (translation)
Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I h1`. Establish `hM0 : M ≠ ⊥` using `fun h ↦ h0 (le_bot_iff.1 (h ▸ hIM))`. Conclude with `⟨⟨M, hM.isPrime, hM0⟩, Ideal.dvd_iff_le.2 hIM⟩`.
-/
theorem exists_heightOneSpectrum_dvd {I : Ideal R} (h0 : I ≠ ⊥) (h1 : I ≠ ⊤) :
    ∃ v : HeightOneSpectrum R, v.asIdeal ∣ I := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I h1
  have hM0 : M ≠ ⊥ := fun h ↦ h0 (le_bot_iff.1 (h ▸ hIM))
  exact ⟨⟨M, hM.isPrime, hM0⟩, Ideal.dvd_iff_le.2 hIM⟩

def factoredIdeals (S : Finset (HeightOneSpectrum R)) : Set (Ideal R) :=
  {I | I ≠ ⊥ ∧ ∀ v : HeightOneSpectrum R, v.asIdeal ∣ I → v ∈ S}

/- English proof (translation)
Use extensionality with `I`. Simplify using `only [factoredIdeals, Set.mem_ofPred_eq, Finset.notMem_empty, imp_false, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h⟩`. Assume the negation of the conclusion as `h1`.

Take `⟨v, hv⟩` from `exists_heightOneSpectrum_dvd h0 h1`. Conclude with `h v hv`. Introduce and unpack `rfl`. Conclude with `⟨top_ne_bot, fun v hv ↦ v.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hv))⟩`.
-/
theorem factoredIdeals_empty : factoredIdeals (∅ : Finset (HeightOneSpectrum R)) = {⊤} := by
  ext I
  simp only [factoredIdeals, Set.mem_ofPred_eq, Finset.notMem_empty, imp_false,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, h⟩
    by_contra h1
    obtain ⟨v, hv⟩ := exists_heightOneSpectrum_dvd h0 h1
    exact h v hv
  · rintro rfl
    exact ⟨top_ne_bot, fun v hv ↦ v.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hv))⟩

/- English proof (translation)
Use `⟨?_, fun w hw ↦ ?_⟩` and prove the remaining obligations. Establish `hv0 : v.asIdeal ≠ 0` using `by simpa [Submodule.zero_eq_bot] using v.ne_bot`. Rewrite using `[Ne, Ideal.mul_eq_bot, not_or]`. Conclude with `⟨by simpa [Submodule.zero_eq_bot] using pow_ne_zero k hv0, hI.1⟩`. Break down `(HeightOneSpectrum.prime w).dvd_or_dvd hw with h | h` into its components or cases.

Rewrite using `[heightOneSpectrum_eq_of_dvd_pow h]`. Conclude with `Finset.mem_insert_self _ _`. Conclude with `Finset.mem_insert_of_mem (hI.2 w h)`.
-/
theorem pow_mul_mem_factoredIdeals_insert [DecidableEq (HeightOneSpectrum R)]
    {S : Finset (HeightOneSpectrum R)}
    {v : HeightOneSpectrum R} {I : Ideal R} (hI : I ∈ factoredIdeals S) (k : ℕ) :
    v.asIdeal ^ k * I ∈ factoredIdeals (insert v S) := by
  refine ⟨?_, fun w hw ↦ ?_⟩
  · have hv0 : v.asIdeal ≠ 0 := by simpa [Submodule.zero_eq_bot] using v.ne_bot
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨by simpa [Submodule.zero_eq_bot] using pow_ne_zero k hv0, hI.1⟩
  · rcases (HeightOneSpectrum.prime w).dvd_or_dvd hw with h | h
    · rw [heightOneSpectrum_eq_of_dvd_pow h]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hI.2 w h)

/- English proof (translation)
Establish `hv0 : v.asIdeal ≠ 0` using `by simpa [Submodule.zero_eq_bot] using v.ne_bot`. Establish `hp0 : ∀ n : ℕ, v.asIdeal ^ n ≠ 0` using `fun n ↦ pow_ne_zero n hv0`. Break down `lt_trichotomy k j with hkj | rfl | hkj` into its components or cases. It suffices to derive a contradiction. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hkj`.

Rewrite `h` using `[add_assoc, pow_add, mul_assoc]`. Establish `h'` using `mul_left_cancel₀ (hp0 k) h`. Conclude with `hI (h' ▸ Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero d)) J)`. Conclude with `⟨rfl, mul_left_cancel₀ (hp0 k) h⟩`. It suffices to derive a contradiction.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hkj`. Rewrite `h` using `[add_assoc, pow_add, mul_assoc]`. Establish `h'` using `mul_left_cancel₀ (hp0 j) h.symm`. Conclude with `hJ (h' ▸ Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero d)) I)`.
-/
theorem pow_mul_inj {v : HeightOneSpectrum R} {k j : ℕ} {I J : Ideal R}
    (hI : ¬ v.asIdeal ∣ I) (hJ : ¬ v.asIdeal ∣ J) (h : v.asIdeal ^ k * I = v.asIdeal ^ j * J) :
    k = j ∧ I = J := by
  have hv0 : v.asIdeal ≠ 0 := by simpa [Submodule.zero_eq_bot] using v.ne_bot
  have hp0 : ∀ n : ℕ, v.asIdeal ^ n ≠ 0 := fun n ↦ pow_ne_zero n hv0
  rcases lt_trichotomy k j with hkj | rfl | hkj
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkj
    rw [add_assoc, pow_add, mul_assoc] at h
    have h' := mul_left_cancel₀ (hp0 k) h
    exact hI (h' ▸ Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero d)) J)
  · exact ⟨rfl, mul_left_cancel₀ (hp0 k) h⟩
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkj
    rw [add_assoc, pow_add, mul_assoc] at h
    have h' := mul_left_cancel₀ (hp0 j) h.symm
    exact hJ (h' ▸ Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero d)) I)

/- English proof (translation)
Establish `hI0 : I ≠ 0` using `by simpa [Submodule.zero_eq_bot] using hI.1`. Establish `hfin : FiniteMultiplicity v.asIdeal I` using `FiniteMultiplicity.of_not_isUnit (fun h ↦ v.isPrime.ne_top (Ideal.isUnit_iff.1 h)) hI0`. Take `⟨J, hJ⟩` from `pow_multiplicity_dvd v.asIdeal I`. Use `⟨multiplicity v.asIdeal I, J, ⟨?_, fun w hw ↦ ?_⟩, hJ⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Rewrite `hJ` using `[Ideal.mul_bot]`. Conclude with `hI.1 hJ`. Establish `hwI : w.asIdeal ∣ I`. Rewrite using `[hJ]`. Conclude with `dvd_mul_of_dvd_right hw _`.

Break down `Finset.mem_insert.1 (hI.2 w hwI) with rfl | hw'` into its components or cases. It suffices to derive a contradiction. Apply `hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)` to reduce the goal to its premises. Rewrite using `[pow_succ]`. Use `conv_rhs => rw [hJ]`.

Conclude with `mul_dvd_mul_left _ hw`. Conclude with `hw'`.
-/
theorem exists_pow_mul_of_mem_factoredIdeals_insert [DecidableEq (HeightOneSpectrum R)]
    {S : Finset (HeightOneSpectrum R)}
    {v : HeightOneSpectrum R} {I : Ideal R} (hI : I ∈ factoredIdeals (insert v S)) :
    ∃ k : ℕ, ∃ J ∈ factoredIdeals S, I = v.asIdeal ^ k * J := by
  have hI0 : I ≠ 0 := by simpa [Submodule.zero_eq_bot] using hI.1
  have hfin : FiniteMultiplicity v.asIdeal I :=
    FiniteMultiplicity.of_not_isUnit (fun h ↦ v.isPrime.ne_top (Ideal.isUnit_iff.1 h)) hI0
  obtain ⟨J, hJ⟩ := pow_multiplicity_dvd v.asIdeal I
  refine ⟨multiplicity v.asIdeal I, J, ⟨?_, fun w hw ↦ ?_⟩, hJ⟩
  · rintro rfl
    rw [Ideal.mul_bot] at hJ
    exact hI.1 hJ
  · have hwI : w.asIdeal ∣ I := by
      rw [hJ]
      exact dvd_mul_of_dvd_right hw _
    rcases Finset.mem_insert.1 (hI.2 w hwI) with rfl | hw'
    · exfalso
      apply hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
      rw [pow_succ]
      conv_rhs => rw [hJ]
      exact mul_dvd_mul_left _ hw
    · exact hw'

/- English proof (translation)
Establish `hfin` using `Ideal.finite_factors (I := I) (by simpa [Submodule.zero_eq_bot] using hI)`. Use `Filter.eventually_atTop.2 ⟨hfin.toFinset, fun S hS ↦ ⟨hI, fun v hv ↦ hS ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `hv`.
-/
theorem eventually_mem_factoredIdeals {I : Ideal R} (hI : I ≠ ⊥) :
    ∀ᶠ S : Finset (HeightOneSpectrum R) in atTop, I ∈ factoredIdeals S := by
  have hfin := Ideal.finite_factors (I := I) (by simpa [Submodule.zero_eq_bot] using hI)
  refine Filter.eventually_atTop.2 ⟨hfin.toFinset, fun S hS ↦ ⟨hI, fun v hv ↦ hS ?_⟩⟩
  rw [Set.Finite.mem_toFinset]
  exact hv

end Factored

section Euler

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (g : Ideal R →* ℂ)

/- English proof (translation)
Establish `hv0 : v.asIdeal ≠ 0` using `by simpa [Submodule.zero_eq_bot] using v.ne_bot`. Establish `hinj : Injective fun k : ℕ ↦ v.asIdeal ^ k` using `pow_injective_of_not_isUnit (fun h ↦ v.isPrime.ne_top (Ideal.isUnit_iff.1 h)) hv0`. Establish `h` using `hsum.comp_injective hinj`. Simplify using `only [Function.comp_def, map_pow, norm_pow] at h`. Simplify using `using summable_geometric_iff_norm_lt_one.1 h`.
-/
theorem norm_lt_one_of_summable (hsum : Summable fun I ↦ ‖g I‖) (v : HeightOneSpectrum R) :
    ‖g v.asIdeal‖ < 1 := by
  have hv0 : v.asIdeal ≠ 0 := by simpa [Submodule.zero_eq_bot] using v.ne_bot
  have hinj : Injective fun k : ℕ ↦ v.asIdeal ^ k :=
    pow_injective_of_not_isUnit (fun h ↦ v.isPrime.ne_top (Ideal.isUnit_iff.1 h)) hv0
  have h := hsum.comp_injective hinj
  simp only [Function.comp_def, map_pow, norm_pow] at h
  simpa using summable_geometric_iff_norm_lt_one.1 h

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[factoredIdeals_empty, Finset.prod_empty]`. Establish `h : ({⊤} : Set (Ideal R)).indicator g = fun I ↦ if I = ⊤ then 1 else 0`. Use extensionality with `I`.

Distinguish the cases in `h : I = ⊤`. Rewrite using `[h, Set.indicator_of_mem (Set.mem_singleton _), if_pos rfl, ← Ideal.one_eq_top, map_one]`. Rewrite using `[Set.indicator_of_notMem (by simpa using h), if_neg h]`. Rewrite using `[h]`. Conclude with `hasSum_ite_eq ⊤ 1`.

Consider the case `insert v S hv ih`. Rewrite using `[Finset.prod_insert hv]`. Establish `hlt` using `norm_lt_one_of_summable g hsum v`. Establish `hgeo` using `hasSum_geometric_of_norm_lt_one hlt`. Establish `hgeo' : Summable fun k : ℕ ↦ ‖g v.asIdeal ^ k‖`.

Simplify `summable_geometric_of_lt_one (norm_nonneg _) hlt` using `[norm_pow]`. Establish `hind : Summable fun I ↦ ‖(factoredIdeals S).indicator g I‖` using `hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun I ↦ norm_indicator_le_norm_self g I`. Establish `hprod` using `hgeo.mul ih (summable_mul_of_summable_norm hgeo' hind)`. Use `set F : ℕ × Ideal R → ℂ := fun x ↦ g v.asIdeal ^ x.1 * (factoredIdeals S).indicator g x.2 with hF`. Establish `hmemF : ∀ x : ℕ × Ideal R, F x ≠ 0 → x.2 ∈ factoredIdeals S`.

Introduce `x hx`. Assume the negation of the conclusion as `h`. Apply `hx` to reduce the goal to its premises. Simplify using `only [hF, Set.indicator_of_notMem h, mul_zero]`. Establish `hndvd : ∀ {J : Ideal R}, J ∈ factoredIdeals S → ¬ v.asIdeal ∣ J` using `fun hJ h ↦ hv (hJ.2 v h)`.

Use `(hasSum_iff_hasSum_of_ne_zero_bij (fun x : support F ↦ v.asIdeal ^ (x : ℕ × Ideal R).1 * (x : ℕ × Ideal R).2) ?_ ?_ ?_).2 hprod` and prove the remaining obligations. Introduce and unpack `⟨⟨k, I⟩, hx⟩ ⟨⟨j, J⟩, hy⟩ h`. Take `⟨rfl, rfl⟩` from `pow_mul_inj (hndvd (hmemF _ hx)) (hndvd (hmemF _ hy)) h`. Both sides reduce to the same expression. Introduce `I hI`.

Rewrite `hI` using `[mem_support]`. Establish `hI' : I ∈ factoredIdeals (insert v S)` using `Set.mem_of_indicator_ne_zero hI`. Take `⟨k, J, hJ, rfl⟩` from `exists_pow_mul_of_mem_factoredIdeals_insert hI'`. Use `⟨⟨(k, J), ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[mem_support]`.

Simplify using `only [hF, Set.indicator_of_mem hJ]`. Rewrite `hI` using `[Set.indicator_of_mem hI', map_mul, map_pow]`. Then use the resulting hypothesis. Introduce and unpack `⟨⟨k, J⟩, hx⟩`. Establish `hJ` using `hmemF _ hx`. Simplify using `only [hF]`.

Rewrite using `[Set.indicator_of_mem hJ, Set.indicator_of_mem (pow_mul_mem_factoredIdeals_insert hJ k), map_mul, map_pow]`.
-/
theorem hasSum_indicator_factoredIdeals (hsum : Summable fun I ↦ ‖g I‖)
    (S : Finset (HeightOneSpectrum R)) :
    HasSum ((factoredIdeals S).indicator g) (∏ v ∈ S, (1 - g v.asIdeal)⁻¹) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [factoredIdeals_empty, Finset.prod_empty]
    have h : ({⊤} : Set (Ideal R)).indicator g = fun I ↦ if I = ⊤ then 1 else 0 := by
      ext I
      by_cases h : I = ⊤
      · rw [h, Set.indicator_of_mem (Set.mem_singleton _), if_pos rfl, ← Ideal.one_eq_top,
          map_one]
      · rw [Set.indicator_of_notMem (by simpa using h), if_neg h]
    rw [h]
    exact hasSum_ite_eq ⊤ 1
  | insert v S hv ih =>
    rw [Finset.prod_insert hv]
    have hlt := norm_lt_one_of_summable g hsum v
    have hgeo := hasSum_geometric_of_norm_lt_one hlt
    have hgeo' : Summable fun k : ℕ ↦ ‖g v.asIdeal ^ k‖ := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hlt
    have hind : Summable fun I ↦ ‖(factoredIdeals S).indicator g I‖ :=
      hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun I ↦ norm_indicator_le_norm_self g I
    have hprod := hgeo.mul ih (summable_mul_of_summable_norm hgeo' hind)
    set F : ℕ × Ideal R → ℂ := fun x ↦ g v.asIdeal ^ x.1 * (factoredIdeals S).indicator g x.2
      with hF
    have hmemF : ∀ x : ℕ × Ideal R, F x ≠ 0 → x.2 ∈ factoredIdeals S := by
      intro x hx
      by_contra h
      apply hx
      simp only [hF, Set.indicator_of_notMem h, mul_zero]
    have hndvd : ∀ {J : Ideal R}, J ∈ factoredIdeals S → ¬ v.asIdeal ∣ J := fun hJ h ↦ hv (hJ.2 v h)
    refine (hasSum_iff_hasSum_of_ne_zero_bij (fun x : support F ↦ v.asIdeal ^ (x : ℕ × Ideal R).1 *
      (x : ℕ × Ideal R).2) ?_ ?_ ?_).2 hprod
    · rintro ⟨⟨k, I⟩, hx⟩ ⟨⟨j, J⟩, hy⟩ h
      obtain ⟨rfl, rfl⟩ := pow_mul_inj (hndvd (hmemF _ hx)) (hndvd (hmemF _ hy)) h
      rfl
    · intro I hI
      rw [mem_support] at hI
      have hI' : I ∈ factoredIdeals (insert v S) := Set.mem_of_indicator_ne_zero hI
      obtain ⟨k, J, hJ, rfl⟩ := exists_pow_mul_of_mem_factoredIdeals_insert hI'
      refine ⟨⟨(k, J), ?_⟩, rfl⟩
      rw [mem_support]
      simp only [hF, Set.indicator_of_mem hJ]
      rwa [Set.indicator_of_mem hI', map_mul, map_pow] at hI
    · rintro ⟨⟨k, J⟩, hx⟩
      have hJ := hmemF _ hx
      simp only [hF]
      rw [Set.indicator_of_mem hJ, Set.indicator_of_mem (pow_mul_mem_factoredIdeals_insert hJ k),
        map_mul, map_pow]

/- English proof (translation)
Establish `key : (fun S : Finset (HeightOneSpectrum R) ↦ ∏ v ∈ S, (1 - g v.asIdeal)⁻¹) = fun S ↦ ∑' I, (factoredIdeals S).indicator g I`. Use function extensionality and compare the values at `fun S ↦ (hasSum_indicator_factoredIdeals g hsum S).tsum_eq.symm`. Use `show Tendsto (fun S : Finset (HeightOneSpectrum R) ↦ ∏ v ∈ S, (1 - g v.asIdeal)⁻¹) atTop (𝓝 (∑' I, g I))`. Rewrite using `[key]`. Use `tendsto_tsum_of_dominated_convergence hsum (fun I ↦ ?_) (Eventually.of_forall fun S I ↦ norm_indicator_le_norm_self g I)` and prove the remaining obligations.

Distinguish the cases in `hI : I = ⊥`. Substitute `hI` using the available equality. Establish `: ∀ S : Finset (HeightOneSpectrum R), (factoredIdeals S).indicator g ⊥ = g ⊥` using `fun S ↦ by rw [Set.indicator_of_notMem (fun h ↦ h.1 rfl), h0]`. Simplify using `only [this]`. Conclude with `tendsto_const_nhds`.

Use `tendsto_const_nhds.congr' ?_ filter_upwards [eventually_mem_factoredIdeals hI] with S hS` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem hS]`.
-/
theorem hasProd_euler (hsum : Summable fun I ↦ ‖g I‖) (h0 : g ⊥ = 0) :
    HasProd (fun v : HeightOneSpectrum R ↦ (1 - g v.asIdeal)⁻¹) (∑' I, g I) := by
  have key : (fun S : Finset (HeightOneSpectrum R) ↦ ∏ v ∈ S, (1 - g v.asIdeal)⁻¹) =
      fun S ↦ ∑' I, (factoredIdeals S).indicator g I :=
    funext fun S ↦ (hasSum_indicator_factoredIdeals g hsum S).tsum_eq.symm
  show Tendsto (fun S : Finset (HeightOneSpectrum R) ↦ ∏ v ∈ S, (1 - g v.asIdeal)⁻¹) atTop
    (𝓝 (∑' I, g I))
  rw [key]
  refine tendsto_tsum_of_dominated_convergence hsum (fun I ↦ ?_)
    (Eventually.of_forall fun S I ↦ norm_indicator_le_norm_self g I)
  by_cases hI : I = ⊥
  · subst hI
    have : ∀ S : Finset (HeightOneSpectrum R), (factoredIdeals S).indicator g ⊥ = g ⊥ :=
      fun S ↦ by rw [Set.indicator_of_notMem (fun h ↦ h.1 rfl), h0]
    simp only [this]
    exact tendsto_const_nhds
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_factoredIdeals hI] with S hS
    rw [Set.indicator_of_mem hS]

end Euler

section Summable

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Use `⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]`. Reduce the equality to equality of the corresponding arguments. Rewrite using `[← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one, show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _, show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff], Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le), ← Finset.card …`. Simplify using `[Set.coe_eq_subtype]`.
-/
theorem exists_tendsto_sum_card_absNorm_div :
    ∃ l : ℝ, Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ)) / n) atTop (𝓝 l) := by
  refine ⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n ↦ ?_⟩
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/- English proof (translation)
Take `⟨l, hl⟩` from `exists_tendsto_sum_card_absNorm_div (K := K)`. Use `LSeriesSummable_of_sum_norm_bigO (r := 1) ?_ zero_le_one hs` and prove the remaining obligations. Establish `h1` using `(hl.isBigO_one ℝ).mul (Asymptotics.isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)`. Use `h1.congr' ?_ ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ne_atTop 0] with n hn`.

Simplify using `only [Complex.norm_natCast]`. Rewrite using `[div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hn)]`. Conclude with `Eventually.of_forall fun n ↦ by simp`.
-/
theorem LSeriesSummable_card_absNorm {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s := by
  obtain ⟨l, hl⟩ := exists_tendsto_sum_card_absNorm_div (K := K)
  refine LSeriesSummable_of_sum_norm_bigO (r := 1) ?_ zero_le_one hs
  have h1 := (hl.isBigO_one ℝ).mul (Asymptotics.isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)
  refine h1.congr' ?_ ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Complex.norm_natCast]
    rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hn)]
  · exact Eventually.of_forall fun n ↦ by simp

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qp7.summable_absNorm_rpow_inv hσ`.
-/
theorem summable_absNorm_rpow_inv {σ : ℝ} (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 K) ↦ ((absNorm I : ℝ) ^ σ)⁻¹ :=
  _root_.UpperTheory.Reformulated.B.Qp7.summable_absNorm_rpow_inv hσ

end Summable

section Coprime

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/- English proof (translation)
Introduce `hI`. Rewrite `h` using `[Ideal.isCoprime_iff_sup_eq]`. Conclude with `v.isPrime.ne_top (top_le_iff.1 (h ▸ sup_le (Ideal.le_of_dvd hI) (Ideal.le_of_dvd hv)))`.
-/
theorem not_dvd_of_isCoprime {I 𝔪 : Ideal (𝓞 K)} (h : IsCoprime I 𝔪)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪) : ¬ v.asIdeal ∣ I := by
  intro hI
  rw [Ideal.isCoprime_iff_sup_eq] at h
  exact v.isPrime.ne_top (top_le_iff.1 (h ▸ sup_le (Ideal.le_of_dvd hI) (Ideal.le_of_dvd hv)))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h hv`. Conclude with `not_dvd_of_isCoprime h hv (dvd_refl _)`. Introduce `h`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`.

Conclude with `v.isMaximal.out.2 _ (left_lt_sup.2 fun hle ↦ h (Ideal.dvd_iff_le.2 hle))`.
-/
theorem isCoprime_asIdeal_iff (v : HeightOneSpectrum (𝓞 K)) (𝔪 : Ideal (𝓞 K)) :
    IsCoprime v.asIdeal 𝔪 ↔ ¬ v.asIdeal ∣ 𝔪 := by
  constructor
  · intro h hv
    exact not_dvd_of_isCoprime h hv (dvd_refl _)
  · intro h
    rw [Ideal.isCoprime_iff_sup_eq]
    exact v.isMaximal.out.2 _ (left_lt_sup.2 fun hle ↦ h (Ideal.dvd_iff_le.2 hle))

/- English proof (translation)
Establish `hI0 : I ≠ 0` using `by simpa [Submodule.zero_eq_bot] using hI`. Rewrite using `[count_coe K v hI0, Nat.cast_eq_zero]`. Assume the negation of the conclusion as `h`. Conclude with `hv ((Associates.count_ne_zero_iff_dvd hI0 (HeightOneSpectrum.prime v).irreducible).1 h)`.
-/
theorem count_coeIdeal_eq_zero {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ I) : count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  classical
  have hI0 : I ≠ 0 := by simpa [Submodule.zero_eq_bot] using hI
  rw [count_coe K v hI0, Nat.cast_eq_zero]
  by_contra h
  exact hv ((Associates.count_ne_zero_iff_dvd hI0 (HeightOneSpectrum.prime v).irreducible).1 h)

def idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (coeIdeal_ne_zero.2 hI)

/- English proof (translation)
The claim follows from `fun _ hv ↦ count_coeIdeal_eq_zero hI (not_dvd_of_isCoprime h hv)`.
-/
theorem idealUnit_mem_idealsPrimeTo {I 𝔪 : Ideal (𝓞 K)} (hI : I ≠ ⊥) (h : IsCoprime I 𝔪) :
    idealUnit I hI ∈ idealsPrimeTo 𝔪 :=
  fun _ hv ↦ count_coeIdeal_eq_zero hI (not_dvd_of_isCoprime h hv)

end Coprime

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)

open Classical in

def coeff (I : Ideal (𝓞 K)) : ℂ :=
  if h : I ≠ ⊥ ∧ IsCoprime I χ.conductor then
    (χ.idealCharacter ⟨idealUnit I h.1, idealUnit_mem_idealsPrimeTo h.1 h.2⟩ : ℂ)
  else 0

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem coeff_of_mem {I : Ideal (𝓞 K)} (h : I ≠ ⊥ ∧ IsCoprime I χ.conductor) :
    χ.coeff I = χ.idealCharacter ⟨idealUnit I h.1, idealUnit_mem_idealsPrimeTo h.1 h.2⟩ :=
  dif_pos h

/- English proof (translation)
The claim follows from `dif_neg h @[simp]`.
-/
theorem coeff_of_not {I : Ideal (𝓞 K)} (h : ¬ (I ≠ ⊥ ∧ IsCoprime I χ.conductor)) :
    χ.coeff I = 0 :=
  dif_neg h

@[simp]
/- English proof (translation)
The claim follows from `χ.coeff_of_not fun h ↦ h.1 rfl`.
-/
theorem coeff_bot : χ.coeff ⊥ = 0 :=
  χ.coeff_of_not fun h ↦ h.1 rfl

/- English proof (translation)
Unfold `coeff`. Use `split_ifs`. Rewrite using `[Circle.norm_coe]`. Simplify using the standard rewrite rules. Use the proof step `@[simp]`.
-/
theorem norm_coeff_le (I : Ideal (𝓞 K)) : ‖χ.coeff I‖ ≤ 1 := by
  unfold coeff
  split_ifs
  · rw [Circle.norm_coe]
  · simp

@[simp]
/- English proof (translation)
Establish `h : (⊤ : Ideal (𝓞 K)) ≠ ⊥ ∧ IsCoprime (⊤ : Ideal (𝓞 K)) χ.conductor` using `⟨top_ne_bot, by rw [← Ideal.one_eq_top]; exact isCoprime_one_left⟩`. Rewrite using `[coeff, dif_pos h]`. Establish `h1 : (⟨idealUnit ⊤ h.1, idealUnit_mem_idealsPrimeTo h.1 h.2⟩ : idealsPrimeTo χ.conductor) = 1` using `Subtype.ext (Units.ext (by simp [idealUnit]))`. Rewrite using `[h1, map_one, Circle.coe_one]`.
-/
theorem coeff_top : χ.coeff ⊤ = 1 := by
  have h : (⊤ : Ideal (𝓞 K)) ≠ ⊥ ∧ IsCoprime (⊤ : Ideal (𝓞 K)) χ.conductor :=
    ⟨top_ne_bot, by rw [← Ideal.one_eq_top]; exact isCoprime_one_left⟩
  rw [coeff, dif_pos h]
  have h1 : (⟨idealUnit ⊤ h.1, idealUnit_mem_idealsPrimeTo h.1 h.2⟩ : idealsPrimeTo χ.conductor) =
      1 :=
    Subtype.ext (Units.ext (by simp [idealUnit]))
  rw [h1, map_one, Circle.coe_one]

/- English proof (translation)
Distinguish the cases in `hI : I ≠ ⊥ ∧ IsCoprime I χ.conductor`. Distinguish the cases in `hJ : J ≠ ⊥ ∧ IsCoprime J χ.conductor`. Establish `hIJ : I * J ≠ ⊥ ∧ IsCoprime (I * J) χ.conductor` using `⟨fun h ↦ (Ideal.mul_eq_bot.1 h).elim hI.1 hJ.1, hI.2.mul_left hJ.2⟩`. Rewrite using `[coeff, coeff, coeff, dif_pos hI, dif_pos hJ, dif_pos hIJ, ← Circle.coe_mul, ← map_mul]`. Use `congr 2`.

Conclude with `Subtype.ext (Units.ext (by simp [idealUnit, coeIdeal_mul]))`. Rewrite using `[χ.coeff_of_not hJ, mul_zero]`. Use `χ.coeff_of_not fun h ↦ hJ ⟨fun hJ0 ↦ h.1 (by rw [hJ0, Ideal.mul_bot]), ?_⟩` and prove the remaining obligations. Conclude with `(IsCoprime.mul_left_iff.1 h.2).2`. Rewrite using `[χ.coeff_of_not hI, zero_mul]`.

Use `χ.coeff_of_not fun h ↦ hI ⟨fun hI0 ↦ h.1 (by rw [hI0, Ideal.bot_mul]), ?_⟩` and prove the remaining obligations. Conclude with `(IsCoprime.mul_left_iff.1 h.2).1`.
-/
theorem coeff_mul (I J : Ideal (𝓞 K)) : χ.coeff (I * J) = χ.coeff I * χ.coeff J := by
  by_cases hI : I ≠ ⊥ ∧ IsCoprime I χ.conductor
  · by_cases hJ : J ≠ ⊥ ∧ IsCoprime J χ.conductor
    · have hIJ : I * J ≠ ⊥ ∧ IsCoprime (I * J) χ.conductor :=
        ⟨fun h ↦ (Ideal.mul_eq_bot.1 h).elim hI.1 hJ.1, hI.2.mul_left hJ.2⟩
      rw [coeff, coeff, coeff, dif_pos hI, dif_pos hJ, dif_pos hIJ, ← Circle.coe_mul, ← map_mul]
      congr 2
      exact Subtype.ext (Units.ext (by simp [idealUnit, coeIdeal_mul]))
    · rw [χ.coeff_of_not hJ, mul_zero]
      refine χ.coeff_of_not fun h ↦ hJ ⟨fun hJ0 ↦ h.1 (by rw [hJ0, Ideal.mul_bot]), ?_⟩
      exact (IsCoprime.mul_left_iff.1 h.2).2
  · rw [χ.coeff_of_not hI, zero_mul]
    refine χ.coeff_of_not fun h ↦ hI ⟨fun hI0 ↦ h.1 (by rw [hI0, Ideal.bot_mul]), ?_⟩
    exact (IsCoprime.mul_left_iff.1 h.2).1

/- English proof (translation)
The claim follows from `χ.coeff_of_not fun h ↦ ((isCoprime_asIdeal_iff v _).1 h.2) hv`.
-/
theorem coeff_asIdeal_of_dvd {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ χ.conductor) :
    χ.coeff v.asIdeal = 0 :=
  χ.coeff_of_not fun h ↦ ((isCoprime_asIdeal_iff v _).1 h.2) hv

/- English proof (translation)
Rewrite using `[coeff, dif_pos ⟨v.ne_bot, (isCoprime_asIdeal_iff v _).2 hv⟩]`. Both sides reduce to the same expression.
-/
theorem coeff_asIdeal_of_not_dvd {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ χ.conductor) :
    χ.coeff v.asIdeal =
      χ.idealCharacter ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ := by
  rw [coeff, dif_pos ⟨v.ne_bot, (isCoprime_asIdeal_iff v _).2 hv⟩]
  rfl

def coeffTerm (s : ℂ) : Ideal (𝓞 K) →* ℂ where
  toFun I := χ.coeff I / (absNorm I : ℂ) ^ s
  map_one' := by
    rw [Ideal.one_eq_top, coeff_top, Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow, _root_.div_one]
  map_mul' I J := by
    rw [coeff_mul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, mul_div_mul_comm]

/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem coeffTerm_apply (s : ℂ) (I : Ideal (𝓞 K)) :
    χ.coeffTerm s I = χ.coeff I / (absNorm I : ℂ) ^ s :=
  rfl

@[simp]
/- English proof (translation)
Rewrite using `[coeffTerm_apply, coeff_bot, zero_div]`.
-/
theorem coeffTerm_bot (s : ℂ) : χ.coeffTerm s ⊥ = 0 := by
  rw [coeffTerm_apply, coeff_bot, zero_div]

/- English proof (translation)
Distinguish the cases in `hI : I = ⊥`. Substitute `hI` using the available equality. Rewrite using `[coeffTerm_bot, norm_zero]`. Conclude with `inv_nonneg.2 (Real.rpow_nonneg (Nat.cast_nonneg _) _)`. Establish `hpos : 0 < absNorm I` using `Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])`.

Rewrite using `[coeffTerm_apply, norm_div, Complex.norm_natCast_cpow_of_pos hpos, inv_eq_one_div]`. Conclude with `div_le_div_of_nonneg_right (χ.norm_coeff_le I) (Real.rpow_nonneg (Nat.cast_nonneg _) _)`.
-/
theorem norm_coeffTerm_le {s : ℂ} (I : Ideal (𝓞 K)) :
    ‖χ.coeffTerm s I‖ ≤ ((absNorm I : ℝ) ^ s.re)⁻¹ := by
  by_cases hI : I = ⊥
  · subst hI
    rw [coeffTerm_bot, norm_zero]
    exact inv_nonneg.2 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · have hpos : 0 < absNorm I := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
    rw [coeffTerm_apply, norm_div, Complex.norm_natCast_cpow_of_pos hpos, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (χ.norm_coeff_le I) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/- English proof (translation)
The claim follows from `(summable_absNorm_rpow_inv hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _) χ.norm_coeffTerm_le`.
-/
theorem summable_norm_coeffTerm {s : ℂ} (hs : 1 < s.re) :
    Summable fun I ↦ ‖χ.coeffTerm s I‖ :=
  (summable_absNorm_rpow_inv hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _) χ.norm_coeffTerm_le

def LCoeff (n : ℕ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, χ.coeff I

def LFunction (s : ℂ) : ℂ :=
  LSeries χ.LCoeff s

/- English proof (translation)
Establish `hsum : Summable (χ.coeffTerm s)` using `(χ.summable_norm_coeffTerm hs).of_norm`. Set `e` to `Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ absNorm I)`. Establish `h1 : HasSum (χ.coeffTerm s ∘ e) (∑' I, χ.coeffTerm s I)` using `e.hasSum_iff.2 hsum.hasSum`. Establish `h2` using `h1.sigma fun n ↦ ((e.summable_iff.2 hsum).sigma_factor n).hasSum`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `n`. Rewrite using `[LSeries.term_def]`. Use `split_ifs with hn`. Substitute `hn` using the available equality. Use `symm`.

Use `(tsum_congr fun y ↦ ?_).trans tsum_zero` and prove the remaining obligations. Establish `hy : (y : Ideal (𝓞 K)) = ⊥` using `Ideal.absNorm_eq_zero_iff.1 y.2`. Simplify using `[e, hy]`. Rewrite using `[LCoeff, ← tsum_div_const]`. Use `tsum_congr fun y ↦ ?_` and prove the remaining obligations.

Simplify using `[e, coeffTerm_apply, y.2]`.
-/
theorem hasSum_term_LCoeff {s : ℂ} (hs : 1 < s.re) :
    HasSum (LSeries.term χ.LCoeff s) (∑' I, χ.coeffTerm s I) := by
  have hsum : Summable (χ.coeffTerm s) := (χ.summable_norm_coeffTerm hs).of_norm
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ absNorm I)
  have h1 : HasSum (χ.coeffTerm s ∘ e) (∑' I, χ.coeffTerm s I) := e.hasSum_iff.2 hsum.hasSum
  have h2 := h1.sigma fun n ↦ ((e.summable_iff.2 hsum).sigma_factor n).hasSum
  convert h2 using 1
  funext n
  rw [LSeries.term_def]
  split_ifs with hn
  · subst hn
    symm
    refine (tsum_congr fun y ↦ ?_).trans tsum_zero
    have hy : (y : Ideal (𝓞 K)) = ⊥ := Ideal.absNorm_eq_zero_iff.1 y.2
    simp [e, hy]
  · rw [LCoeff, ← tsum_div_const]
    refine tsum_congr fun y ↦ ?_
    simp [e, coeffTerm_apply, y.2]

/- English proof (translation)
The claim follows from `(χ.hasSum_term_LCoeff hs).summable`.
-/
theorem LSeriesSummable_LCoeff {s : ℂ} (hs : 1 < s.re) : LSeriesSummable χ.LCoeff s :=
  (χ.hasSum_term_LCoeff hs).summable

/- English proof (translation)
The claim follows from `(χ.hasSum_term_LCoeff hs).tsum_eq`.
-/
theorem LFunction_eq_tsum_coeffTerm {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = ∑' I, χ.coeffTerm s I :=
  (χ.hasSum_term_LCoeff hs).tsum_eq

/- English proof (translation)
Simplify `χ.summable_norm_coeffTerm hs` using `[coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]`.
-/
theorem summable_norm_coeff_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) ↦ ‖χ.coeff I * (absNorm I : ℂ) ^ (-s)‖ := by
  simpa [coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv] using χ.summable_norm_coeffTerm hs

/- English proof (translation)
Establish `hfun : (fun I : Ideal (𝓞 K) ↦ χ.coeff I * (absNorm I : ℂ) ^ (-s)) = χ.coeffTerm s`. Use function extensionality and compare the values at `fun I ↦ by rw [coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]`. Rewrite using `[χ.LFunction_eq_tsum_coeffTerm hs, hfun]`. Conclude with `((χ.summable_norm_coeffTerm hs).of_norm).hasSum`.
-/
theorem hasSum_LFunction {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 K) ↦ χ.coeff I * (absNorm I : ℂ) ^ (-s)) (χ.LFunction s) := by
  have hfun : (fun I : Ideal (𝓞 K) ↦ χ.coeff I * (absNorm I : ℂ) ^ (-s)) = χ.coeffTerm s :=
    funext fun I ↦ by rw [coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]
  rw [χ.LFunction_eq_tsum_coeffTerm hs, hfun]
  exact ((χ.summable_norm_coeffTerm hs).of_norm).hasSum

/- English proof (translation)
Establish `h` using `χ.hasSum_LFunction hs`. Rewrite `h` using `[← hasSum_subtype_iff_of_support_subset (s := {I | I ≠ ⊥ ∧ IsCoprime I χ.conductor})]`. Establish `h2 : HasSum (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦ χ.coeff I.1 * (absNorm I.1 : ℂ) ^ (-s)) (χ.LFunction s)` using `h`. Establish `hfun : (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦ (χ.idealCharacter ⟨idealUnit I.1 I.2.1, idealUnit_mem_idealsPrimeTo I.2.1 I.2.2⟩ : ℂ) * (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) = fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦ χ.coeff I.1 * (I …`. Use function extensionality and compare the values at `fun I ↦ by rw [χ.coeff_of_mem I.2]`.

Rewrite using `[hfun]`. Conclude with `h2`. Introduce `I hI`. Assume the negation of the conclusion as `h'`. Conclude with `hI (by simp only [χ.coeff_of_not h', zero_mul])`.
-/
theorem hasSum_LFunction_coprime {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦
      (χ.idealCharacter ⟨idealUnit I.1 I.2.1, idealUnit_mem_idealsPrimeTo I.2.1 I.2.2⟩ : ℂ) *
        (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) (χ.LFunction s) := by
  have h := χ.hasSum_LFunction hs
  rw [← hasSum_subtype_iff_of_support_subset (s := {I | I ≠ ⊥ ∧ IsCoprime I χ.conductor})] at h
  · have h2 : HasSum (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦
        χ.coeff I.1 * (absNorm I.1 : ℂ) ^ (-s)) (χ.LFunction s) := h
    have hfun : (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦
        (χ.idealCharacter ⟨idealUnit I.1 I.2.1, idealUnit_mem_idealsPrimeTo I.2.1 I.2.2⟩ : ℂ) *
          (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
        fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦
          χ.coeff I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s) :=
      funext fun I ↦ by rw [χ.coeff_of_mem I.2]
    rw [hfun]
    exact h2
  · intro I hI
    by_contra h'
    exact hI (by simp only [χ.coeff_of_not h', zero_mul])

/- English proof (translation)
The claim follows from `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ χ.LSeriesSummable_LCoeff (by simpa using hy)`.
-/
theorem abscissaOfAbsConv_LCoeff_le : LSeries.abscissaOfAbsConv χ.LCoeff ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
    χ.LSeriesSummable_LCoeff (by simpa using hy)

/- English proof (translation)
The claim follows from `(LSeries_differentiableOn χ.LCoeff).mono fun s hs ↦ χ.abscissaOfAbsConv_LCoeff_le.trans_lt (by exact_mod_cast hs)`.
-/
theorem differentiableOn_LFunction : DifferentiableOn ℂ χ.LFunction {s | 1 < s.re} :=
  (LSeries_differentiableOn χ.LCoeff).mono fun s hs ↦
    χ.abscissaOfAbsConv_LCoeff_le.trans_lt (by exact_mod_cast hs)

/- English proof (translation)
The claim follows from `(LSeries_analyticOnNhd χ.LCoeff).mono fun s hs ↦ χ.abscissaOfAbsConv_LCoeff_le.trans_lt (by exact_mod_cast hs)`.
-/
theorem analyticOnNhd_LFunction : AnalyticOnNhd ℂ χ.LFunction {s | 1 < s.re} :=
  (LSeries_analyticOnNhd χ.LCoeff).mono fun s hs ↦
    χ.abscissaOfAbsConv_LCoeff_le.trans_lt (by exact_mod_cast hs)

/- English proof (translation)
Rewrite using `[χ.LFunction_eq_tsum_coeffTerm hs]`. Use `hasProd_euler (χ.coeffTerm s) (χ.summable_norm_coeffTerm hs) (χ.coeffTerm_bot s) using 3 with v` and compare the differences between its conclusion and the goal. Rewrite using `[coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]`.
-/
theorem LFunction_hasProd_all {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) ↦
      (1 - χ.coeff v.asIdeal * (absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (χ.LFunction s) := by
  rw [χ.LFunction_eq_tsum_coeffTerm hs]
  convert hasProd_euler (χ.coeffTerm s) (χ.summable_norm_coeffTerm hs) (χ.coeffTerm_bot s)
    using 3 with v
  rw [coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]

/- English proof (translation)
Establish `h` using `χ.LFunction_hasProd_all hs`. Rewrite `h` using `[← hasProd_subtype_iff_of_mulSupport_subset (s := {v : HeightOneSpectrum (𝓞 K) | ¬ v.asIdeal ∣ χ.conductor})]`. Establish `h2 : HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦ (1 - χ.coeff v.1.asIdeal * (absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) (χ.LFunction s)` using `h`. Establish `hfun : (fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦ (1 - (χ.idealCharacter ⟨primeIdealUnit v.1, primeIdealUnit_mem_idealsPrimeTo v.2⟩ : ℂ) * (absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) = fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦ (1 - χ …`. Use function extensionality and compare the values at `fun v ↦ by rw [χ.coeff_asIdeal_of_not_dvd v.2]`.

Rewrite using `[hfun]`. Conclude with `h2`. Introduce `v hv`. Assume the negation of the conclusion as `hdvd`. Establish `hdvd' : v.asIdeal ∣ χ.conductor` using `by simpa using hdvd`.

Apply `hv` to reduce the goal to its premises. Simplify using `only [χ.coeff_asIdeal_of_dvd hdvd', zero_mul, sub_zero, inv_one]`.
-/
theorem LFunction_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦
      (1 - (χ.idealCharacter ⟨primeIdealUnit v.1, primeIdealUnit_mem_idealsPrimeTo v.2⟩ : ℂ) *
        (absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) (χ.LFunction s) := by
  have h := χ.LFunction_hasProd_all hs
  rw [← hasProd_subtype_iff_of_mulSupport_subset
    (s := {v : HeightOneSpectrum (𝓞 K) | ¬ v.asIdeal ∣ χ.conductor})] at h
  · have h2 : HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦
        (1 - χ.coeff v.1.asIdeal * (absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) (χ.LFunction s) := h
    have hfun : (fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦
        (1 - (χ.idealCharacter ⟨primeIdealUnit v.1, primeIdealUnit_mem_idealsPrimeTo v.2⟩ : ℂ) *
          (absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) =
        fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦
          (1 - χ.coeff v.1.asIdeal * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ :=
      funext fun v ↦ by rw [χ.coeff_asIdeal_of_not_dvd v.2]
    rw [hfun]
    exact h2
  · intro v hv
    by_contra hdvd
    have hdvd' : v.asIdeal ∣ χ.conductor := by simpa using hdvd
    apply hv
    simp only [χ.coeff_asIdeal_of_dvd hdvd', zero_mul, sub_zero, inv_one]

/- English proof (translation)
Use `set x : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ χ.coeffTerm s v.asIdeal with hx`. Establish `hlt : ∀ v, ‖x v‖ < 1` using `fun v ↦ norm_lt_one_of_summable _ (χ.summable_norm_coeffTerm hs) v`. Establish `hne : ∀ v, 1 - x v ≠ 0`. Introduce `v h`. Establish `h1 : x v = 1` using `(sub_eq_zero.1 h).symm`.

Establish `h2` using `hlt v`. Rewrite `h2` using `[h1, norm_one]`. Conclude with `lt_irrefl _ h2`. Establish `hinj : Injective fun v : HeightOneSpectrum (𝓞 K) ↦ v.asIdeal` using `fun v w h ↦ HeightOneSpectrum.ext h`. Establish `hxs : Summable x` using `Summable.of_norm (f := x) ((χ.summable_norm_coeffTerm hs).comp_injective hinj)`.

Establish `hlog : Summable fun v ↦ Complex.log (1 - x v)` using `(Complex.summable_log_one_add_of_summable hxs.neg).congr fun v ↦ by rw [sub_eq_add_neg]`. Establish `hP : HasProd (fun v ↦ 1 - x v) (Complex.exp (∑' v, Complex.log (1 - x v)))` using `Complex.hasProd_of_hasSum_log hne hlog.hasSum`. Establish `hL : HasProd (fun v ↦ (1 - x v)⁻¹) (χ.LFunction s)`. Rewrite using `[χ.LFunction_eq_tsum_coeffTerm hs]`. Conclude with `hasProd_euler _ (χ.summable_norm_coeffTerm hs) (χ.coeffTerm_bot s)`.

Establish `h1` using `hL.mul hP`. Establish `h2 : (fun v ↦ (1 - x v)⁻¹ * (1 - x v)) = fun _ ↦ (1 : ℂ)`. Use function extensionality and compare the values at `fun v ↦ inv_mul_cancel₀ (hne v)`. Rewrite `h1` using `[h2]`. Establish `h3` using `h1.unique hasProd_one`.

Introduce `hL0`. Rewrite `h3` using `[hL0, zero_mul]`. Conclude with `zero_ne_one h3`.
-/
theorem LFunction_ne_zero {s : ℂ} (hs : 1 < s.re) : χ.LFunction s ≠ 0 := by
  set x : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ χ.coeffTerm s v.asIdeal with hx
  have hlt : ∀ v, ‖x v‖ < 1 := fun v ↦ norm_lt_one_of_summable _ (χ.summable_norm_coeffTerm hs) v
  have hne : ∀ v, 1 - x v ≠ 0 := by
    intro v h
    have h1 : x v = 1 := (sub_eq_zero.1 h).symm
    have h2 := hlt v
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hinj : Injective fun v : HeightOneSpectrum (𝓞 K) ↦ v.asIdeal :=
    fun v w h ↦ HeightOneSpectrum.ext h
  have hxs : Summable x :=
    Summable.of_norm (f := x) ((χ.summable_norm_coeffTerm hs).comp_injective hinj)
  have hlog : Summable fun v ↦ Complex.log (1 - x v) :=
    (Complex.summable_log_one_add_of_summable hxs.neg).congr fun v ↦ by rw [sub_eq_add_neg]
  have hP : HasProd (fun v ↦ 1 - x v) (Complex.exp (∑' v, Complex.log (1 - x v))) :=
    Complex.hasProd_of_hasSum_log hne hlog.hasSum
  have hL : HasProd (fun v ↦ (1 - x v)⁻¹) (χ.LFunction s) := by
    rw [χ.LFunction_eq_tsum_coeffTerm hs]
    exact hasProd_euler _ (χ.summable_norm_coeffTerm hs) (χ.coeffTerm_bot s)
  have h1 := hL.mul hP
  have h2 : (fun v ↦ (1 - x v)⁻¹ * (1 - x v)) = fun _ ↦ (1 : ℂ) :=
    funext fun v ↦ inv_mul_cancel₀ (hne v)
  rw [h2] at h1
  have h3 := h1.unique hasProd_one
  intro hL0
  rw [hL0, zero_mul] at h3
  exact zero_ne_one h3

/- English proof (translation)
Establish `h : ∀ v, IdeleGroup.conductorExponentAt ((1 : HeckeCharacter K).toIdele.comp IdeleGroup.ofFinite) v = 0` using `fun v ↦ (IdeleGroup.conductorExponentAt_eq_zero_iff Circle.noSmallSubgroups _ ((1 : HeckeCharacter K).continuous_toIdele.comp IdeleGroup.continuous_ofFinite) v).2 fun x _ ↦ by rw [MonoidHom.mem_ker]; rfl`. Rewrite using `[conductor, IdeleGroup.conductor]`. Simplify using `only [h, pow_zero]`. Rewrite using `[finprod_one, Ideal.one_eq_top]`.
-/
theorem conductor_one : (1 : HeckeCharacter K).conductor = ⊤ := by
  have h : ∀ v, IdeleGroup.conductorExponentAt
      ((1 : HeckeCharacter K).toIdele.comp IdeleGroup.ofFinite) v = 0 := fun v ↦
    (IdeleGroup.conductorExponentAt_eq_zero_iff Circle.noSmallSubgroups _
      ((1 : HeckeCharacter K).continuous_toIdele.comp IdeleGroup.continuous_ofFinite) v).2
      fun x _ ↦ by rw [MonoidHom.mem_ker]; rfl
  rw [conductor, IdeleGroup.conductor]
  simp only [h, pow_zero]
  rw [finprod_one, Ideal.one_eq_top]

/- English proof (translation)
Establish `h : I ≠ ⊥ ∧ IsCoprime I (1 : HeckeCharacter K).conductor` using `⟨hI, by rw [conductor_one, ← Ideal.one_eq_top]; exact isCoprime_one_right⟩`. Rewrite using `[coeff, dif_pos h]`. Conclude with `congrArg ((↑) : Circle → ℂ) rfl |>.trans Circle.coe_one`.
-/
theorem coeff_one {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : (1 : HeckeCharacter K).coeff I = 1 := by
  have h : I ≠ ⊥ ∧ IsCoprime I (1 : HeckeCharacter K).conductor :=
    ⟨hI, by rw [conductor_one, ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  rw [coeff, dif_pos h]
  exact congrArg ((↑) : Circle → ℂ) rfl |>.trans Circle.coe_one

/- English proof (translation)
Rewrite using `[LFunction, dedekindZeta]`. Use `LSeries_congr (fun {n} hn ↦ ?_) s` and prove the remaining obligations. Establish `hy : ∀ y : {I : Ideal (𝓞 K) // absNorm I = n}, (1 : HeckeCharacter K).coeff y = 1`. Introduce `y`. Use `coeff_one fun h ↦ hn ?_` and prove the remaining obligations.

Rewrite using `[← y.2, h, Ideal.absNorm_bot]`. Rewrite using `[LCoeff, tsum_congr hy, tsum_const, nsmul_eq_mul, mul_one]`.
-/
theorem LFunction_one (s : ℂ) : (1 : HeckeCharacter K).LFunction s = dedekindZeta K s := by
  rw [LFunction, dedekindZeta]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  have hy : ∀ y : {I : Ideal (𝓞 K) // absNorm I = n}, (1 : HeckeCharacter K).coeff y = 1 := by
    intro y
    refine coeff_one fun h ↦ hn ?_
    rw [← y.2, h, Ideal.absNorm_bot]
  rw [LCoeff, tsum_congr hy, tsum_const, nsmul_eq_mul, mul_one]

end HeckeCharacter

end

end GroundTheory.Global

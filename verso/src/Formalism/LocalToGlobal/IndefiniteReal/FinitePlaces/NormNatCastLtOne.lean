import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FiniteAdeleSndAlgebraMap
import ReciprocityTheory.AdeleApproximation.AdeleIntA

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter

namespace Formalism.IndefR.Fin.U1

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `first`. Consider the case `exact NumberField.InfinitePlace.Completion.norm_coe w (show WithAbs w.1 from x)`. Consider the case `exact NumberField.InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 x)`. Consider the case `simp [NumberField.InfinitePlace.Completion.norm_coe]`.
-/
theorem norm_coe_inf (w : InfinitePlace F) (x : F) : ‖(x : w.Completion)‖ = w x := by
  first
  | exact NumberField.InfinitePlace.Completion.norm_coe w (show WithAbs w.1 from x)
  | exact NumberField.InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 x)
  | simp [NumberField.InfinitePlace.Completion.norm_coe]

/- English proof (translation)
Rewrite using `[show algebraMap F w.Completion (m : F) = ((m : F) : w.Completion) from rfl, norm_coe_inf]`. Simplify using `[← NumberField.InfinitePlace.norm_embedding_eq]`.
-/
theorem norm_nat_inf (w : InfinitePlace F) (m : ℕ) : ‖algebraMap F w.Completion (m : F)‖ = m := by
  rw [show algebraMap F w.Completion (m : F) = ((m : F) : w.Completion) from rfl, norm_coe_inf]
  simp [← NumberField.InfinitePlace.norm_embedding_eq]

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `Valued.toNormedField.norm_le_one_iff`.
-/
theorem norm_le_one_iff_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

/- English proof (translation)
The claim follows from `(norm_le_one_iff_int v _).mpr (natCast_mem _ m)`.
-/
theorem norm_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) : ‖(m : v.adicCompletion F)‖ ≤ 1 := (norm_le_one_iff_int v _).mpr (natCast_mem _ m)

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap F (v.adicCompletion F)) m]`. Conclude with `(map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hm)`.
-/
theorem nat_ne_zero_fin (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (hm : m ≠ 0) : (m : v.adicCompletion F) ≠ 0 := by
  rw [← map_natCast (algebraMap F (v.adicCompletion F)) m]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hm)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp`.
-/
theorem natCast_apply' (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) : (N : Af F) v = (N : v.adicCompletion F) := by
  first
  | rfl
  | simp

/- English proof (translation)
Rewrite using `[← natCast_apply' N v]`. Both sides reduce to the same expression.
-/
theorem natCast_mul_apply' (N : ℕ) (z : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    ((N : Af F) * z) v = (N : v.adicCompletion F) * z v := by
  rw [← natCast_apply' N v]
  rfl

/- English proof (translation)
Establish `hmem : ((c : ℕ) : 𝓞 F) ∈ v.asIdeal`. Take `⟨k, hk⟩` from `hc`. Rewrite using `[hk, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.absNorm_mem v.asIdeal)`. Rewrite using `[Valued.toNormedField.norm_lt_one_iff]`.

Establish `h1 : ((c : v.adicCompletion F)) = ((algebraMap (𝓞 F) F (c : 𝓞 F) : F) : v.adicCompletion F)`. Rewrite using `[map_natCast]`. Use `first`. Consider the case `exact (map_natCast (algebraMap F (v.adicCompletion F)) c).symm`. Consider the case `norm_cast`.

Consider the case `rfl`. Rewrite using `[h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(v.intValuation_lt_one_iff_mem _).mpr hmem`.
-/
theorem norm_natCast_lt_one' (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : ((c : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem v.asIdeal)
  rw [Valued.toNormedField.norm_lt_one_iff]
  have h1 : ((c : v.adicCompletion F)) = ((algebraMap (𝓞 F) F (c : 𝓞 F) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    first
    | exact (map_natCast (algebraMap F (v.adicCompletion F)) c).symm
    | norm_cast
    | rfl
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_lt_one_iff_mem _).mpr hmem

/- English proof (translation)
Establish `hAopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))` using `fun _ => Valued.isOpen_valuationSubring _`. Establish `hU' : U ∈ Filter.map (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) (𝓝 (fun v => ⟨0, zero_mem (v.adicCompletionIntegers F)⟩))`. Rewrite using `[← RestrictedProduct.nhds_eq_map_structureMap hAopen]`. Conclude with `hU`. Establish `hU2 : (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) ⁻¹' (U : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicComp …` using `hU'`.

Rewrite `hU2` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, t, ht, hIt⟩` from `hU2`. Establish `hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > (0 : ℝ), ∀ y : (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ‖(y : v.adicCompletion F)‖ < ε → y ∈ t v`. Introduce `v`. Take `⟨u, hu, hut⟩` from `(mem_nhds_subtype _ _ _).1 (ht v)`.

Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hu`. Use `⟨ε, hε, fun y hy => hut (hball ?_)⟩` and prove the remaining obligations. Simplify `hy` using `[Metric.mem_ball, dist_zero_right]`. Use `choose ε hεpos hεt using hε`. Use `set c : ℕ := ∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal with hcdef`.

Establish `hc0 : c ≠ 0`. Rewrite using `[hcdef, Finset.prod_ne_zero_iff]`. Introduce `v _`. Conclude with `(lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'`. Establish `hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1` using `fun v hv => norm_natCast_lt_one' v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))`.

Establish `hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v` using `fun v hv => (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually (Iio_mem_nhds (hεpos v))`. Take `⟨k, hk⟩` from `((Filter.eventually_all_finite hI).2 hev).exists`. Use `⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun z hz => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ v, (((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))`. Introduce `v`.

Rewrite using `[natCast_mul_apply']`. Conclude with `mul_mem (natCast_mem _ _) (hz v)`. Establish `hx : ((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z = RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite (fun v => ⟨_, hmem v⟩)`. Use extensionality with `v`. Both sides reduce to the same expression.

Rewrite using `[hx]`. Apply `hIt` to reduce the goal to its premises. Introduce `v hv`. Apply `hεt` to reduce the goal to its premises. Use `show ‖(((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v‖ < ε v`.

Rewrite using `[natCast_mul_apply', norm_mul, Nat.cast_pow, norm_pow]`. Establish `hz1 : ‖z v‖ ≤ 1` using `(norm_le_one_iff_int v _).2 (hz v)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem finNhd (U : Set (Af F)) (hU : U ∈ 𝓝 (0 : Af F)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z : Af F, (∀ v, z v ∈ v.adicCompletionIntegers F) → (N : Af F) * z ∈ U := by
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
    exact (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one' v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))
  have hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v := fun v hv =>
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually
      (Iio_mem_nhds (hεpos v))
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hI).2 hev).exists
  refine ⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun z hz => ?_⟩
  have hmem : ∀ v, (((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v ∈
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    rw [natCast_mul_apply']
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
  rw [natCast_mul_apply', norm_mul, Nat.cast_pow, norm_pow]
  have hz1 : ‖z v‖ ≤ 1 := (norm_le_one_iff_int v _).2 (hz v)
  calc ‖(c : v.adicCompletion F)‖ ^ k * ‖z v‖ ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 :=
        mul_le_mul_of_nonneg_left hz1 (pow_nonneg (norm_nonneg _) _)
    _ < ε v := by rw [mul_one]; exact hk v hv

/- English proof (translation)
Use `⟨algebraMap F (Af F) ((N : F)⁻¹) * y, fun v => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← norm_le_one_iff_int] show ‖algebraMap F (v.adicCompletion F) ((N : F)⁻¹) * y v‖ ≤ 1`. Establish `hN0 : 0 < ‖(N : v.adicCompletion F)‖` using `norm_pos_iff.2 (nat_ne_zero_fin v hN)`. Rewrite using `[map_inv₀, map_natCast, norm_mul, norm_inv, inv_mul_le_iff₀ hN0, mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, ← map_natCast (algebraMap F (Af F)) N, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one, one_mul]`.
-/
theorem int_of_le (y : Af F) (N M : ℕ) (hN : N ≠ 0)
    (hy : ∀ v, ‖y v‖ ≤ ‖(N : v.adicCompletion F)‖ * ‖(M : v.adicCompletion F)‖) :
    ∃ z : Af F, (∀ v, z v ∈ v.adicCompletionIntegers F) ∧ y = (N : Af F) * z := by
  refine ⟨algebraMap F (Af F) ((N : F)⁻¹) * y, fun v => ?_, ?_⟩
  · rw [← norm_le_one_iff_int]
    show ‖algebraMap F (v.adicCompletion F) ((N : F)⁻¹) * y v‖ ≤ 1
    have hN0 : 0 < ‖(N : v.adicCompletion F)‖ := norm_pos_iff.2 (nat_ne_zero_fin v hN)
    rw [map_inv₀, map_natCast, norm_mul, norm_inv, inv_mul_le_iff₀ hN0, mul_one]
    calc ‖y v‖ ≤ ‖(N : v.adicCompletion F)‖ * ‖(M : v.adicCompletion F)‖ := hy v
      _ ≤ ‖(N : v.adicCompletion F)‖ * 1 := mul_le_mul_of_nonneg_left (norm_nat_le_one v M) hN0.le
      _ = ‖(N : v.adicCompletion F)‖ := mul_one _
  · rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one, one_mul]

/- English proof (translation)
Take `⟨U1, hU1, U2, hU2, hsub⟩` from `mem_nhds_prod_iff.1 ht`. Establish `hU1' : U1 ∈ 𝓝 (((1 : Ainf F), (1 : Af F)))` using `hU1`. Establish `hU2' : U2 ∈ 𝓝 (((0 : Ainf F), (0 : Af F)))` using `hU2`. Take `⟨V1, hV1, W1, hW1, hs1⟩` from `mem_nhds_prod_iff.1 hU1'`. Take `⟨V2, hV2, W2, hW2, hs2⟩` from `mem_nhds_prod_iff.1 hU2'`.

Establish `hW1' : (fun z : Af F => 1 + z) ⁻¹' W1 ∈ 𝓝 (0 : Af F)`. Establish `: Tendsto (fun z : Af F => 1 + z) (𝓝 0) (𝓝 1)`. Establish `h` using `(continuous_const_add (1 : Af F)).tendsto 0`. Rewrite `h` using `[add_zero]`. Then use the resulting hypothesis. Conclude with `this hW1`.

Take `⟨N1, hN1, hN1W⟩` from `finNhd _ hW1'`. Take `⟨N2, hN2, hN2W⟩` from `finNhd _ hW2`. Establish `hinf : ∀ (V : Set (∀ w : InfinitePlace F, w.Completion)) (x : ∀ w : InfinitePlace F, w.Completion), V ∈ 𝓝 x → ∃ ε : InfinitePlace F → ℝ, (∀ w, 0 < ε w) ∧ ∀ y : ∀ w : InfinitePlace F, w.Completion, (∀ w, ‖y w - x w‖ < ε w) → y ∈ V`. Introduce `V x hV'`. Rewrite `hV'` using `[nhds_pi, Filter.mem_pi]`.

Take `⟨I, -, s, hs, hIs⟩` from `hV'`. Establish `h1 : ∀ w, ∃ ε > 0, ∀ y : w.Completion, ‖y - x w‖ < ε → y ∈ s w` using `fun w => by`. Take `⟨ε, hε, hb⟩` from `Metric.mem_nhds_iff.1 (hs w)`. Conclude with `⟨ε, hε, fun y hy => hb (by rw [Metric.mem_ball, dist_eq_norm]; exact hy)⟩`. Use `choose ε hε hεs using h1`.

Conclude with `⟨ε, hε, fun y hy => hIs fun w _ => hεs w (y w) (hy w)⟩`. Take `⟨ε1, hε1, h1⟩` from `hinf V1 1 hV1`. Take `⟨ε2, hε2, h2⟩` from `hinf V2 0 hV2`. Use `⟨fun w => min (ε1 w) (ε2 w), fun w => lt_min (hε1 w) (hε2 w), N1 * N2, mul_ne_zero (by omega) (by omega), fun a b hi hf => ?_⟩` and prove the remaining obligations. Take `⟨za, hza, heqa⟩` from `int_of_le (a.2 - 1) N1 N2 (by omega) fun v => by`.

Use `(hf v).1` as an intermediate fact. Rewrite `this` using `[Nat.cast_mul, norm_mul]`. Then use the resulting hypothesis. Take `⟨zb, hzb, heqb⟩` from `int_of_le b.2 N2 N1 (by omega) fun v => by`. Use `(hf v).2` as an intermediate fact. Rewrite `this` using `[Nat.cast_mul, norm_mul, mul_comm]`. Then use the resulting hypothesis.

Apply `hsub` to reduce the goal to its premises. Use `⟨hs1 ⟨h1 a.1 fun w => lt_of_lt_of_le (hi w).1 (min_le_left _ _), ?_⟩, hs2 ⟨h2 b.1 fun w => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `: a.2 = 1 + (N1 : Af F) * za` using `by rw [← heqa]; ring`. Rewrite using `[this]`. Conclude with `hN1W za hza`.

Use `show ‖b.1 w - 0‖ < ε2 w`. Rewrite using `[sub_zero]`. Conclude with `lt_of_lt_of_le (hi w).2 (min_le_right _ _)`. Rewrite using `[heqb]`. Conclude with `hN2W zb hzb`.
-/
theorem basic (t : Set (AF F × AF F)) (ht : t ∈ 𝓝 ((1, 0) : AF F × AF F)) :
    ∃ ε : InfinitePlace F → ℝ, (∀ w, 0 < ε w) ∧ ∃ N : ℕ, N ≠ 0 ∧ ∀ a b : AF F,
      (∀ w, ‖a.1 w - 1‖ < ε w ∧ ‖b.1 w‖ < ε w) →
      (∀ v, ‖a.2 v - 1‖ ≤ ‖(N : v.adicCompletion F)‖ ∧ ‖b.2 v‖ ≤ ‖(N : v.adicCompletion F)‖) → (a, b) ∈ t := by
  obtain ⟨U1, hU1, U2, hU2, hsub⟩ := mem_nhds_prod_iff.1 ht
  have hU1' : U1 ∈ 𝓝 (((1 : Ainf F), (1 : Af F))) := hU1
  have hU2' : U2 ∈ 𝓝 (((0 : Ainf F), (0 : Af F))) := hU2
  obtain ⟨V1, hV1, W1, hW1, hs1⟩ := mem_nhds_prod_iff.1 hU1'
  obtain ⟨V2, hV2, W2, hW2, hs2⟩ := mem_nhds_prod_iff.1 hU2'
  have hW1' : (fun z : Af F => 1 + z) ⁻¹' W1 ∈ 𝓝 (0 : Af F) := by
    have : Tendsto (fun z : Af F => 1 + z) (𝓝 0) (𝓝 1) := by
      have h := (continuous_const_add (1 : Af F)).tendsto 0
      rwa [add_zero] at h
    exact this hW1
  obtain ⟨N1, hN1, hN1W⟩ := finNhd _ hW1'
  obtain ⟨N2, hN2, hN2W⟩ := finNhd _ hW2
  have hinf : ∀ (V : Set (∀ w : InfinitePlace F, w.Completion)) (x : ∀ w : InfinitePlace F, w.Completion),
      V ∈ 𝓝 x → ∃ ε : InfinitePlace F → ℝ, (∀ w, 0 < ε w) ∧
      ∀ y : ∀ w : InfinitePlace F, w.Completion, (∀ w, ‖y w - x w‖ < ε w) → y ∈ V := by
    intro V x hV'
    rw [nhds_pi, Filter.mem_pi] at hV'
    obtain ⟨I, -, s, hs, hIs⟩ := hV'
    have h1 : ∀ w, ∃ ε > 0, ∀ y : w.Completion, ‖y - x w‖ < ε → y ∈ s w := fun w => by
      obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 (hs w)
      exact ⟨ε, hε, fun y hy => hb (by rw [Metric.mem_ball, dist_eq_norm]; exact hy)⟩
    choose ε hε hεs using h1
    exact ⟨ε, hε, fun y hy => hIs fun w _ => hεs w (y w) (hy w)⟩
  obtain ⟨ε1, hε1, h1⟩ := hinf V1 1 hV1
  obtain ⟨ε2, hε2, h2⟩ := hinf V2 0 hV2
  refine ⟨fun w => min (ε1 w) (ε2 w), fun w => lt_min (hε1 w) (hε2 w), N1 * N2,
    mul_ne_zero (by omega) (by omega), fun a b hi hf => ?_⟩
  obtain ⟨za, hza, heqa⟩ := int_of_le (a.2 - 1) N1 N2 (by omega) fun v => by
    have := (hf v).1; rwa [Nat.cast_mul, norm_mul] at this
  obtain ⟨zb, hzb, heqb⟩ := int_of_le b.2 N2 N1 (by omega) fun v => by
    have := (hf v).2; rwa [Nat.cast_mul, norm_mul, mul_comm] at this
  apply hsub
  refine ⟨hs1 ⟨h1 a.1 fun w => lt_of_lt_of_le (hi w).1 (min_le_left _ _), ?_⟩,
    hs2 ⟨h2 b.1 fun w => ?_, ?_⟩⟩
  · have : a.2 = 1 + (N1 : Af F) * za := by rw [← heqa]; ring
    rw [this]; exact hN1W za hza
  · show ‖b.1 w - 0‖ < ε2 w
    rw [sub_zero]; exact lt_of_lt_of_le (hi w).2 (min_le_right _ _)
  · rw [heqb]; exact hN2W zb hzb

/- English proof (translation)
Establish `hopen : IsOpen {y : InfiniteAdeleRing F | ∀ w, ‖y w - t w‖ < ηi w / 2}`. Rewrite using `[Set.ofPred_forall]`. Conclude with `isOpen_iInter_of_finite fun w => isOpen_lt (((continuous_apply w : Continuous fun y : InfiniteAdeleRing F => y w).sub continuous_const).norm) continuous_const`. Take `⟨f, hf⟩` from `(InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hopen ⟨(t : InfiniteAdeleRing F), fun w => by show ‖t w - t w‖ < ηi w / 2`. Rewrite using `[sub_self, norm_zero]`.

Conclude with `half_pos (hηi w)⟩`. Establish `hf' : ∀ w, ‖algebraMap F w.Completion f - t w‖ < ηi w / 2` using `hf`. Use `set M : ℕ := ∏ v ∈ S, Ideal.absNorm v.asIdeal with hMdef`. Establish `hM0 : M ≠ 0`. Rewrite using `[hMdef, Finset.prod_ne_zero_iff]`.

Introduce `v _`. Conclude with `(lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'`. Establish `hM1 : (1 : ℝ) ≤ M` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 hM0`. Establish `hMv : ∀ v ∈ S, ‖(M : v.adicCompletion F)‖ < 1` using `fun v hv => norm_natCast_lt_one' v M (Finset.dvd_prod_of_mem _ hv)`. Establish `hev : ∀ v ∈ (S : Set (HeightOneSpectrum (𝓞 F))), ∀ᶠ k in atTop, ‖(M : v.adicCompletion F)‖ ^ k < ηf v / 2` using `fun v hv => (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hMv v hv)).eventually (Iio_mem_nhds (half_pos (hηf v)))`.

Take `⟨k, hk⟩` from `((Filter.eventually_all_finite S.finite_toSet).2 hev).exists`. Set `b : Af F` to `RestrictedProduct.mk (fun v => if v ∈ S then (s v - algebraMap F (v.adicCompletion F) f) * ((M : v.adicCompletion F) ^ k)⁻¹ else 0) (by filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv`. Simplify using `only [Set.mem_compl_iff, Finset.mem_coe] at hv`. Rewrite using `[if_neg hv]`. Conclude with `zero_mem _)`.

Take `⟨u, hu⟩` from `ReciprocityTheory.UG.AdeleIntA.exists_approx_adele b`. Use `set g : F := (M : F) ^ k * u with hg`. Establish `hgS : ∀ v ∈ S, ‖algebraMap F (v.adicCompletion F) (f + g) - s v‖ < ηf v / 2`. Introduce `v hv`. Establish `hMk : (M : v.adicCompletion F) ^ k ≠ 0` using `pow_ne_zero _ (nat_ne_zero_fin v hM0)`.

Establish `hbv : b v = (s v - algebraMap F (v.adicCompletion F) f) * ((M : v.adicCompletion F) ^ k)⁻¹` using `by show (if v ∈ S then _ else _) = _`. Rewrite using `[if_pos hv]`. Establish `huv : b v - algebraMap F (v.adicCompletion F) u ∈ v.adicCompletionIntegers F` using `hu v`. Establish `e : algebraMap F (v.adicCompletion F) (f + g) - s v = -((M : v.adicCompletion F) ^ k * (b v - algebraMap F (v.adicCompletion F) u))`. Rewrite using `[hbv, hg, map_add, map_mul, map_pow, map_natCast]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_neg, norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hev2 : ∀ v ∈ (S : Set (HeightOneSpectrum (𝓞 F))), ∀ᶠ j in atTop, ‖algebraMap F (v.adicCompletion F) g‖ * ‖(M : v.adicCompletion F)‖ ^ j < ηf v / 2` using `fun v hv => by`.

Use `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hMv v hv)).const_mul ‖algebraMap F (v.adicCompletion F) g‖` as an intermediate fact. Rewrite `this` using `[mul_zero]`. Conclude with `this.eventually (Iio_mem_nhds (half_pos (hηf v)))`. Take `⟨j, hj1, hj⟩` from `((eventually_ge_atTop 1).and ((Filter.eventually_all_finite S.finite_toSet).2 hev2)).exists`. Use `set n : ℕ := ∑ w : InfinitePlace F, ⌈2 * ‖algebraMap F w.Completion g‖ / ηi w⌉₊ with hn`.

Establish `hnw : ∀ w, 2 * ‖algebraMap F w.Completion g‖ / ηi w ≤ n` using `fun w => by`. Use `(Nat.le_ceil _).trans ?_` and prove the remaining obligations. Rewrite using `[hn]`. Conclude with `Finset.single_le_sum (f := fun w : InfinitePlace F => ⌈2 * ‖algebraMap F w.Completion g‖ / ηi w⌉₊) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)` after adjusting the coercions. Use `set m : ℕ := 1 + M ^ j * n with hm`.

Establish `hm0 : (m : F) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Use `⟨f + g * (m : F)⁻¹, fun w => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hmw : ‖algebraMap F w.Completion ((m : F)⁻¹)‖ = (m : ℝ)⁻¹`. Rewrite using `[map_inv₀, norm_inv, norm_nat_inf]`. Establish `hgw : ‖algebraMap F w.Completion g‖ * (m : ℝ)⁻¹ < ηi w / 2`.

Establish `hmpos : (0 : ℝ) < m` using `by exact_mod_cast (show 0 < m by omega)`. Rewrite using `[← div_eq_mul_inv, div_lt_iff₀ hmpos]`. Establish `h1` using `hnw w`. Rewrite `h1` using `[div_le_iff₀ (hηi w)]`. Establish `hMj : (1 : ℝ) ≤ (M : ℝ) ^ j` using `one_le_pow₀ hM1`.

Establish `hmc : (m : ℝ) = 1 + (M : ℝ) ^ j * n` using `by rw [hm]; push_cast; ring`. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `h3 : (n : ℝ) ≤ (M : ℝ) ^ j * n` using `le_mul_of_one_le_left hn0 hMj`. Rewrite using `[hmc]`. Use polynomial arithmetic with `[hηi w]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_add, map_mul]`. Put the polynomial expressions in normal form. Use `_ ≤ ‖algebraMap F w.Completion f - t w‖ + ‖algebraMap F w.Completion g‖ * (m : ℝ)⁻¹ := by`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, hmw]`. Use `_ < ηi w / 2 + ηi w / 2 := add_lt_add (hf' w) hgw`. Use `_ = ηi w := by ring`. Establish `hMn : ‖((M ^ j * n : ℕ) : v.adicCompletion F)‖ < 1`. Rewrite using `[Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hmv : ‖(m : v.adicCompletion F)‖ = 1`. Rewrite using `[hm, Nat.cast_add, Nat.cast_one, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hMn.ne'), norm_one]`. Conclude with `max_eq_left hMn.le`. Establish `hm0v : (m : v.adicCompletion F) ≠ 0`.

Introduce `h`. Rewrite `hmv` using `[h, norm_zero]`. Conclude with `zero_ne_one hmv`. Establish `he1 : ‖algebraMap F (v.adicCompletion F) ((m : F)⁻¹) - 1‖ ≤ ‖(M : v.adicCompletion F)‖ ^ j`. Establish `e : algebraMap F (v.adicCompletion F) ((m : F)⁻¹) - 1 = -((m : v.adicCompletion F)⁻¹ * ((M ^ j * n : ℕ) : v.adicCompletion F))`.

Rewrite using `[map_inv₀, map_natCast, hm]`. Establish `: ((1 + M ^ j * n : ℕ) : v.adicCompletion F) ≠ 0` using `by rw [← hm]; exact hm0v`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, norm_neg, norm_mul, norm_inv, hmv, inv_one, one_mul, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_add, map_add, map_mul]`. Put the polynomial expressions in normal form.

Use `_ ≤ ‖algebraMap F (v.adicCompletion F) (f + g) - s v‖ + ‖algebraMap F (v.adicCompletion F) g‖ * ‖(M : v.adicCompletion F)‖ ^ j := by`. Use `(norm_add_le _ _).trans (add_le_add le_rfl ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left he1 (norm_nonneg _)`. Use `_ < ηf v / 2 + ηf v / 2 := add_lt_add (hgS v hv) (hj v hv)`.

Use `_ = ηf v := by ring`.
-/
theorem weakApprox (S : Finset (HeightOneSpectrum (𝓞 F))) (t : ∀ w : InfinitePlace F, w.Completion)
    (s : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ηi : InfinitePlace F → ℝ) (hηi : ∀ w, 0 < ηi w) (ηf : HeightOneSpectrum (𝓞 F) → ℝ) (hηf : ∀ v, 0 < ηf v) :
    ∃ c : F, (∀ w, ‖algebraMap F w.Completion c - t w‖ < ηi w) ∧
      ∀ v ∈ S, ‖algebraMap F (v.adicCompletion F) c - s v‖ < ηf v := by
  classical

  have hopen : IsOpen {y : InfiniteAdeleRing F | ∀ w, ‖y w - t w‖ < ηi w / 2} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (((continuous_apply w : Continuous fun y : InfiniteAdeleRing F => y w).sub
        continuous_const).norm) continuous_const
  obtain ⟨f, hf⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hopen
    ⟨(t : InfiniteAdeleRing F), fun w => by
      show ‖t w - t w‖ < ηi w / 2
      rw [sub_self, norm_zero]; exact half_pos (hηi w)⟩
  have hf' : ∀ w, ‖algebraMap F w.Completion f - t w‖ < ηi w / 2 := hf

  set M : ℕ := ∏ v ∈ S, Ideal.absNorm v.asIdeal with hMdef
  have hM0 : M ≠ 0 := by
    rw [hMdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hM0
  have hMv : ∀ v ∈ S, ‖(M : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one' v M (Finset.dvd_prod_of_mem _ hv)

  have hev : ∀ v ∈ (S : Set (HeightOneSpectrum (𝓞 F))), ∀ᶠ k in atTop,
      ‖(M : v.adicCompletion F)‖ ^ k < ηf v / 2 := fun v hv =>
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hMv v hv)).eventually
      (Iio_mem_nhds (half_pos (hηf v)))
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite S.finite_toSet).2 hev).exists
  let b : Af F := RestrictedProduct.mk
    (fun v => if v ∈ S then (s v - algebraMap F (v.adicCompletion F) f) * ((M : v.adicCompletion F) ^ k)⁻¹ else 0)
    (by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hv
      rw [if_neg hv]; exact zero_mem _)
  obtain ⟨u, hu⟩ := ReciprocityTheory.UG.AdeleIntA.exists_approx_adele b
  set g : F := (M : F) ^ k * u with hg
  have hgS : ∀ v ∈ S, ‖algebraMap F (v.adicCompletion F) (f + g) - s v‖ < ηf v / 2 := by
    intro v hv
    have hMk : (M : v.adicCompletion F) ^ k ≠ 0 := pow_ne_zero _ (nat_ne_zero_fin v hM0)
    have hbv : b v = (s v - algebraMap F (v.adicCompletion F) f) * ((M : v.adicCompletion F) ^ k)⁻¹ := by
      show (if v ∈ S then _ else _) = _
      rw [if_pos hv]
    have huv : b v - algebraMap F (v.adicCompletion F) u ∈ v.adicCompletionIntegers F := hu v
    have e : algebraMap F (v.adicCompletion F) (f + g) - s v =
        -((M : v.adicCompletion F) ^ k * (b v - algebraMap F (v.adicCompletion F) u)) := by
      rw [hbv, hg, map_add, map_mul, map_pow, map_natCast]
      field_simp
      ring
    rw [e, norm_neg, norm_mul, norm_pow]
    calc ‖(M : v.adicCompletion F)‖ ^ k * ‖b v - algebraMap F (v.adicCompletion F) u‖
        ≤ ‖(M : v.adicCompletion F)‖ ^ k * 1 :=
          mul_le_mul_of_nonneg_left ((norm_le_one_iff_int v _).2 huv) (pow_nonneg (norm_nonneg _) _)
      _ < ηf v / 2 := by rw [mul_one]; exact hk v hv

  have hev2 : ∀ v ∈ (S : Set (HeightOneSpectrum (𝓞 F))), ∀ᶠ j in atTop,
      ‖algebraMap F (v.adicCompletion F) g‖ * ‖(M : v.adicCompletion F)‖ ^ j < ηf v / 2 := fun v hv => by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hMv v hv)).const_mul
      ‖algebraMap F (v.adicCompletion F) g‖
    rw [mul_zero] at this
    exact this.eventually (Iio_mem_nhds (half_pos (hηf v)))
  obtain ⟨j, hj1, hj⟩ := ((eventually_ge_atTop 1).and ((Filter.eventually_all_finite S.finite_toSet).2 hev2)).exists
  set n : ℕ := ∑ w : InfinitePlace F, ⌈2 * ‖algebraMap F w.Completion g‖ / ηi w⌉₊ with hn
  have hnw : ∀ w, 2 * ‖algebraMap F w.Completion g‖ / ηi w ≤ n := fun w => by
    refine (Nat.le_ceil _).trans ?_
    rw [hn]
    exact_mod_cast Finset.single_le_sum (f := fun w : InfinitePlace F => ⌈2 * ‖algebraMap F w.Completion g‖ / ηi w⌉₊)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
  set m : ℕ := 1 + M ^ j * n with hm
  have hm0 : (m : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨f + g * (m : F)⁻¹, fun w => ?_, fun v hv => ?_⟩
  · have hmw : ‖algebraMap F w.Completion ((m : F)⁻¹)‖ = (m : ℝ)⁻¹ := by
      rw [map_inv₀, norm_inv, norm_nat_inf]
    have hgw : ‖algebraMap F w.Completion g‖ * (m : ℝ)⁻¹ < ηi w / 2 := by
      have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      rw [← div_eq_mul_inv, div_lt_iff₀ hmpos]
      have h1 := hnw w
      rw [div_le_iff₀ (hηi w)] at h1
      have hMj : (1 : ℝ) ≤ (M : ℝ) ^ j := one_le_pow₀ hM1
      have hmc : (m : ℝ) = 1 + (M : ℝ) ^ j * n := by rw [hm]; push_cast; ring
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h3 : (n : ℝ) ≤ (M : ℝ) ^ j * n := le_mul_of_one_le_left hn0 hMj
      rw [hmc]
      nlinarith [hηi w]
    calc ‖algebraMap F w.Completion (f + g * (m : F)⁻¹) - t w‖
        = ‖(algebraMap F w.Completion f - t w) + algebraMap F w.Completion g * algebraMap F w.Completion ((m : F)⁻¹)‖ := by
          rw [map_add, map_mul]; ring_nf
      _ ≤ ‖algebraMap F w.Completion f - t w‖ + ‖algebraMap F w.Completion g‖ * (m : ℝ)⁻¹ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, hmw]
      _ < ηi w / 2 + ηi w / 2 := add_lt_add (hf' w) hgw
      _ = ηi w := by ring
  · have hMn : ‖((M ^ j * n : ℕ) : v.adicCompletion F)‖ < 1 := by
      rw [Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
      calc ‖(M : v.adicCompletion F)‖ ^ j * ‖(n : v.adicCompletion F)‖ ≤ ‖(M : v.adicCompletion F)‖ ^ j * 1 :=
            mul_le_mul_of_nonneg_left (norm_nat_le_one v n) (pow_nonneg (norm_nonneg _) _)
        _ = ‖(M : v.adicCompletion F)‖ ^ j := mul_one _
        _ ≤ ‖(M : v.adicCompletion F)‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (hMv v hv).le hj1
        _ = ‖(M : v.adicCompletion F)‖ := pow_one _
        _ < 1 := hMv v hv
    have hmv : ‖(m : v.adicCompletion F)‖ = 1 := by
      rw [hm, Nat.cast_add, Nat.cast_one, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hMn.ne'),
        norm_one]
      exact max_eq_left hMn.le
    have hm0v : (m : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h, norm_zero] at hmv; exact zero_ne_one hmv
    have he1 : ‖algebraMap F (v.adicCompletion F) ((m : F)⁻¹) - 1‖ ≤ ‖(M : v.adicCompletion F)‖ ^ j := by
      have e : algebraMap F (v.adicCompletion F) ((m : F)⁻¹) - 1 =
          -((m : v.adicCompletion F)⁻¹ * ((M ^ j * n : ℕ) : v.adicCompletion F)) := by
        rw [map_inv₀, map_natCast, hm]
        have : ((1 + M ^ j * n : ℕ) : v.adicCompletion F) ≠ 0 := by rw [← hm]; exact hm0v
        field_simp
        push_cast
        ring
      rw [e, norm_neg, norm_mul, norm_inv, hmv, inv_one, one_mul, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
      calc ‖(M : v.adicCompletion F)‖ ^ j * ‖(n : v.adicCompletion F)‖ ≤ ‖(M : v.adicCompletion F)‖ ^ j * 1 :=
            mul_le_mul_of_nonneg_left (norm_nat_le_one v n) (pow_nonneg (norm_nonneg _) _)
        _ = ‖(M : v.adicCompletion F)‖ ^ j := mul_one _
    calc ‖algebraMap F (v.adicCompletion F) (f + g * (m : F)⁻¹) - s v‖
        = ‖(algebraMap F (v.adicCompletion F) (f + g) - s v) +
            algebraMap F (v.adicCompletion F) g * (algebraMap F (v.adicCompletion F) ((m : F)⁻¹) - 1)‖ := by
          rw [map_add, map_add, map_mul]; ring_nf
      _ ≤ ‖algebraMap F (v.adicCompletion F) (f + g) - s v‖ +
            ‖algebraMap F (v.adicCompletion F) g‖ * ‖(M : v.adicCompletion F)‖ ^ j := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left he1 (norm_nonneg _)
      _ < ηf v / 2 + ηf v / 2 := add_lt_add (hgS v hv) (hj v hv)
      _ = ηf v := by ring

end Formalism.IndefR.Fin.U1

end

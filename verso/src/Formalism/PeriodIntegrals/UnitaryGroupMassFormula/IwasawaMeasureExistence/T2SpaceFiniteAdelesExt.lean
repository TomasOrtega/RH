import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.SecondCountableOfOpenSubgroups

noncomputable section

namespace PI.IwaMeasEx.AfT

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct
open Formalism.MainNotions.S

section Fin

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap F (Af F)) N, FiniteAdeleRing.algebraMap_apply]`. Conclude with `map_natCast (algebraMap F (v.adicCompletion F)) N`.
-/
theorem natCast_apply (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (N : Af F) v = (N : v.adicCompletion F) := by
  rw [← map_natCast (algebraMap F (Af F)) N, FiniteAdeleRing.algebraMap_apply]
  exact map_natCast (algebraMap F (v.adicCompletion F)) N

/- English proof (translation)
Rewrite using `[← natCast_apply]`. Both sides reduce to the same expression.
-/
theorem natCast_mul_apply (N : ℕ) (z : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    ((N : Af F) * z) v = (N : v.adicCompletion F) * z v := by
  rw [← natCast_apply]
  rfl

/- English proof (translation)
Establish `hmem : (c : 𝓞 F) ∈ v.asIdeal`. Take `⟨k, hk⟩` from `hc`. Rewrite using `[hk, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)`. Establish `hval` using `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (c : 𝓞 F)).2 hmem`.

Rewrite using `[Valued.toNormedField.norm_lt_one_iff]`. Establish `e : (c : v.adicCompletion F) = (((algebraMap (𝓞 F) F (c : 𝓞 F)) : F) : v.adicCompletion F)`. Rewrite using `[map_natCast]`. Rewrite using `[show (((c : F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (c : F) from rfl, map_natCast]`. Rewrite using `[e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.

Conclude with `hval`.
-/
theorem norm_natCast_lt_one (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
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
The claim follows from `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((Valued.toNormedField.norm_le_one_iff).1 h)`.
-/
theorem mem_int_of_norm_le_one (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (h : ‖x‖ ≤ 1) :
    x ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((Valued.toNormedField.norm_le_one_iff).1 h)

/- English proof (translation)
The claim follows from `(Valued.toNormedField.norm_le_one_iff).2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h)`.
-/
theorem norm_le_one_of_mem_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : x ∈ v.adicCompletionIntegers F) : ‖x‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h)

/- English proof (translation)
Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ x v ∈ v.adicCompletionIntegers F}.Finite` using `Filter.eventually_cofinite.1 x.2`. Use `set S := hfin.toFinset with hS`. Use `set c : ℕ := ∏ v ∈ S, Ideal.absNorm v.asIdeal with hcdef`. Establish `hc0 : c ≠ 0`. Rewrite using `[hcdef, Finset.prod_ne_zero_iff]`.

Introduce `v _`. Conclude with `(lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'`. Establish `hcv : ∀ v ∈ S, ‖(c : v.adicCompletion F)‖ < 1` using `fun v hv => norm_natCast_lt_one F v c (Finset.dvd_prod_of_mem _ hv)`. Establish `hev : ∀ v ∈ S, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k * ‖x v‖ < 1`. Introduce `v hv`.

Establish `ht` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).mul_const ‖x v‖`. Rewrite `ht` using `[zero_mul]`. Conclude with `ht.eventually (Iio_mem_nhds one_pos)`. Take `⟨k, hk⟩` from `((Filter.eventually_all_finset S).2 hev).exists`. Use `⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun v => ?_⟩` and prove the remaining obligations.

Use `show ((((c ^ k : ℕ)) : Af F) * x) v ∈ v.adicCompletionIntegers F`. Rewrite using `[natCast_mul_apply]`. Distinguish the cases in `hv : v ∈ S`. Apply `mem_int_of_norm_le_one` to reduce the goal to its premises. Rewrite using `[norm_mul, Nat.cast_pow, norm_pow]`.

Conclude with `(hk v hv).le`. Establish `hxv : x v ∈ v.adicCompletionIntegers F`. Rewrite `hv` using `[hS, Set.Finite.mem_toFinset]`. Simplify using `using hv`. Conclude with `mul_mem (natCast_mem _ _) hxv`.
-/
theorem exists_nat_mul_intAd (x : Af F) : ∃ N : ℕ, 1 ≤ N ∧ (N : Af F) * x ∈ Formalism.UG.intAd F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ x v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 x.2
  set S := hfin.toFinset with hS
  set c : ℕ := ∏ v ∈ S, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ S, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one F v c (Finset.dvd_prod_of_mem _ hv)
  have hev : ∀ v ∈ S, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k * ‖x v‖ < 1 := by
    intro v hv
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).mul_const ‖x v‖
    rw [zero_mul] at ht
    exact ht.eventually (Iio_mem_nhds one_pos)
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finset S).2 hev).exists
  refine ⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun v => ?_⟩
  show ((((c ^ k : ℕ)) : Af F) * x) v ∈ v.adicCompletionIntegers F
  rw [natCast_mul_apply]
  by_cases hv : v ∈ S
  · apply mem_int_of_norm_le_one
    rw [norm_mul, Nat.cast_pow, norm_pow]
    exact (hk v hv).le
  · have hxv : x v ∈ v.adicCompletionIntegers F := by
      rw [hS, Set.Finite.mem_toFinset] at hv
      simpa using hv
    exact mul_mem (natCast_mem _ _) hxv

/- English proof (translation)
Use extensionality with `v`. It suffices to establish `key : x v = 0 by rw [key]; rfl`. Use `set p : ℕ := Ideal.absNorm v.asIdeal`. Establish `hp1 : 1 ≤ p` using `(NumberField.HeightOneSpectrum.one_lt_absNorm v).le`. Establish `hp : ‖(p : v.adicCompletion F)‖ < 1` using `norm_natCast_lt_one F v p dvd_rfl`.

Establish `hle : ∀ k : ℕ, ‖x v‖ ≤ ‖(p : v.adicCompletion F)‖ ^ k`. Introduce `k`. Take `⟨z, hz, hxz⟩` from `h (p ^ k) (Nat.one_le_pow _ _ hp1)`. Establish `e : x v = ((p ^ k : ℕ) : v.adicCompletion F) * z v`. Rewrite using `[hxz, natCast_mul_apply]`.

Rewrite using `[e, norm_mul, Nat.cast_pow, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : ‖x v‖ ≤ 0` using `ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp) hle`. Conclude with `norm_le_zero_iff.1 h0`.
-/
theorem eq_zero_of_forall_mem (x : Af F)
    (h : ∀ N : ℕ, 1 ≤ N → ∃ z ∈ Formalism.UG.intAd F, x = (N : Af F) * z) : x = 0 := by
  ext v
  suffices key : x v = 0 by rw [key]; rfl
  set p : ℕ := Ideal.absNorm v.asIdeal
  have hp1 : 1 ≤ p := (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hp : ‖(p : v.adicCompletion F)‖ < 1 := norm_natCast_lt_one F v p dvd_rfl
  have hle : ∀ k : ℕ, ‖x v‖ ≤ ‖(p : v.adicCompletion F)‖ ^ k := by
    intro k
    obtain ⟨z, hz, hxz⟩ := h (p ^ k) (Nat.one_le_pow _ _ hp1)
    have e : x v = ((p ^ k : ℕ) : v.adicCompletion F) * z v := by
      rw [hxz, natCast_mul_apply]
    rw [e, norm_mul, Nat.cast_pow, norm_pow]
    calc ‖(p : v.adicCompletion F)‖ ^ k * ‖z v‖ ≤ ‖(p : v.adicCompletion F)‖ ^ k * 1 :=
          mul_le_mul_of_nonneg_left (norm_le_one_of_mem_int F v _ (hz v)) (pow_nonneg (norm_nonneg _) _)
      _ = _ := mul_one _
  have h0 : ‖x v‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp) hle
  exact norm_le_zero_iff.1 h0

end Fin

/- English proof (translation)
Take `⟨y, hy, h⟩` from `exists_integral_multiples ℤ ℚ s`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hi : IsIntegral ℤ ((y.natAbs : E) * x)`. Establish `hyx` using `h x hx`. Rewrite `hyx` using `[zsmul_eq_mul]`.

Rewrite using `[← Int.cast_natCast, Int.natCast_natAbs]`. Break down `abs_choice y with h' | h'` into its components or cases. Rewrite using `[h']`. Conclude with `hyx`. Rewrite using `[h', Int.cast_neg, neg_mul]`.

Conclude with `hyx.neg`. Take `⟨a, ha⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hi`. Conclude with `⟨a, ha⟩`.
-/
theorem exists_nat_den {E : Type} [Field E] [NumberField E] (s : Finset E) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ x ∈ s, (d : E) * x ∈ Formalism.UG.intOE E := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun x hx => ?_⟩
  have hi : IsIntegral ℤ ((y.natAbs : E) * x) := by
    have hyx := h x hx
    rw [zsmul_eq_mul] at hyx
    rw [← Int.cast_natCast, Int.natCast_natAbs]
    rcases abs_choice y with h' | h'
    · rw [h']; exact hyx
    · rw [h', Int.cast_neg, neg_mul]; exact hyx.neg
  obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hi
  exact ⟨a, ha⟩

variable (I : AutInst)

abbrev AEf : Type := I.E ⊗[I.F] Af I.F

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)`.
-/
theorem inclE_mem_IntAf {x : I.E} (hx : x ∈ Formalism.UG.intOE I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) x ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)`.
-/
theorem includeRight_mem_IntAf {a : Af I.F} (ha : a ∈ Formalism.UG.intAd I.F) :
    (Algebra.TensorProduct.includeRight a : AEf I) ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

/- English proof (translation)
Simplify using `[Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]`.
-/
theorem tmul_eq (e : I.E) (a : Af I.F) :
    (e ⊗ₜ[I.F] a : AEf I) = Formalism.UG.inclE (F := I.F) (Af I.F) e * Algebra.TensorProduct.includeRight a := by
  simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]

/- English proof (translation)
The claim follows from `mul_mem (natCast_mem _ N) hy`.
-/
theorem natCast_mul_mem {N : ℕ} {y : AEf I} (hy : y ∈ IntAf I.F I.E) : (N : AEf I) * y ∈ IntAf I.F I.E :=
  mul_mem (natCast_mem _ N) hy

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, le_rfl, by rw [mul_zero]; exact zero_mem _⟩`. Consider the case `tmul e a`. Take `⟨d, hd, hde⟩` from `exists_nat_den (E := I.E) {e}`. Take `⟨M, hM, hMa⟩` from `exists_nat_mul_intAd I.F a`.

Use `⟨d * M, Nat.mul_pos hd hM, ?_⟩` and prove the remaining obligations. Establish `h1` using `inclE_mem_IntAf I (hde e (Finset.mem_singleton_self e))`. Establish `h2` using `includeRight_mem_IntAf I hMa`. Rewrite `h1` using `[map_mul, map_natCast]`. Rewrite `h2` using `[map_mul, map_natCast]`.

Rewrite using `[tmul_eq]`. Establish `e' : ((d * M : ℕ) : AEf I) * (Formalism.UG.inclE (F` using `I.F) (Af I.F) e * Algebra.TensorProduct.includeRight a) = ((d : AEf I) * Formalism.UG.inclE (F := I.F) (Af I.F) e) * ((M : AEf I) * Algebra.TensorProduct.includeRight a) := by push_cast; ring`. Rewrite using `[e']`. Conclude with `mul_mem h1 h2`. Consider the case `add s t hs ht`.

Take `⟨N1, h1, hs⟩` from `hs`. Take `⟨N2, h2, ht⟩` from `ht`. Use `⟨N1 * N2, Nat.mul_pos h1 h2, ?_⟩` and prove the remaining obligations. Establish `e' : ((N1 * N2 : ℕ) : AEf I) * (s + t) = (N2 : AEf I) * ((N1 : AEf I) * s) + (N1 : AEf I) * ((N2 : AEf I) * t)` using `by push_cast; ring`. Rewrite using `[e']`.

Conclude with `add_mem (natCast_mul_mem I hs) (natCast_mul_mem I ht)`.
-/
theorem exists_nat_mul_mem (t : AEf I) : ∃ N : ℕ, 1 ≤ N ∧ (N : AEf I) * t ∈ IntAf I.F I.E := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, le_rfl, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e a =>
    obtain ⟨d, hd, hde⟩ := exists_nat_den (E := I.E) {e}
    obtain ⟨M, hM, hMa⟩ := exists_nat_mul_intAd I.F a
    refine ⟨d * M, Nat.mul_pos hd hM, ?_⟩
    have h1 := inclE_mem_IntAf I (hde e (Finset.mem_singleton_self e))
    have h2 := includeRight_mem_IntAf I hMa
    rw [map_mul, map_natCast] at h1
    rw [map_mul, map_natCast] at h2
    rw [tmul_eq]
    have e' : ((d * M : ℕ) : AEf I) * (Formalism.UG.inclE (F := I.F) (Af I.F) e * Algebra.TensorProduct.includeRight a) =
        ((d : AEf I) * Formalism.UG.inclE (F := I.F) (Af I.F) e) * ((M : AEf I) * Algebra.TensorProduct.includeRight a) := by
      push_cast; ring
    rw [e']
    exact mul_mem h1 h2
  | add s t hs ht =>
    obtain ⟨N1, h1, hs⟩ := hs
    obtain ⟨N2, h2, ht⟩ := ht
    refine ⟨N1 * N2, Nat.mul_pos h1 h2, ?_⟩
    have e' : ((N1 * N2 : ℕ) : AEf I) * (s + t) = (N2 : AEf I) * ((N1 : AEf I) * s) + (N1 : AEf I) * ((N2 : AEf I) * t) := by
      push_cast; ring
    rw [e']
    exact add_mem (natCast_mul_mem I hs) (natCast_mul_mem I ht)

def bsub (N : ℕ) : AddSubgroup (AEf I) :=
  (IntAf I.F I.E).toAddSubgroup.map (AddMonoidHom.mulLeft (N : AEf I))

/- English proof (translation)
Simplify using `[bsub]`.
-/
theorem mem_bsub {N : ℕ} {x : AEf I} : x ∈ bsub I N ↔ ∃ z ∈ IntAf I.F I.E, (N : AEf I) * z = x := by
  simp [bsub]

/- English proof (translation)
Introduce `x hx`. Take `⟨k, rfl⟩` from `h`. Take `⟨z, hz, rfl⟩` from `(mem_bsub I).1 hx`. Use `(mem_bsub I).2 ⟨(k : AEf I) * z, natCast_mul_mem I hz, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bsub_mul_le {N M : ℕ} (h : M ∣ N) : bsub I N ≤ bsub I M := by
  intro x hx
  obtain ⟨k, rfl⟩ := h
  obtain ⟨z, hz, rfl⟩ := (mem_bsub I).1 hx
  refine (mem_bsub I).2 ⟨(k : AEf I) * z, natCast_mul_mem I hz, ?_⟩
  push_cast; ring

def bas (k : ℕ) : AddSubgroup (AEf I) := bsub I (k + 1)

/- English proof (translation)
Use `RingSubgroupsBasis.of_comm (bas I) ?_ ?_ ?_` and prove the remaining obligations. Introduce `i j`. Use `⟨(i + 1) * (j + 1) - 1, le_inf ?_ ?_⟩` and prove the remaining obligations. Apply `bsub_mul_le; rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity))]` to reduce the goal to its premises. Conclude with `dvd_mul_right _ _`.

Apply `bsub_mul_le; rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity))]` to reduce the goal to its premises. Conclude with `dvd_mul_left _ _`. Introduce `i`. Use `⟨i, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, y, hy, rfl⟩`.

Take `⟨z, hz, rfl⟩` from `(mem_bsub I).1 hx`. Take `⟨w, hw, rfl⟩` from `(mem_bsub I).1 hy`. Use `(mem_bsub I).2 ⟨z * (((i + 1 : ℕ) : AEf I) * w), mul_mem hz (natCast_mul_mem I hw), ?_⟩` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Introduce `x i`.

Take `⟨N, hN, hx⟩` from `exists_nat_mul_mem I x`. Use `⟨(i + 1) * N - 1, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hpos : 1 ≤ (i + 1) * N` using `Nat.mul_pos (Nat.succ_pos i) hN`. Express the relevant statement in the definitionally equal form `y ∈ bsub I ((i + 1) * N - 1 + 1) at hy`.

Rewrite `hy` using `[Nat.sub_add_cancel hpos]`. Take `⟨z, hz, rfl⟩` from `(mem_bsub I).1 hy`. Use `show x * (((i + 1) * N : ℕ) * z) ∈ bsub I (i + 1)`. Use `(mem_bsub I).2 ⟨((N : AEf I) * x) * z, mul_mem hx hz, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ringSubgroupsBasis_bas : RingSubgroupsBasis (bas I) := by
  refine RingSubgroupsBasis.of_comm (bas I) ?_ ?_ ?_
  · intro i j
    refine ⟨(i + 1) * (j + 1) - 1, le_inf ?_ ?_⟩
    · apply bsub_mul_le; rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity))]
      exact dvd_mul_right _ _
    · apply bsub_mul_le; rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity))]
      exact dvd_mul_left _ _
  · intro i
    refine ⟨i, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (mem_bsub I).1 hx
    obtain ⟨w, hw, rfl⟩ := (mem_bsub I).1 hy
    refine (mem_bsub I).2 ⟨z * (((i + 1 : ℕ) : AEf I) * w), mul_mem hz (natCast_mul_mem I hw), ?_⟩
    ring
  · intro x i
    obtain ⟨N, hN, hx⟩ := exists_nat_mul_mem I x
    refine ⟨(i + 1) * N - 1, ?_⟩
    intro y hy
    have hpos : 1 ≤ (i + 1) * N := Nat.mul_pos (Nat.succ_pos i) hN
    change y ∈ bsub I ((i + 1) * N - 1 + 1) at hy
    rw [Nat.sub_add_cancel hpos] at hy
    obtain ⟨z, hz, rfl⟩ := (mem_bsub I).1 hy
    show x * (((i + 1) * N : ℕ) * z) ∈ bsub I (i + 1)
    refine (mem_bsub I).2 ⟨((N : AEf I) * x) * z, mul_mem hx hz, ?_⟩
    push_cast; ring

@[instance_reducible] def tAf : TopologicalSpace (AEf I) := (ringSubgroupsBasis_bas I).topology

/- English proof (translation)
The claim follows from `(ringSubgroupsBasis_bas I).hasBasis_nhds_zero`.
-/
theorem hasBasis_nhds_zero_tAf :
    HasBasis (@nhds (AEf I) (tAf I) 0) (fun _ => True) fun k => (bas I k : Set (AEf I)) :=
  (ringSubgroupsBasis_bas I).hasBasis_nhds_zero

/- English proof (translation)
The claim follows from `(ringSubgroupsBasis_bas I).hasBasis_nhds a`.
-/
theorem hasBasis_nhds_tAf (a : AEf I) :
    HasBasis (@nhds (AEf I) (tAf I) a) (fun _ => True) fun k => {b | b - a ∈ bas I k} :=
  (ringSubgroupsBasis_bas I).hasBasis_nhds a

/- English proof (translation)
The claim follows from `RingFilterBasis.isTopologicalRing _`.
-/
theorem isTopologicalRing_tAf : @IsTopologicalRing (AEf I) (tAf I) _ :=
  RingFilterBasis.isTopologicalRing _

section T2

variable {ι : Type} [Fintype ι] (b : Module.Basis ι I.F I.E)

def crd (j : ι) : AEf I →ₗ[I.F] Af I.F :=
  (TensorProduct.lid I.F (Af I.F)).toLinearMap ∘ₗ (b.coord j).rTensor (Af I.F)

/- English proof (translation)
Simplify using `[crd, Module.Basis.coord_apply]`.
-/
theorem crd_tmul (j : ι) (x : I.E) (a : Af I.F) : crd I b j (x ⊗ₜ[I.F] a) = b.repr x j • a := by
  simp [crd, Module.Basis.coord_apply]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x a`. Simplify using `only [crd_tmul, TensorProduct.tmul_smul]`. Use `conv_lhs => rw [← b.sum_repr x]`.

Rewrite using `[TensorProduct.sum_tmul]`. Simplify using `only [TensorProduct.smul_tmul']`. Consider the case `add s t hs ht`. Simplify using `only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]`. Rewrite using `[← hs, ← ht]`.
-/
theorem sum_crd (t : AEf I) : t = ∑ j, b j ⊗ₜ[I.F] crd I b j t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    simp only [crd_tmul, TensorProduct.tmul_smul]
    conv_lhs => rw [← b.sum_repr x]
    rw [TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul']
  | add s t hs ht =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hs, ← ht]

/- English proof (translation)
Use `set eb := NumberField.RingOfIntegers.basis I.E`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ ((Finset.univ : Finset (_ × ι)).image (fun p => b.repr ((eb p.1 : 𝓞 I.E) : I.E) p.2))`. Use `⟨y.natAbs, Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hy0), ?_⟩` and prove the remaining obligations. Establish `hint : ∀ c : I.F, IsIntegral ℤ (y • c) → IsIntegral ℤ ((y.natAbs : I.F) * c)`. Introduce `c hc`.

Break down `Int.natAbs_eq y with h | h` into its components or cases. Establish `: ((y.natAbs : ℤ) : I.F) * c = y • c` using `by rw [← h, zsmul_eq_mul]`. Rewrite using `[← Int.cast_natCast, this]`. Conclude with `hc`. Establish `: ((y.natAbs : ℤ) : I.F) * c = -(y • c)`.

Rewrite using `[zsmul_eq_mul]`. Use `conv_rhs => rw [h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Int.cast_natCast, this]`.

Conclude with `hc.neg`. Establish `gen : ∀ i j, ∃ r : 𝓞 I.F, (y.natAbs : I.F) * b.repr ((eb i : 𝓞 I.E) : I.E) j = algebraMap (𝓞 I.F) I.F r`. Introduce `i j`. Establish `hm` using `hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))`. Conclude with `⟨⟨_, hint _ hm⟩, rfl⟩`.

Introduce `o`. Establish `ho : o ∈ Submodule.span ℤ (Set.range eb)` using `by rw [eb.span_eq]; exact Submodule.mem_top`. Proceed by induction on `ho using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`.

Conclude with `gen i`. Consider the case `zero`. Introduce `j`. Conclude with `⟨0, by simp⟩`. Consider the case `add x y' _ _ hx hy'`.

Introduce `j`. Take `⟨r, hr⟩` from `hx j`. Take `⟨r', hr'⟩` from `hy' j`. Use `⟨r + r', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← hr, ← hr']`.

Use `push_cast`. Rewrite using `[map_add, Finsupp.add_apply, mul_add]`. Consider the case `smul a x _ hx`. Introduce `j`. Take `⟨r, hr⟩` from `hx j`.

Use `⟨a • r, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zsmul, ← hr]`. Establish `e : ((a • x : 𝓞 I.E) : I.E) = a • (x : I.E)` using `by push_cast; rfl`. Rewrite using `[e, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_denom : ∃ D : ℕ, 1 ≤ D ∧ ∀ o : 𝓞 I.E, ∀ j : ι,
    ∃ r : 𝓞 I.F, (D : I.F) * b.repr (o : I.E) j = algebraMap (𝓞 I.F) I.F r := by
  classical
  set eb := NumberField.RingOfIntegers.basis I.E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (_ × ι)).image (fun p => b.repr ((eb p.1 : 𝓞 I.E) : I.E) p.2))
  refine ⟨y.natAbs, Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hy0), ?_⟩
  have hint : ∀ c : I.F, IsIntegral ℤ (y • c) → IsIntegral ℤ ((y.natAbs : I.F) * c) := by
    intro c hc
    rcases Int.natAbs_eq y with h | h
    · have : ((y.natAbs : ℤ) : I.F) * c = y • c := by rw [← h, zsmul_eq_mul]
      rw [← Int.cast_natCast, this]
      exact hc
    · have : ((y.natAbs : ℤ) : I.F) * c = -(y • c) := by
        rw [zsmul_eq_mul]
        conv_rhs => rw [h]
        push_cast
        ring
      rw [← Int.cast_natCast, this]
      exact hc.neg
  have gen : ∀ i j, ∃ r : 𝓞 I.F,
      (y.natAbs : I.F) * b.repr ((eb i : 𝓞 I.E) : I.E) j = algebraMap (𝓞 I.F) I.F r := by
    intro i j
    have hm := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
    exact ⟨⟨_, hint _ hm⟩, rfl⟩
  intro o
  have ho : o ∈ Submodule.span ℤ (Set.range eb) := by rw [eb.span_eq]; exact Submodule.mem_top
  induction ho using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact gen i
  | zero =>
    intro j
    exact ⟨0, by simp⟩
  | add x y' _ _ hx hy' =>
    intro j
    obtain ⟨r, hr⟩ := hx j
    obtain ⟨r', hr'⟩ := hy' j
    refine ⟨r + r', ?_⟩
    rw [map_add, ← hr, ← hr']
    push_cast
    rw [map_add, Finsupp.add_apply, mul_add]
  | smul a x _ hx =>
    intro j
    obtain ⟨r, hr⟩ := hx j
    refine ⟨a • r, ?_⟩
    rw [map_zsmul, ← hr]
    have e : ((a • x : 𝓞 I.E) : I.E) = a • (x : I.E) := by push_cast; rfl
    rw [e, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, zsmul_eq_mul]
    ring

end T2

def sumsInt : AddSubgroup (AEf I) :=
  AddSubgroup.closure {x | ∃ o ∈ Formalism.UG.intOE I.E, ∃ a ∈ Formalism.UG.intAd I.F, x = o ⊗ₜ[I.F] a}

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨o, ho, a, ha, rfl⟩` from `hx`.

Take `⟨o', ho', a', ha', rfl⟩` from `hy`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Conclude with `AddSubgroup.subset_closure ⟨_, mul_mem ho ho', _, mul_mem ha ha', rfl⟩`. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`.

Consider the case `add y y' _ _ h h' => rw [mul_add]`. Conclude with `add_mem h h'`. Consider the case `neg y _ h => rw [mul_neg]`. Conclude with `neg_mem h`. Consider the case `zero => rw [zero_mul]`.

Conclude with `zero_mem _`. Consider the case `add x x' _ _ h h' => rw [add_mul]`. Conclude with `add_mem h h'`. Consider the case `neg x _ h => rw [neg_mul]`. Conclude with `neg_mem h`.
-/
theorem sumsInt_mul {x y : AEf I} (hx : x ∈ sumsInt I) (hy : y ∈ sumsInt I) : x * y ∈ sumsInt I := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨o, ho, a, ha, rfl⟩ := hx
      obtain ⟨o', ho', a', ha', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨_, mul_mem ho ho', _, mul_mem ha ha', rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | neg y _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | neg x _ h => rw [neg_mul]; exact neg_mem h

/- English proof (translation)
Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨o, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Conclude with `AddSubgroup.subset_closure ⟨o, o.2, 1, one_mem _, rfl⟩`. Conclude with `AddSubgroup.subset_closure ⟨1, one_mem _, a, a.2, rfl⟩`.

Consider the case `zero => exact zero_mem _`. Consider the case `one => exact AddSubgroup.subset_closure ⟨1, one_mem _, 1, one_mem _, rfl⟩`. Consider the case `add x y _ _ h h' => exact add_mem h h'`. Consider the case `neg x _ h => exact neg_mem h`. Consider the case `mul x y _ _ h h' => exact sumsInt_mul I h h'`.
-/
theorem IntAf_le_sumsInt {x : AEf I} (hx : x ∈ IntAf I.F I.E) : x ∈ sumsInt I := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨o, rfl⟩ | ⟨a, rfl⟩
    · exact AddSubgroup.subset_closure ⟨o, o.2, 1, one_mem _, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, one_mem _, a, a.2, rfl⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, one_mem _, 1, one_mem _, rfl⟩
  | add x y _ _ h h' => exact add_mem h h'
  | neg x _ h => exact neg_mem h
  | mul x y _ _ h h' => exact sumsInt_mul I h h'

/- English proof (translation)
Introduce `v`. Conclude with `HeightOneSpectrum.coe_algebraMap_mem (𝓞 I.F) I.F v r`.
-/
theorem algebraMap_mem_intAd (r : 𝓞 I.F) :
    algebraMap I.F (Af I.F) (algebraMap (𝓞 I.F) I.F r) ∈ Formalism.UG.intAd I.F := by
  intro v
  exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 I.F) I.F v r

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨o, ⟨o', rfl⟩, a, ha, rfl⟩` from `hx`. Take `⟨r, hr⟩` from `hD o' j`. Rewrite using `[crd_tmul, Algebra.smul_def, ← mul_assoc, ← map_natCast (algebraMap I.F _) D, ← map_mul]`.

Establish `e : (algebraMap (𝓞 I.E) I.E o') = (o' : I.E)` using `rfl`. Rewrite using `[e, hr]`. Conclude with `mul_mem (algebraMap_mem_intAd I r) ha`. Consider the case `zero => rw [map_zero, mul_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ h h' => rw [map_add, mul_add]`. Conclude with `add_mem h h'`. Consider the case `neg x _ h => rw [map_neg, mul_neg]`. Conclude with `neg_mem h`.
-/
theorem crd_mem {ι : Type} [Fintype ι] (b : Module.Basis ι I.F I.E) {D : ℕ} (hD : ∀ o : 𝓞 I.E, ∀ j : ι,
    ∃ r : 𝓞 I.F, (D : I.F) * b.repr (o : I.E) j = algebraMap (𝓞 I.F) I.F r)
    {x : AEf I} (hx : x ∈ sumsInt I) (j : ι) :
    (D : Af I.F) * crd I b j x ∈ Formalism.UG.intAd I.F := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨o, ⟨o', rfl⟩, a, ha, rfl⟩ := hx
    obtain ⟨r, hr⟩ := hD o' j
    rw [crd_tmul, Algebra.smul_def, ← mul_assoc, ← map_natCast (algebraMap I.F _) D, ← map_mul]
    have e : (algebraMap (𝓞 I.E) I.E o') = (o' : I.E) := rfl
    rw [e, hr]
    exact mul_mem (algebraMap_mem_intAd I r) ha
  | zero => rw [map_zero, mul_zero]; exact zero_mem _
  | add x y _ _ h h' => rw [map_add, mul_add]; exact add_mem h h'
  | neg x _ h => rw [map_neg, mul_neg]; exact neg_mem h

/- English proof (translation)
Set `b` to `Module.finBasis I.F I.E`. Take `⟨D, hD1, hD⟩` from `exists_denom I b`. Establish `hc : ∀ j, crd I b j t = 0`. Introduce `j`. Apply `eq_zero_of_forall_mem I.F` to reduce the goal to its premises.

Introduce `N hN`. Take `⟨s, hs, hst⟩` from `(mem_bsub I).1 (h (N * D) (Nat.mul_pos hN hD1))`. Use `⟨(D : Af I.F) * crd I b j s, crd_mem I b hD (IntAf_le_sumsInt I hs) j, ?_⟩` and prove the remaining obligations. Rewrite using `[← hst, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sum_crd I b t]`. Simplify using `[hc]`.
-/
theorem eq_zero_of_forall_bsub (t : AEf I) (h : ∀ N : ℕ, 1 ≤ N → t ∈ bsub I N) : t = 0 := by
  classical
  let b := Module.finBasis I.F I.E
  obtain ⟨D, hD1, hD⟩ := exists_denom I b
  have hc : ∀ j, crd I b j t = 0 := by
    intro j
    apply eq_zero_of_forall_mem I.F
    intro N hN
    obtain ⟨s, hs, hst⟩ := (mem_bsub I).1 (h (N * D) (Nat.mul_pos hN hD1))
    refine ⟨(D : Af I.F) * crd I b j s, crd_mem I b hD (IntAf_le_sumsInt I hs) j, ?_⟩
    rw [← hst, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    push_cast
    ring
  rw [sum_crd I b t]
  simp [hc]

/- English proof (translation)
Use `letI := tAf I`. Use `haveI := isTopologicalRing_tAf I`. Apply `IsTopologicalAddGroup.t2Space_of_zero_sep` to reduce the goal to its premises. Introduce `x hx`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Apply `hx` to reduce the goal to its premises. Apply `eq_zero_of_forall_bsub I x` to reduce the goal to its premises. Introduce `N hN`. Take `⟨k, rfl⟩ : ∃ k, N = k + 1` from `⟨N - 1, by omega⟩`.

Conclude with `hcon _ ((hasBasis_nhds_zero_tAf I).mem_of_mem trivial)`.
-/
theorem t2Space_finite_adeles_ext : @T2Space (AEf I) (tAf I) := by
  letI := tAf I
  haveI := isTopologicalRing_tAf I
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  by_contra hcon
  push_neg at hcon
  apply hx
  apply eq_zero_of_forall_bsub I x
  intro N hN
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  exact hcon _ ((hasBasis_nhds_zero_tAf I).mem_of_mem trivial)

/- English proof (translation)
Establish `h0 : (c : I.F) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Use `h0.isUnit.map (algebraMap I.F (AEf I))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem isUnit_natCast (c : ℕ) (hc : 1 ≤ c) : IsUnit (c : AEf I) := by
  have h0 : (c : I.F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have := h0.isUnit.map (algebraMap I.F (AEf I))
  rwa [map_natCast] at this

end PI.IwaMeasEx.AfT

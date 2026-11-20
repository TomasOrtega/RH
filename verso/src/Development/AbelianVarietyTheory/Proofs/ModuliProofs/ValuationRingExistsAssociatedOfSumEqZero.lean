import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialMapMaximalIdealIsPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfFlatOfFormallyUnramified

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Take `⟨i, hi, h⟩` from `valuationRing_exists_dvd_all f s hs`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `choose! c hc using h`. Establish `hm : ∀ j ∈ s.erase i, c j ∈ IsLocalRing.maximalIdeal V`.

Introduce `j hj`. Take `⟨hji, hj⟩` from `Finset.mem_erase.1 hj`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Conclude with `hcon i hi j hj hji.symm ⟨hu.unit, by simp [hc j hj]⟩`.

Establish `h1 : f i * (1 + ∑ j ∈ s.erase i, c j) = 0`. Rewrite using `[← hsum, ← Finset.add_sum_erase s f hi, mul_add, mul_one, Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j hj => (hc j (Finset.mem_of_mem_erase hj)).symm`. Establish `h2` using `(mul_eq_zero.1 h1).resolve_left (h0 i hi)`.

Establish `h3 : (1 : V) ∈ IsLocalRing.maximalIdeal V`. Rewrite using `[eq_neg_of_add_eq_zero_left h2]`. Conclude with `neg_mem (Ideal.sum_mem _ hm)`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 h3)`.
-/
theorem valuationRing_exists_associated_of_sum_eq_zero {V ι : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] (f : ι → V) (s : Finset ι) (hs : s.Nonempty) (h0 : ∀ i ∈ s, f i ≠ 0)
    (hsum : ∑ i ∈ s, f i = 0) : ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ Associated (f i) (f j) := by
  classical
  obtain ⟨i, hi, h⟩ := valuationRing_exists_dvd_all f s hs
  by_contra hcon
  push Not at hcon
  choose! c hc using h
  have hm : ∀ j ∈ s.erase i, c j ∈ IsLocalRing.maximalIdeal V := by
    intro j hj
    obtain ⟨hji, hj⟩ := Finset.mem_erase.1 hj
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hcon i hi j hj hji.symm ⟨hu.unit, by simp [hc j hj]⟩
  have h1 : f i * (1 + ∑ j ∈ s.erase i, c j) = 0 := by
    rw [← hsum, ← Finset.add_sum_erase s f hi, mul_add, mul_one, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j hj => (hc j (Finset.mem_of_mem_erase hj)).symm
  have h2 := (mul_eq_zero.1 h1).resolve_left (h0 i hi)
  have h3 : (1 : V) ∈ IsLocalRing.maximalIdeal V := by
    rw [eq_neg_of_add_eq_zero_left h2]
    exact neg_mem (Ideal.sum_mem _ hm)
  exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 h3)

/- English proof (translation)
Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap O K c) hk`. Establish `hint : IsIntegral O z` using `IsIntegral.of_pow hk (hz ▸ isIntegral_algebraMap)`. Take `⟨r, rfl⟩` from `(IsIntegrallyClosed.isIntegral_iff (K := K)).1 hint`. Conclude with `⟨r, IsFractionRing.injective O K (by rw [map_pow, hz])⟩`.
-/
theorem valuationRing_exists_pow_eq (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (c : O) {k : ℕ} (hk : 0 < k) :
    ∃ r : O, r ^ k = c := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O K c) hk
  have hint : IsIntegral O z := IsIntegral.of_pow hk (hz ▸ isIntegral_algebraMap)
  obtain ⟨r, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).1 hint
  exact ⟨r, IsFractionRing.injective O K (by rw [map_pow, hz])⟩

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_lt hij`. Establish `h1 : Associated (φ p) (φ q * b ^ (k + 1))`. Use `Associated.of_mul_right (b := b ^ i) (d := b ^ i) ?_ (Associated.refl _) (pow_ne_zero _ hb)` and prove the remaining obligations. Establish `e : φ q * b ^ (k + 1) * b ^ i = φ q * b ^ (i + k + 1)` using `by ring`. Rewrite using `[e]` and apply the resulting hypothesis.

Break down `ValuationRing.dvd_total p q with ⟨c, rfl⟩ | ⟨c, rfl⟩` into its components or cases. Establish `h2 : Associated 1 (φ c * b ^ (k + 1))`. Use `Associated.of_mul_left (a := φ p) (c := φ p) ?_ (Associated.refl _) hp` and prove the remaining obligations. Rewrite using `[mul_one, ← mul_assoc, ← map_mul]` and apply the resulting hypothesis. Establish `h3 : IsUnit (b ^ (k + 1))` using `isUnit_of_mul_isUnit_right (associated_one_iff_isUnit.1 h2.symm)`.

Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, associated_one_iff_isUnit]`. Conclude with `(isUnit_pow_iff (Nat.succ_ne_zero k)).1 h3`. Establish `h2 : Associated (φ c) (b ^ (k + 1))`. Use `Associated.of_mul_left (a := φ q) (c := φ q) ?_ (Associated.refl _) hq` and prove the remaining obligations.

Rewrite using `[← map_mul]` and apply the resulting hypothesis. Take `⟨r, rfl⟩` from `valuationRing_exists_pow_eq O K c (Nat.succ_pos k)`. Rewrite `h2` using `[map_pow]`. Conclude with `⟨r, ((Associated.pow_iff (Nat.succ_ne_zero k)).1 h2).symm⟩`.
-/
theorem associated_of_associated_mul_pow (O K V : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K]
    [CommRing V] [IsDomain V] [ValuationRing V] (φ : O →+* V) (b : V) (hb : b ≠ 0) (p q : O)
    {i j : ℕ} (hij : i < j) (hp : φ p ≠ 0) (hq : φ q ≠ 0)
    (h : Associated (φ p * b ^ i) (φ q * b ^ j)) : ∃ π : O, Associated b (φ π) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have h1 : Associated (φ p) (φ q * b ^ (k + 1)) := by
    refine Associated.of_mul_right (b := b ^ i) (d := b ^ i) ?_ (Associated.refl _)
      (pow_ne_zero _ hb)
    have e : φ q * b ^ (k + 1) * b ^ i = φ q * b ^ (i + k + 1) := by ring
    rwa [e]
  rcases ValuationRing.dvd_total p q with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have h2 : Associated 1 (φ c * b ^ (k + 1)) := by
      refine Associated.of_mul_left (a := φ p) (c := φ p) ?_ (Associated.refl _) hp
      rwa [mul_one, ← mul_assoc, ← map_mul]
    have h3 : IsUnit (b ^ (k + 1)) := isUnit_of_mul_isUnit_right (associated_one_iff_isUnit.1 h2.symm)
    refine ⟨1, ?_⟩
    rw [map_one, associated_one_iff_isUnit]
    exact (isUnit_pow_iff (Nat.succ_ne_zero k)).1 h3
  · have h2 : Associated (φ c) (b ^ (k + 1)) := by
      refine Associated.of_mul_left (a := φ q) (c := φ q) ?_ (Associated.refl _) hq
      rwa [← map_mul]
    obtain ⟨r, rfl⟩ := valuationRing_exists_pow_eq O K c (Nat.succ_pos k)
    rw [map_pow] at h2
    exact ⟨r, ((Associated.pow_iff (Nat.succ_ne_zero k)).1 h2).symm⟩

/- English proof (translation)
Take `⟨P, hP, hPb⟩` from `halg`. Rewrite `hPb` using `[Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]`. Take `⟨i, hi, j, hj, hij, h⟩` from `valuationRing_exists_associated_of_sum_eq_zero _ _ (Polynomial.support_nonempty.2 hP) (fun i hi => mul_ne_zero (hinj _ (Polynomial.mem_support_iff.1 hi)) (pow_ne_zero _ hb)) hPb`. Establish `hi'` using `Polynomial.mem_support_iff.1 hi`. Establish `hj'` using `Polynomial.mem_support_iff.1 hj`.

Take `⟨p, hp⟩` from `hW _ hi'`. Take `⟨q, hq⟩` from `hW _ hj'`. Establish `hp0` using `hinj _ (hp.ne_zero_iff.1 hi')`. Establish `hq0` using `hinj _ (hq.ne_zero_iff.1 hj')`. Establish `h' : Associated (algebraMap W V (ψ p) * b ^ i) (algebraMap W V (ψ q) * b ^ j)` using `(((hp.map (algebraMap W V)).mul_right _).symm.trans h).trans ((hq.map (algebraMap W V)).mul_right _)`.

Break down `lt_or_gt_of_ne hij with hlt | hlt` into its components or cases. Conclude with `associated_of_associated_mul_pow O K V ((algebraMap W V).comp ψ) b hb p q hlt hp0 hq0 h'`. Conclude with `associated_of_associated_mul_pow O K V ((algebraMap W V).comp ψ) b hb q p hlt hq0 hp0 h'.symm`.
-/
theorem exists_associated_of_isAlgebraic (O K W V : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K]
    [CommRing W] [CommRing V] [IsDomain V] [ValuationRing V] [Algebra W V] (ψ : O →+* W)
    (hinj : ∀ w : W, w ≠ 0 → algebraMap W V w ≠ 0)
    (hW : ∀ w : W, w ≠ 0 → ∃ π : O, Associated w (ψ π)) (b : V) (hb : b ≠ 0)
    (halg : IsAlgebraic W b) : ∃ π : O, Associated b (algebraMap W V (ψ π)) := by
  obtain ⟨P, hP, hPb⟩ := halg
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum] at hPb
  obtain ⟨i, hi, j, hj, hij, h⟩ := valuationRing_exists_associated_of_sum_eq_zero _ _
    (Polynomial.support_nonempty.2 hP)
    (fun i hi => mul_ne_zero (hinj _ (Polynomial.mem_support_iff.1 hi)) (pow_ne_zero _ hb)) hPb
  have hi' := Polynomial.mem_support_iff.1 hi
  have hj' := Polynomial.mem_support_iff.1 hj
  obtain ⟨p, hp⟩ := hW _ hi'
  obtain ⟨q, hq⟩ := hW _ hj'
  have hp0 := hinj _ (hp.ne_zero_iff.1 hi')
  have hq0 := hinj _ (hq.ne_zero_iff.1 hj')
  have h' : Associated (algebraMap W V (ψ p) * b ^ i) (algebraMap W V (ψ q) * b ^ j) :=
    (((hp.map (algebraMap W V)).mul_right _).symm.trans h).trans
      ((hq.map (algebraMap W V)).mul_right _)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact associated_of_associated_mul_pow O K V ((algebraMap W V).comp ψ) b hb p q hlt hp0 hq0 h'
  · exact associated_of_associated_mul_pow O K V ((algebraMap W V).comp ψ) b hb q p hlt hq0 hp0
      h'.symm

/- English proof (translation)
Establish `hm : IsSMulRegular (A ⧸ Ideal.span {t}) u`. Rewrite using `[isSMulRegular_iff_right_eq_zero_of_smul]`. Introduce `y hy`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`.

Apply `h` to reduce the goal to its premises. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hy`. Establish `hJ : ∀ y : B, algebraMap A B t ∣ y ↔ y ∈ (Ideal.span {t}).map (algebraMap A B)`. Introduce `y`.

Rewrite using `[Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]`. Rewrite `hx`, the goal using `[hJ]`. Establish `h` using `hm.lTensor B`. Set `e` to `Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (Ideal.span {t})`. Rewrite `hx`, the goal using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `h` to reduce the goal to its premises. Establish `h2` using `congrArg e hx`. Rewrite `h2` using `[map_zero]`.

Simplify using `only [smul_zero]`. Rewrite using `[← h2, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, TensorProduct.smul_tmul', Algebra.smul_def]`.
-/
theorem dvd_of_dvd_mul_of_flat {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (t u : A) (h : ∀ F : A, t ∣ u * F → t ∣ F) (x : B)
    (hx : algebraMap A B t ∣ algebraMap A B u * x) : algebraMap A B t ∣ x := by
  have hm : IsSMulRegular (A ⧸ Ideal.span {t}) u := by
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro y hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    apply h
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    exact hy
  have hJ : ∀ y : B, algebraMap A B t ∣ y ↔ y ∈ (Ideal.span {t}).map (algebraMap A B) := by
    intro y
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  rw [hJ] at hx ⊢
  have h := hm.lTensor B
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (Ideal.span {t})
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  apply e.injective
  rw [map_zero]
  apply h
  have h2 := congrArg e hx
  rw [map_zero] at h2
  simp only [smul_zero]
  rw [← h2, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, TensorProduct.smul_tmul',
    Algebra.smul_def]

/- English proof (translation)
Take `⟨P, hP, _, hl⟩` from `Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := (p.map (algebraMap A B)).under A) (p.map (algebraMap A B)) Ideal.le_comap_map`. Establish `: P = p.map (algebraMap A B)` using `le_antisymm hP (Ideal.map_le_iff_le_comap.2 hl.over.le)`. Conclude with `this ▸ hl`.
-/
theorem map_liesOver_of_flat_of_isPrime {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (p : Ideal A) [p.IsPrime] [(p.map (algebraMap A B)).IsPrime] :
    (p.map (algebraMap A B)).LiesOver p := by
  obtain ⟨P, hP, _, hl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p)
    (q := (p.map (algebraMap A B)).under A) (p.map (algebraMap A B)) Ideal.le_comap_map
  have : P = p.map (algebraMap A B) :=
    le_antisymm hP (Ideal.map_le_iff_le_comap.2 hl.over.le)
  exact this ▸ hl

/- English proof (translation)
Take `⟨⟨a, u⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl w`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `hw (IsLocalization.mk'_zero _)`. Take `⟨π, F, rfl, hF⟩` from `mvPolynomial_exists_content O g a ha`.

Use `⟨π, ?_⟩` and prove the remaining obligations. Rewrite `hF` using `[← hp]`. Establish `hu : IsUnit (IsLocalization.mk' (Localization.AtPrime p) F u)` using `(IsLocalization.AtPrime.isUnit_mk'_iff _ p F u).2 hF`. Simplify using `only`. Rewrite using `[← IsLocalization.mul_mk'_eq_mk'_of_mul]`.

Conclude with `(associated_mul_unit_left _ _ hu)`.
-/
theorem gaussLocalization_exists_associated (O : Type) [CommRing O] [IsDomain O] [ValuationRing O]
    (g : ℕ) (p : Ideal (MvPolynomial (Fin g) O)) [p.IsPrime]
    (hp : p = (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O))
    (w : Localization.AtPrime p) (hw : w ≠ 0) :
    ∃ π : O, Associated w (algebraMap _ (Localization.AtPrime p)
      (MvPolynomial.C π : MvPolynomial (Fin g) O)) := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl w
  have ha : a ≠ 0 := by
    rintro rfl
    exact hw (IsLocalization.mk'_zero _)
  obtain ⟨π, F, rfl, hF⟩ := mvPolynomial_exists_content O g a ha
  refine ⟨π, ?_⟩
  rw [← hp] at hF
  have hu : IsUnit (IsLocalization.mk' (Localization.AtPrime p) F u) :=
    (IsLocalization.AtPrime.isUnit_mk'_iff _ p F u).2 hF
  simp only
  rw [← IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact (associated_mul_unit_left _ _ hu)

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ _ g B _ _ _ _ _ _ hη b hb`. Take `⟨hpp, -, hcanc⟩` from `mvPolynomial_content_valuationRing O g`. Use `set p := (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) with hp`. Establish `hC : ∀ π : O, algebraMap (MvPolynomial (Fin g) O) B (MvPolynomial.C π) = algebraMap O B π` using `fun π => (IsScalarTower.algebraMap_apply O (MvPolynomial (Fin g) O) B π).symm`. Establish `hηp : (IsLocalRing.maximalIdeal O).map (algebraMap O B) = p.map (algebraMap (MvPolynomial (Fin g) O) B)`.

Rewrite using `[hp, Ideal.map_map]`. Use `congr 1`. Conclude with `RingHom.ext fun π => (hC π).symm`. Rewrite `hη`, the goal using `[hηp]`. Use `set η := p.map (algebraMap (MvPolynomial (Fin g) O) B) with hηdef`.

Establish `hlo : η.LiesOver p` using `map_liesOver_of_flat_of_isPrime p`. Establish `step1 : ∃ (π : O) (s t : B), s ∉ η ∧ t ∉ η ∧ s * b = algebraMap O B π * t`. Set `` to `Localization.AtPrime.algebraOfLiesOver p η`. Establish `: Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime η)` using `.of_comp (MvPolynomial (Fin g) O) _ _`. Establish `: Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime η)` using `.of_restrictScalars (MvPolynomial (Fin g) O) _ _`.

Establish `hW` using `gaussLocalization_exists_associated O g p hp`. Establish `: ValuationRing (Localization.AtPrime p)`. Use `ValuationRing.iff_dvd_total.2 ⟨fun x y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Use `right`.

Rewrite using `[hx]`. Conclude with `dvd_zero _`. Distinguish the cases in `hy : y = 0`. Use `left`. Rewrite using `[hy]`.

Conclude with `dvd_zero _`. Take `⟨a, ha⟩` from `hW x hx`. Take `⟨c, hc⟩` from `hW y hy`. Break down `ValuationRing.dvd_total a c with h | h` into its components or cases. Use `left`.

Conclude with `(ha.dvd.trans (map_dvd _ (map_dvd _ h))).trans hc.symm.dvd`. Use `right`. Conclude with `(hc.dvd.trans (map_dvd _ (map_dvd _ h))).trans ha.symm.dvd`. Take `⟨hV, halg⟩` from `GlobalTheory.valuationRing_of_flat_of_formallyUnramified (Localization.AtPrime p) (Localization.AtPrime η)`. Establish `hBinj : Function.Injective (algebraMap B (Localization.AtPrime η))` using `IsLocalization.injective _ η.primeCompl_le_nonZeroDivisors`.

Take `⟨π, hπ⟩` from `exists_associated_of_isAlgebraic O K (Localization.AtPrime p) (Localization.AtPrime η) ((algebraMap (MvPolynomial (Fin g) O) (Localization.AtPrime p)).comp MvPolynomial.C) (fun w hw h0 => by`. Use `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Localization.AtPrime η) (mem_nonZeroDivisors_of_ne_zero hw)` as an intermediate fact. Conclude with `one_ne_zero (this.right_eq_zero_of_smul (by rw [Algebra.smul_def, h0, zero_mul])))`. Use `hW (algebraMap B _ b) (fun h => hb (hBinj (h.trans (map_zero _).symm)))`. Use the proof step `(halg.isAlgebraic _)`.

Rewrite `hπ` using `[RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (MvPolynomial (Fin g) O) B (Localization.AtPrime η), hC]`. Take `⟨v, hv⟩` from `hπ`. Take `⟨⟨s, t⟩, hst⟩` from `IsLocalization.mk'_surjective η.primeCompl (v : Localization.AtPrime η)`. Simplify using `only at hst`. Establish `hs : s ∈ η.primeCompl` using `(IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime η) η s t).1 (hst ▸ v.isUnit)`.

Use `⟨π, s, t, hs, t.2, hBinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← hv, ← hst, mul_assoc, IsLocalization.mk'_spec, mul_comm]`. Take `⟨π, s, t, hs, ht, hst⟩` from `step1`. Establish `step2 : algebraMap O B π ∣ b`. Distinguish the cases in `hu : IsUnit π`.

Conclude with `(hu.map _).dvd`. Establish `hs0 : s ≠ 0` using `fun h => hs (h ▸ η.zero_mem)`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hst` using `[map_zero, zero_mul]`.

Conclude with `mul_ne_zero hs0 hb hst`. Establish `hnd : ¬ Disjoint (Ideal.span {s, algebraMap O B π} : Set B) (p.primeCompl.map (algebraMap (MvPolynomial (Fin g) O) B) : Set B)`. Introduce `hd`. Take `⟨Q, hQ, hle, hdis⟩` from `Ideal.exists_le_prime_disjoint _ _ hd`. Establish `hsQ : s ∈ Q` using `hle (Ideal.subset_span (by simp))`.

Establish `hπQ : algebraMap O B π ∈ Q` using `hle (Ideal.subset_span (by simp))`. Establish `hmax : (Q.comap (algebraMap O B)).IsMaximal` using `Ring.DimensionLEOne.maximalOfPrime (fun h => hπ0 (by rw [← Ideal.mem_bot, ← h]; exact hπQ)) inferInstance`. Establish `hηQ : η ≤ Q`. Rewrite using `[← hηp, Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hmax]`. Establish `hunder : η.under (MvPolynomial (Fin g) O) = Q.under (MvPolynomial (Fin g) O)`.

Use `le_antisymm (Ideal.comap_mono hηQ) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← hlo.over]`. Assume the negation of the conclusion as `hxp`. Conclude with `Set.disjoint_left.1 hdis hx ⟨x, hxp, rfl⟩`. Use `Algebra.QuasiFinite.eq_of_le_of_under_eq η Q hηQ hunder` as an intermediate fact.

Conclude with `hs (this ▸ hsQ)`. Take `⟨_, hy, u, hu, rfl⟩` from `Set.not_disjoint_iff.1 hnd`. Take `⟨c, d, hcd⟩` from `Ideal.mem_span_pair.1 hy`. Rewrite using `[← hC]`. Use `dvd_of_dvd_mul_of_flat _ u (fun F => hcanc π u F hu) b ?_` and prove the remaining obligations.

Rewrite using `[hC]`. Use `⟨c * t + d * b, ?_⟩` and prove the remaining obligations. Rewrite using `[← hcd]`. Take the linear combination `c * hst`. Take `⟨b', rfl⟩` from `step2`.

Use `⟨π, b', rfl, fun hb' => ht ?_⟩` and prove the remaining obligations. Establish `: s * b' = t`. Apply `mul_left_cancel₀ (left_ne_zero_of_mul hb)` to reduce the goal to its premises. Rewrite using `[← hst]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← this]`. Conclude with `η.mul_mem_left _ hb'`.
-/
theorem etale_mvPolynomial_exists_content :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (g : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra (MvPolynomial (Fin g) O) B] [IsScalarTower O (MvPolynomial (Fin g) O) B] [Algebra.Etale (MvPolynomial (Fin g) O) B], ((IsLocalRing.maximalIdeal O).map (algebraMap O B)).IsPrime → ∀ b : B, b ≠ 0 → ∃ (π : O) (b' : B), b = algebraMap O B π * b' ∧ b' ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O B) := by
  intro O K _ _ _ _ _ _ _ _ g B _ _ _ _ _ _ hη b hb
  obtain ⟨hpp, -, hcanc⟩ := mvPolynomial_content_valuationRing O g
  set p := (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)
    with hp
  have hC : ∀ π : O, algebraMap (MvPolynomial (Fin g) O) B (MvPolynomial.C π)
      = algebraMap O B π := fun π =>
    (IsScalarTower.algebraMap_apply O (MvPolynomial (Fin g) O) B π).symm
  have hηp : (IsLocalRing.maximalIdeal O).map (algebraMap O B)
      = p.map (algebraMap (MvPolynomial (Fin g) O) B) := by
    rw [hp, Ideal.map_map]
    congr 1
    exact RingHom.ext fun π => (hC π).symm
  rw [hηp] at hη ⊢
  set η := p.map (algebraMap (MvPolynomial (Fin g) O) B) with hηdef
  have hlo : η.LiesOver p := map_liesOver_of_flat_of_isPrime p

  have step1 : ∃ (π : O) (s t : B), s ∉ η ∧ t ∉ η ∧ s * b = algebraMap O B π * t := by
    let := Localization.AtPrime.algebraOfLiesOver p η
    have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime η) :=
      .of_comp (MvPolynomial (Fin g) O) _ _
    have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime η) :=
      .of_restrictScalars (MvPolynomial (Fin g) O) _ _
    have hW := gaussLocalization_exists_associated O g p hp
    have : ValuationRing (Localization.AtPrime p) := by
      refine ValuationRing.iff_dvd_total.2 ⟨fun x y => ?_⟩
      by_cases hx : x = 0
      · right; rw [hx]; exact dvd_zero _
      by_cases hy : y = 0
      · left; rw [hy]; exact dvd_zero _
      obtain ⟨a, ha⟩ := hW x hx
      obtain ⟨c, hc⟩ := hW y hy
      rcases ValuationRing.dvd_total a c with h | h
      · left; exact (ha.dvd.trans (map_dvd _ (map_dvd _ h))).trans hc.symm.dvd
      · right; exact (hc.dvd.trans (map_dvd _ (map_dvd _ h))).trans ha.symm.dvd
    obtain ⟨hV, halg⟩ := GlobalTheory.valuationRing_of_flat_of_formallyUnramified (Localization.AtPrime p) (Localization.AtPrime η)
    have hBinj : Function.Injective (algebraMap B (Localization.AtPrime η)) :=
      IsLocalization.injective _ η.primeCompl_le_nonZeroDivisors
    obtain ⟨π, hπ⟩ := exists_associated_of_isAlgebraic O K (Localization.AtPrime p)
      (Localization.AtPrime η)
      ((algebraMap (MvPolynomial (Fin g) O) (Localization.AtPrime p)).comp MvPolynomial.C)
      (fun w hw h0 => by
        have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Localization.AtPrime η)
          (mem_nonZeroDivisors_of_ne_zero hw)
        exact one_ne_zero (this.right_eq_zero_of_smul (by rw [Algebra.smul_def, h0, zero_mul])))
      hW (algebraMap B _ b) (fun h => hb (hBinj (h.trans (map_zero _).symm)))
      (halg.isAlgebraic _)
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin g) O) B (Localization.AtPrime η), hC] at hπ
    obtain ⟨v, hv⟩ := hπ
    obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective η.primeCompl
      (v : Localization.AtPrime η)
    simp only at hst
    have hs : s ∈ η.primeCompl :=
      (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime η) η s t).1 (hst ▸ v.isUnit)
    refine ⟨π, s, t, hs, t.2, hBinj ?_⟩
    rw [map_mul, map_mul, ← hv, ← hst, mul_assoc, IsLocalization.mk'_spec, mul_comm]
  obtain ⟨π, s, t, hs, ht, hst⟩ := step1
  have step2 : algebraMap O B π ∣ b := by
    by_cases hu : IsUnit π
    · exact (hu.map _).dvd
    have hs0 : s ≠ 0 := fun h => hs (h ▸ η.zero_mem)
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hst
      exact mul_ne_zero hs0 hb hst
    have hnd : ¬ Disjoint (Ideal.span {s, algebraMap O B π} : Set B)
        (p.primeCompl.map (algebraMap (MvPolynomial (Fin g) O) B) : Set B) := by
      intro hd
      obtain ⟨Q, hQ, hle, hdis⟩ := Ideal.exists_le_prime_disjoint _ _ hd
      have hsQ : s ∈ Q := hle (Ideal.subset_span (by simp))
      have hπQ : algebraMap O B π ∈ Q := hle (Ideal.subset_span (by simp))
      have hmax : (Q.comap (algebraMap O B)).IsMaximal :=
        Ring.DimensionLEOne.maximalOfPrime
          (fun h => hπ0 (by rw [← Ideal.mem_bot, ← h]; exact hπQ)) inferInstance
      have hηQ : η ≤ Q := by
        rw [← hηp, Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hmax]
      have hunder : η.under (MvPolynomial (Fin g) O) = Q.under (MvPolynomial (Fin g) O) := by
        refine le_antisymm (Ideal.comap_mono hηQ) fun x hx => ?_
        rw [← hlo.over]
        by_contra hxp
        exact Set.disjoint_left.1 hdis hx ⟨x, hxp, rfl⟩
      have := Algebra.QuasiFinite.eq_of_le_of_under_eq η Q hηQ hunder
      exact hs (this ▸ hsQ)
    obtain ⟨_, hy, u, hu, rfl⟩ := Set.not_disjoint_iff.1 hnd
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.1 hy
    rw [← hC]
    refine dvd_of_dvd_mul_of_flat _ u (fun F => hcanc π u F hu) b ?_
    rw [hC]
    refine ⟨c * t + d * b, ?_⟩
    rw [← hcd]
    linear_combination c * hst
  obtain ⟨b', rfl⟩ := step2
  refine ⟨π, b', rfl, fun hb' => ht ?_⟩
  have : s * b' = t := by
    apply mul_left_cancel₀ (left_ne_zero_of_mul hb)
    rw [← hst]; ring
  rw [← this]
  exact η.mul_mem_left _ hb'

end GlobalTheory

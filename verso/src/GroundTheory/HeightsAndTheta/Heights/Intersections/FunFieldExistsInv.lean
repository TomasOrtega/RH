import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.IntCastMemRegMaxAt
import GroundTheory.HeightsAndTheta.Heights.Intersections.LeOfHeightMapEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite using `[eq_intCast C n, map_intCast, map_intCast]`. Simplify using the standard rewrite rules.
-/
theorem regRing_intCast_coe (P : Ideal (MRing ι)) (n : ℤ) :
    (((n : regRing P) : funField P) : FractionRing (MRing ι ⧸ P)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C n)) := by
  rw [eq_intCast C n, map_intCast, map_intCast]
  simp

/- English proof (translation)
Establish `hφ : ∀ s, s ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ≠ 0` using `fun s hs => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hs`. Establish `hFL : (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P P`. Establish `hx` using `y.2`. Unfold `funField at hx`. Unfold `locRing`.

Use `Subring.closure_mono ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨u, v, a, hv, hu, hva, rfl⟩`. Use `⟨u, v, a, hv, fun h => ?_, hu, hva, rfl⟩` and prove the remaining obligations. Establish `h0 : Ideal.Quotient.mk P v = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr h`. Conclude with `zero_notMem_nonZeroDivisors (h0 ▸ hv)`.

Take `⟨u, v, a, hu, hv, hvP, huv⟩` from `LocRingFrac.proof K ι P P hPp hPp le_rfl _ hFL`. Establish `huP : u ∉ P` using `fun h => by`. Establish `h0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]`. Rewrite `h0` using `[← huv]`.

Conclude with `mul_ne_zero hy (hφ v hvP) h0`. Take `⟨x, hx⟩` from `exists_funField_mul_eq hv hu huP`. Use `⟨x, mul_right_cancel₀ (hφ v hvP) ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, huv, hx, one_mul]`.
-/
theorem funField_exists_inv {P : Ideal (MRing ι)} [hPp : P.IsPrime] (y : funField P)
    (hy : (y : FractionRing (MRing ι ⧸ P)) ≠ 0) :
    ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) = 1 := by
  have hφ : ∀ s, s ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ≠ 0 :=
    fun s hs => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  have hFL : (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P P := by
    have hx := y.2
    unfold funField at hx
    unfold locRing
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
    refine ⟨u, v, a, hv, fun h => ?_, hu, hva, rfl⟩
    have h0 : Ideal.Quotient.mk P v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact zero_notMem_nonZeroDivisors (h0 ▸ hv)
  obtain ⟨u, v, a, hu, hv, hvP, huv⟩ := LocRingFrac.proof K ι P P hPp hPp le_rfl _ hFL
  have huP : u ∉ P := fun h => by
    have h0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
    rw [← huv] at h0
    exact mul_ne_zero hy (hφ v hvP) h0
  obtain ⟨x, hx⟩ := exists_funField_mul_eq hv hu huP
  refine ⟨x, mul_right_cancel₀ (hφ v hvP) ?_⟩
  rw [mul_assoc, huv, hx, one_mul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨y, hy⟩, rfl⟩`.
-/
theorem regRing_exists_coe {P : Ideal (MRing ι)} {y : funField P} (hy : y ∈ regRing P) :
    ∃ b : regRing P, (b : funField P) = y :=
  ⟨⟨y, hy⟩, rfl⟩

/- English proof (translation)
Introduce `K _ ι _ P hP m hm`. Establish `hPp : P.IsPrime` using `hP.2.1.1`. Establish `hL : LocRingLocal.Statement` using `LocRingLocal.proof LocRingFrac.proof`. Establish `hmZ : (m.comap (algebraMap ℤ (regRing P))).IsMaximal`. Establish `: Module.Finite ℤ (regRing P)` using `(h₁ K ι P hP).2.1`.

Establish `: Algebra.IsIntegral ℤ (regRing P)` using `Algebra.IsIntegral.of_finite ℤ _`. Conclude with `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m`. Establish `hp` using `Submodule.IsPrincipal.prime_generator_of_isPrime (is_prime := hmZ.isPrime) _ (Ring.ne_bot_of_isMaximal_of_not_isField hmZ Int.not_isField)`. Use `set p := Submodule.IsPrincipal.generator (m.comap (algebraMap ℤ (regRing P)))`. Establish `hZ : ∀ n : ℤ, (n : regRing P) ∈ m ↔ p ∣ n` using `fun n => by`.

Rewrite using `[← Submodule.IsPrincipal.mem_iff_generator_dvd, Ideal.mem_comap, algebraMap_int_eq, eq_intCast]`. Establish `hCp : C p ∉ P` using `fun h => by`. Establish `h' : p ∈ P.comap (C : ℤ →+* MRing ι)` using `h`. Rewrite `h'` using `[hP.2.2.1]`. Conclude with `hp.ne_zero (Ideal.mem_bot.mp h')`.

Establish `hp0 : (p : regRing P) ≠ 0` using `fun h => by`. Establish `h'` using `regRing_intCast_coe P p`. Rewrite `h'` using `[h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hCp h'`. Establish `hS : {W | IsClosedPt W ∧ P ≤ W ∧ C p ∈ W}.Finite` using `(divSupp_finite P (C p)).subset fun W hW => (RegularityDivisorSupportClosed.proof K ι P (C p) 0 W hP (RegularityDenominator.isMultiHomog_C p) hCp).2 hW`.

Set `g : Ideal (MRing ι) → Ideal (regRing P)` to `fun W => if h : IsClosedPt W ∧ P ≤ W then regMaxAt P W h.1 h.2 (hL K ι P W hPp h.1.1.1 h.2).1 else ⊥`. Establish `hgW : ∀ W (h : IsClosedPt W ∧ P ≤ W), g W = regMaxAt P W h.1 h.2 (hL K ι P W hPp h.1.1.1 h.2).1` using `fun W h => dif_pos h`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Set `T : Finset (Ideal (regRing P))` to `insert ⊥ (hS.toFinset.image g)`.

Establish `hT : ¬ ((m : Set (regRing P)) ⊆ ⋃ i ∈ (↑T : Set (Ideal (regRing P))), ((fun i => i) i : Set (regRing P)))`. Rewrite using `[Ideal.subset_union_prime (f := fun i : Ideal (regRing P) => i) ⊥ ⊥ fun i hi h1 _ => ?_]`. Introduce and unpack `⟨i, hi, hle⟩`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `hp0 (Ideal.mem_bot.1 (hle ((hZ p).2 dvd_rfl)))`.

Take `⟨W, hW, rfl⟩` from `Finset.mem_image.1 hi`. Take `⟨hWc, hPW, -⟩` from `hS.mem_toFinset.1 hW`. Take `⟨x, hx, z, hz, hxz⟩` from `hcon W hWc hPW`. Establish `h'` using `hle hx`. Rewrite `h'` using `[hgW W ⟨hWc, hPW⟩]`.

Conclude with `(not_mem_regMaxAt_iff hWc hPW _ x).2 ⟨z, hz, hxz⟩ h'`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `absurd rfl h1`. Take `⟨W, hW, rfl⟩` from `Finset.mem_image.1 hi`. Take `⟨hWc, hPW, -⟩` from `hS.mem_toFinset.1 hW`.

Rewrite using `[hgW W ⟨hWc, hPW⟩]`. Conclude with `(regMaxAt_isMaximal h₁ hL hP hWc hPW _).isPrime`. Take `⟨a, ham, ha⟩` from `Set.not_subset.1 hT`. Simplify using `only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at ha`. Establish `ha0 : ((a : funField P) : FractionRing (MRing ι ⧸ P)) ≠ 0` using `fun h => ha ⊥ (Finset.mem_insert_self _ _) (Ideal.mem_bot.2 (Subtype.ext (Subtype.ext (by rw [h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]))))`.

Take `⟨x, hxa⟩` from `funField_exists_inv (a : funField P) ha0`. Take `⟨n, hpn, hn⟩` from `h₂ K ι P p x hP hp fun W hWc hPW hpW => by`. Establish `h'` using `ha (g W) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g (hS.mem_toFinset.2 ⟨hWc, hPW, hpW⟩)))`. Rewrite `h'` using `[hgW W ⟨hWc, hPW⟩]`. Take `⟨z, hz, haz⟩` from `(not_mem_regMaxAt_iff hWc hPW _ a).1 h'`.

Rewrite using `[show (x : FractionRing (MRing ι ⧸ P)) = z by rw [← mul_one (x : FractionRing (MRing ι ⧸ P)), ← haz, ← mul_assoc, hxa, one_mul]]` and apply the resulting hypothesis. Use `hpn ((hZ n).1 ?_)` and prove the remaining obligations. Take `⟨b, hb⟩` from `regRing_exists_coe hn`. Establish `he : a * b = (n : regRing P)`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subring.coe_mul, Subring.coe_mul, hb, Subring.coe_mul, Subring.coe_intCast, Subring.coe_intCast, Subring.coe_intCast]`. Rewrite using `[mul_left_comm, mul_comm ((a : funField P) : FractionRing (MRing ι ⧸ P)), hxa, mul_one]`. Rewrite using `[← he]`. Conclude with `m.mul_mem_right b ham`.
-/
theorem RegularityMaximalSurjective.proof (h₁ : RegularityOrder.Statement) (h₂ : RegularityLocalPrime.Statement) : RegularityMaximalSurjective.Statement := by
  classical
  intro K _ ι _ P hP m hm
  have hPp : P.IsPrime := hP.2.1.1
  have hL : LocRingLocal.Statement := LocRingLocal.proof LocRingFrac.proof

  have hmZ : (m.comap (algebraMap ℤ (regRing P))).IsMaximal := by
    have : Module.Finite ℤ (regRing P) := (h₁ K ι P hP).2.1
    have : Algebra.IsIntegral ℤ (regRing P) := Algebra.IsIntegral.of_finite ℤ _
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have hp := Submodule.IsPrincipal.prime_generator_of_isPrime (is_prime := hmZ.isPrime) _
    (Ring.ne_bot_of_isMaximal_of_not_isField hmZ Int.not_isField)
  set p := Submodule.IsPrincipal.generator (m.comap (algebraMap ℤ (regRing P)))
  have hZ : ∀ n : ℤ, (n : regRing P) ∈ m ↔ p ∣ n := fun n => by
    rw [← Submodule.IsPrincipal.mem_iff_generator_dvd, Ideal.mem_comap, algebraMap_int_eq, eq_intCast]
  have hCp : C p ∉ P := fun h => by
    have h' : p ∈ P.comap (C : ℤ →+* MRing ι) := h
    rw [hP.2.2.1] at h'
    exact hp.ne_zero (Ideal.mem_bot.mp h')
  have hp0 : (p : regRing P) ≠ 0 := fun h => by
    have h' := regRing_intCast_coe P p
    rw [h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, eq_comm, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem] at h'
    exact hCp h'

  have hS : {W | IsClosedPt W ∧ P ≤ W ∧ C p ∈ W}.Finite :=
    (divSupp_finite P (C p)).subset fun W hW =>
      (RegularityDivisorSupportClosed.proof K ι P (C p) 0 W hP (RegularityDenominator.isMultiHomog_C p) hCp).2 hW
  let g : Ideal (MRing ι) → Ideal (regRing P) := fun W =>
    if h : IsClosedPt W ∧ P ≤ W then regMaxAt P W h.1 h.2 (hL K ι P W hPp h.1.1.1 h.2).1 else ⊥
  have hgW : ∀ W (h : IsClosedPt W ∧ P ≤ W), g W = regMaxAt P W h.1 h.2 (hL K ι P W hPp h.1.1.1 h.2).1 :=
    fun W h => dif_pos h
  by_contra hcon
  push Not at hcon

  let T : Finset (Ideal (regRing P)) := insert ⊥ (hS.toFinset.image g)
  have hT : ¬ ((m : Set (regRing P)) ⊆ ⋃ i ∈ (↑T : Set (Ideal (regRing P))), ((fun i => i) i : Set (regRing P))) := by
    rw [Ideal.subset_union_prime (f := fun i : Ideal (regRing P) => i) ⊥ ⊥ fun i hi h1 _ => ?_]
    · rintro ⟨i, hi, hle⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hp0 (Ideal.mem_bot.1 (hle ((hZ p).2 dvd_rfl)))
      · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hWc, hPW, -⟩ := hS.mem_toFinset.1 hW
        obtain ⟨x, hx, z, hz, hxz⟩ := hcon W hWc hPW
        have h' := hle hx
        rw [hgW W ⟨hWc, hPW⟩] at h'
        exact (not_mem_regMaxAt_iff hWc hPW _ x).2 ⟨z, hz, hxz⟩ h'
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact absurd rfl h1
      · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hWc, hPW, -⟩ := hS.mem_toFinset.1 hW
        rw [hgW W ⟨hWc, hPW⟩]
        exact (regMaxAt_isMaximal h₁ hL hP hWc hPW _).isPrime
  obtain ⟨a, ham, ha⟩ := Set.not_subset.1 hT
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at ha
  have ha0 : ((a : funField P) : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h =>
    ha ⊥ (Finset.mem_insert_self _ _) (Ideal.mem_bot.2 (Subtype.ext (Subtype.ext (by rw [h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]))))

  obtain ⟨x, hxa⟩ := funField_exists_inv (a : funField P) ha0
  obtain ⟨n, hpn, hn⟩ := h₂ K ι P p x hP hp fun W hWc hPW hpW => by
    have h' := ha (g W) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g (hS.mem_toFinset.2 ⟨hWc, hPW, hpW⟩)))
    rw [hgW W ⟨hWc, hPW⟩] at h'
    obtain ⟨z, hz, haz⟩ := (not_mem_regMaxAt_iff hWc hPW _ a).1 h'
    rwa [show (x : FractionRing (MRing ι ⧸ P)) = z by rw [← mul_one (x : FractionRing (MRing ι ⧸ P)), ← haz,
      ← mul_assoc, hxa, one_mul]]

  refine hpn ((hZ n).1 ?_)
  obtain ⟨b, hb⟩ := regRing_exists_coe hn
  have he : a * b = (n : regRing P) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, hb, Subring.coe_mul, Subring.coe_intCast, Subring.coe_intCast,
      Subring.coe_intCast]
    rw [mul_left_comm, mul_comm ((a : funField P) : FractionRing (MRing ι ⧸ P)), hxa, mul_one]
  rw [← he]
  exact m.mul_mem_right b ham

end

end GroundTheory.Heights₂.Heights.Inter

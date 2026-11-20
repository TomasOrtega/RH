import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGeneratorsStatement

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DPFlat

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R} (κ : DividedPowers I)

def expS (z : R) (y : A) : PowerSeries A :=
  PowerSeries.mk fun n ↦ y ^ n * algebraMap R A (κ.dpow n z)

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]`. Establish `h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, y ^ p.1 * algebraMap R A (κ.dpow p.1 z) * (y' ^ p.2 * algebraMap R A (κ.dpow p.2 z)) = y ^ p.1 * y' ^ p.2 * (n.choose p.1 : A) * algebraMap R A (κ.dpow n z)`. Introduce `p hp`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Establish `h` using `κ.mul_dpow (m := p.1) (n := p.2) hz`. Rewrite `h` using `[hp]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by rw [h, map_mul, map_natCast]; ring`. Rewrite using `[Finset.sum_congr rfl h, ← Finset.sum_mul, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`.
-/
theorem expS_add_right {z : R} (hz : z ∈ I) (y y' : A) :
    expS κ z (y + y') = expS κ z y * expS κ z y' := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  have h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, y ^ p.1 * algebraMap R A (κ.dpow p.1 z) *
      (y' ^ p.2 * algebraMap R A (κ.dpow p.2 z)) =
      y ^ p.1 * y' ^ p.2 * (n.choose p.1 : A) * algebraMap R A (κ.dpow n z) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h := κ.mul_dpow (m := p.1) (n := p.2) hz
    rw [hp] at h
    calc _ = y ^ p.1 * y' ^ p.2 * algebraMap R A (κ.dpow p.1 z * κ.dpow p.2 z) := by
            rw [map_mul]; ring
      _ = _ := by rw [h, map_mul, map_natCast]; ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul, κ.dpow_add hz hz', map_sum, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p hp ↦ ?_` and prove the remaining obligations. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[← hp, pow_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem expS_add_left {z z' : R} (hz : z ∈ I) (hz' : z' ∈ I) (y : A) :
    expS κ (z + z') y = expS κ z y * expS κ z' y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul, κ.dpow_add hz hz', map_sum, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]; ring

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [expS, PowerSeries.coeff_mk, κ.dpow_mul hz, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expS_smul {z : R} (hz : z ∈ I) (a : R) (y : A) :
    expS κ z (algebraMap R A a * y) = expS κ (a * z) y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, κ.dpow_mul hz, map_mul, map_pow]
  ring

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[κ.dpow_zero I.zero_mem]`. Simplify using `[κ.dpow_eval_zero hn, hn]`.
-/
theorem expS_zero_left (y : A) : expS κ 0 y = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero I.zero_mem]
  · simp [κ.dpow_eval_zero hn, hn]

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[κ.dpow_zero hz]`. Simplify using `[hn]`.
-/
theorem expS_zero_right (z : R) (hz : z ∈ I) : expS κ z (0 : A) = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero hz]
  · simp [hn]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [expS_zero_right κ z hz]`. Consider the case `insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, expS_add_right κ hz, ih]`.
-/
theorem expS_sum_right {z : R} (hz : z ∈ I) {K : Type} (s : Finset K) (f : K → A) :
    expS κ z (∑ k ∈ s, f k) = ∏ k ∈ s, expS κ z (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_right κ z hz]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, expS_add_right κ hz, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [expS_zero_left κ y]`. Consider the case `insert k s hk ih`. Rewrite using `[Finset.sum_insert hk, Finset.prod_insert hk, expS_add_left κ (hf k (Finset.mem_insert_self k s)) (Ideal.sum_mem _ fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)), ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]`.
-/
theorem expS_sum_left {K : Type} (s : Finset K) (f : K → R) (hf : ∀ k ∈ s, f k ∈ I) (y : A) :
    expS κ (∑ k ∈ s, f k) y = ∏ k ∈ s, expS κ (f k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_left κ y]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk,
      expS_add_left κ (hf k (Finset.mem_insert_self k s))
        (Ideal.sum_mem _ fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]

/- English proof (translation)
Establish `h : ∑ i : ↥c.support, ((i : I) : R) • (c (i : I) : A) = (0 : A)`. Rewrite using `[Finset.sum_coe_sort c.support (fun i : I ↦ ((i : R)) • (c i : A)), ← hc, Finsupp.sum]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Take `⟨k, a, y, hx, ha⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) h`.

Simplify using `only at hx ha`. Express the relevant statement in the definitionally equal form `(∏ i ∈ c.support, expS κ (i : R) (c i)) = 1`. Rewrite using `[← Finset.prod_coe_sort]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_congr rfl fun i _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[hx i, expS_sum_right κ (i.1 : I).2]`. Use `Finset.prod_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, expS_smul κ (i.1 : I).2]`. Use `_ = ∏ j, ∏ i : c.support, expS κ (a i j * ((i.1 : I) : R)) (y j) := Finset.prod_comm`. Use `_ = ∏ j, expS κ (∑ i : c.support, a i j * ((i.1 : I) : R)) (y j) := by`.

Use `Finset.prod_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[expS_sum_left κ _ _ fun i _ ↦ I.mul_mem_left _ (i.1 : I).2]`. Use `_ = 1 := by`. Use `Finset.prod_eq_one fun j _ ↦ ?_` and prove the remaining obligations. Establish `: ∑ i : c.support, a i j * ((i.1 : I) : R) = 0`.

Rewrite using `[← ha j]`. Conclude with `Finset.sum_congr rfl fun i _ ↦ mul_comm _ _`. Rewrite using `[this, expS_zero_left]`.
-/
theorem prod_expS_eq_one [Module.Flat R A] (c : I →₀ A)
    (hc : (c.sum fun i a ↦ a * algebraMap R A i) = 0) :
    (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * algebraMap R A (κ.dpow n i)) = 1 := by
  have h : ∑ i : ↥c.support, ((i : I) : R) • (c (i : I) : A) = (0 : A) := by
    rw [Finset.sum_coe_sort c.support (fun i : I ↦ ((i : R)) • (c i : A)), ← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  obtain ⟨k, a, y, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) h
  simp only at hx ha
  change (∏ i ∈ c.support, expS κ (i : R) (c i)) = 1
  rw [← Finset.prod_coe_sort]
  calc ∏ i : c.support, expS κ ((i.1 : I) : R) (c i.1)
      = ∏ i : c.support, ∏ j, expS κ (a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [hx i, expS_sum_right κ (i.1 : I).2]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [Algebra.smul_def, expS_smul κ (i.1 : I).2]
    _ = ∏ j, ∏ i : c.support, expS κ (a i j * ((i.1 : I) : R)) (y j) := Finset.prod_comm
    _ = ∏ j, expS κ (∑ i : c.support, a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [expS_sum_left κ _ _ fun i _ ↦ I.mul_mem_left _ (i.1 : I).2]
    _ = 1 := by
        refine Finset.prod_eq_one fun j _ ↦ ?_
        have : ∑ i : c.support, a i j * ((i.1 : I) : R) = 0 := by
          rw [← ha j]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
        rw [this, expS_zero_left]

/- English proof (translation)
Introduce `R A _ _ _ _ I κ`. Set `x : I → A` to `fun i ↦ algebraMap R A i`. Establish `hspan : Ideal.span (Set.range x) = I.map (algebraMap R A)`. Rewrite using `[Ideal.map]`. Use `congr 1`.

Use extensionality with `b`. Simplify using `[x]`. Take `⟨γ, hγ, hγx⟩` from `GlobalTheory.T.exists_isPreDividedPowers_of_generators A I x (fun i n ↦ algebraMap R A (κ.dpow n i)) (fun i ↦ by simp [κ.dpow_zero i.2]) (fun i ↦ by simp [x, κ.dpow_one i.2]) (fun i n hn ↦ Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩) (fun i m n ↦ by rw [← map_mul, κ. …`. Rewrite `hγ` using `[hspan]`. Take `⟨δ, hδ⟩` from `GlobalTheory.T.exists_dividedPowers_of_comp_on_generators A _ γ (Set.range x) hγ hspan.symm (by`.

Introduce and unpack `_ ⟨i, rfl⟩ m n hn`. Rewrite using `[hγx, show algebraMap R A (κ.dpow n i) = x ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ from rfl, hγx]`. Simplify using `only [κ.dpow_comp hn i.2, map_mul, map_natCast]`. Rewrite using `[← hγx])`. Conclude with `⟨δ, ⟨le_rfl, fun a ha ↦ by rw [hδ]; exact hγx ⟨a, ha⟩ _⟩⟩`.
-/
theorem exists_isDPMorphism_of_flat : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I),
    ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  intro R A _ _ _ _ I κ
  let x : I → A := fun i ↦ algebraMap R A i
  have hspan : Ideal.span (Set.range x) = I.map (algebraMap R A) := by
    rw [Ideal.map]; congr 1; ext b; simp [x]
  obtain ⟨γ, hγ, hγx⟩ := GlobalTheory.T.exists_isPreDividedPowers_of_generators A I x (fun i n ↦ algebraMap R A (κ.dpow n i))
    (fun i ↦ by simp [κ.dpow_zero i.2]) (fun i ↦ by simp [x, κ.dpow_one i.2])
    (fun i n hn ↦ Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩)
    (fun i m n ↦ by rw [← map_mul, κ.mul_dpow i.2, map_mul, map_natCast])
    (prod_expS_eq_one κ)
  rw [hspan] at hγ
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_dividedPowers_of_comp_on_generators A _ γ (Set.range x) hγ hspan.symm (by
    rintro _ ⟨i, rfl⟩ m n hn
    rw [hγx, show algebraMap R A (κ.dpow n i) = x ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ from rfl, hγx]
    simp only [κ.dpow_comp hn i.2, map_mul, map_natCast]
    rw [← hγx])
  exact ⟨δ, ⟨le_rfl, fun a ha ↦ by rw [hδ]; exact hγx ⟨a, ha⟩ _⟩⟩

end GlobalTheory.DPFlat

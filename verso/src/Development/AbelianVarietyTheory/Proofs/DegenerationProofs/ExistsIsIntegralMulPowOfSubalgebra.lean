import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

namespace GlobalTheory

open Polynomial

section

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type*}

/- English proof (translation)
Use `set A := Algebra.adjoin o (Set.range fun j => t j / t i) with hA`. Use `haveI : Algebra.FiniteType o A := .adjoin_of_finite (Set.finite_range _)`. Establish `hK : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) ≤ Subfield.closure (A : Set Ω)`. Use `Subfield.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `x (⟨a, rfl⟩ | ⟨k, j, rfl⟩)`.

Conclude with `Subfield.subset_closure (A.algebraMap_mem a)`. Establish `: t j / t k = (t j / t i) / (t k / t i)`. Rewrite using `[div_div_div_cancel_right₀ hi]`. Rewrite using `[this]`. Conclude with `div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩)) (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))`.

Use `haveI : Algebra.EssFiniteType A Ω := by`. Take `⟨σ, hσ⟩` from `hfin`. Use `(Algebra.essFiniteType_iff _ _).mpr ⟨σ, fun s => ?_⟩` and prove the remaining obligations. Establish `hs : s ∈ Submodule.span _ (σ : Set Ω)` using `hσ ▸ Submodule.mem_top`. Proceed by induction on `hs using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨1, one_mem _, isUnit_one, by simpa using Algebra.subset_adjoin hx⟩`. Consider the case `zero => exact ⟨1, one_mem _, isUnit_one, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, ha', hx⟩` from `hx`. Take `⟨b, hb, hb', hy⟩` from `hy`.

Use `⟨a * b, mul_mem ha hb, ha'.mul hb', ?_⟩` and prove the remaining obligations. Establish `: (x + y) * (a * b) = x * a * b + y * b * a` using `by ring`. Rewrite using `[this]`. Conclude with `add_mem (mul_mem hx hb) (mul_mem hy ha)`. Consider the case `smul c x _ hx`.

Take `⟨a, ha, ha', hx⟩` from `hx`. Take `⟨y, hy, w, hw, hc⟩` from `Subfield.mem_closure_iff.mp (hK c.2)`. Establish `hAA : Subring.closure (A : Set Ω) = A.toSubring` using `Subring.closure_eq A.toSubring`. Rewrite `hy`, `hw` using `[hAA]`. Establish `hy' : y ∈ Algebra.adjoin A (σ : Set Ω)` using `Subalgebra.algebraMap_mem _ (⟨y, hy⟩ : A)`.

Establish `hw' : w ∈ Algebra.adjoin A (σ : Set Ω)` using `Subalgebra.algebraMap_mem _ (⟨w, hw⟩ : A)`. Distinguish the cases in `hw0 : w = 0`. Use `⟨1, one_mem _, isUnit_one, ?_⟩` and prove the remaining obligations. Establish `: (c : Ω) = 0` using `by rw [← hc, hw0, div_zero]`. Rewrite using `[Subfield.smul_def, this]`.

Simplify using the standard rewrite rules. Use `⟨a * w, mul_mem ha hw', ha'.mul (IsUnit.mk0 _ hw0), ?_⟩` and prove the remaining obligations. Establish `: c • x * (a * w) = y * (x * a)`. Rewrite using `[Subfield.smul_def, ← hc, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `mul_mem hy' hx`. Use `haveI := finite_integralClosure_of_essFiniteType_field o A Ω`. Take `⟨s, hs⟩` from `(inferInstance : Module.Finite A (integralClosure A Ω))`. Use `⟨(integralClosure A Ω).val.toLinearMap '' s, s.finite_toSet.image _, ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `x.2`. Rewrite using `[Submodule.span_image, hs]`. Conclude with `⟨⟨x, hx⟩, trivial, rfl⟩`.
-/
theorem exists_finite_span_isIntegral_chart [IsDedekindDomain o] [CharZero Ω] [Finite J]
    (t : J → Ω) {i : J} (hi : t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω) :
    ∃ G : Set Ω, G.Finite ∧
      (∀ x ∈ G, IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) ∧
      ∀ x, IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x →
        x ∈ Submodule.span (Algebra.adjoin o (Set.range fun j => t j / t i)) G := by
  set A := Algebra.adjoin o (Set.range fun j => t j / t i) with hA
  haveI : Algebra.FiniteType o A := .adjoin_of_finite (Set.finite_range _)
  have hK : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) ≤
      Subfield.closure (A : Set Ω) := by
    refine Subfield.closure_le.mpr ?_
    rintro x (⟨a, rfl⟩ | ⟨k, j, rfl⟩)
    · exact Subfield.subset_closure (A.algebraMap_mem a)
    · have : t j / t k = (t j / t i) / (t k / t i) := by
        rw [div_div_div_cancel_right₀ hi]
      rw [this]
      exact div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩))
        (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))
  haveI : Algebra.EssFiniteType A Ω := by
    obtain ⟨σ, hσ⟩ := hfin
    refine (Algebra.essFiniteType_iff _ _).mpr ⟨σ, fun s => ?_⟩
    have hs : s ∈ Submodule.span _ (σ : Set Ω) := hσ ▸ Submodule.mem_top
    induction hs using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_mem _, isUnit_one, by simpa using Algebra.subset_adjoin hx⟩
    | zero => exact ⟨1, one_mem _, isUnit_one, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨b, hb, hb', hy⟩ := hy
      refine ⟨a * b, mul_mem ha hb, ha'.mul hb', ?_⟩
      have : (x + y) * (a * b) = x * a * b + y * b * a := by ring
      rw [this]
      exact add_mem (mul_mem hx hb) (mul_mem hy ha)
    | smul c x _ hx =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨y, hy, w, hw, hc⟩ := Subfield.mem_closure_iff.mp (hK c.2)
      have hAA : Subring.closure (A : Set Ω) = A.toSubring := Subring.closure_eq A.toSubring
      rw [hAA] at hy hw
      have hy' : y ∈ Algebra.adjoin A (σ : Set Ω) := Subalgebra.algebraMap_mem _ (⟨y, hy⟩ : A)
      have hw' : w ∈ Algebra.adjoin A (σ : Set Ω) := Subalgebra.algebraMap_mem _ (⟨w, hw⟩ : A)
      by_cases hw0 : w = 0
      · refine ⟨1, one_mem _, isUnit_one, ?_⟩
        have : (c : Ω) = 0 := by rw [← hc, hw0, div_zero]
        rw [Subfield.smul_def, this]
        simp
      · refine ⟨a * w, mul_mem ha hw', ha'.mul (IsUnit.mk0 _ hw0), ?_⟩
        have : c • x * (a * w) = y * (x * a) := by
          rw [Subfield.smul_def, ← hc, smul_eq_mul]
          field_simp
        rw [this]
        exact mul_mem hy' hx
  haveI := finite_integralClosure_of_essFiniteType_field o A Ω
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite A (integralClosure A Ω))
  refine ⟨(integralClosure A Ω).val.toLinearMap '' s, s.finite_toSet.image _, ?_, fun x hx => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Submodule.span_image, hs]
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

/- English proof (translation)
Establish `hu : t i / t j ∈ Algebra.adjoin o (Set.range fun k => t k / t j)` using `Algebra.subset_adjoin ⟨i, rfl⟩`. Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Establish `: t k / t i * (t i / t j) ^ 1 = t k / t j`. Rewrite using `[pow_one, div_mul_div_cancel₀ hi]`. Rewrite using `[this]`. Conclude with `Algebra.subset_adjoin ⟨k, rfl⟩`. Consider the case `algebraMap a => exact ⟨0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨n, hx⟩` from `hx`. Take `⟨m, hy⟩` from `hy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `: (x + y) * (t i / t j) ^ (n + m) = x * (t i / t j) ^ n * (t i / t j) ^ m + y * (t i / t j) ^ m * (t i / t j) ^ n` using `by ring`.

Rewrite using `[this]`. Conclude with `add_mem (mul_mem hx (pow_mem hu _)) (mul_mem hy (pow_mem hu _))`. Consider the case `mul x y _ _ hx hy`. Take `⟨n, hx⟩` from `hx`. Take `⟨m, hy⟩` from `hy`.

Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `: x * y * (t i / t j) ^ (n + m) = x * (t i / t j) ^ n * (y * (t i / t j) ^ m)` using `by ring`. Rewrite using `[this]`. Conclude with `mul_mem hx hy`.
-/
theorem exists_mul_pow_mem_chart (t : J → Ω) {i : J} (j : J) (hi : t i ≠ 0) {r : Ω}
    (hr : r ∈ Algebra.adjoin o (Set.range fun k => t k / t i)) :
    ∃ n : ℕ, r * (t i / t j) ^ n ∈ Algebra.adjoin o (Set.range fun k => t k / t j) := by
  have hu : t i / t j ∈ Algebra.adjoin o (Set.range fun k => t k / t j) :=
    Algebra.subset_adjoin ⟨i, rfl⟩
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine ⟨1, ?_⟩
    have : t k / t i * (t i / t j) ^ 1 = t k / t j := by
      rw [pow_one, div_mul_div_cancel₀ hi]
    rw [this]
    exact Algebra.subset_adjoin ⟨k, rfl⟩
  | algebraMap a => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hx⟩ := hx
    obtain ⟨m, hy⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * (t i / t j) ^ (n + m) = x * (t i / t j) ^ n * (t i / t j) ^ m +
      y * (t i / t j) ^ m * (t i / t j) ^ n := by ring
    rw [this]
    exact add_mem (mul_mem hx (pow_mem hu _)) (mul_mem hy (pow_mem hu _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hx⟩ := hx
    obtain ⟨m, hy⟩ := hy
    refine ⟨n + m, ?_⟩
    have : x * y * (t i / t j) ^ (n + m) = x * (t i / t j) ^ n * (y * (t i / t j) ^ m) := by ring
    rw [this]
    exact mul_mem hx hy

/- English proof (translation)
Establish `hB : ∀ x ∈ B, IsIntegral B x` using `fun x hx => isIntegral_algebraMap (x := (⟨x, hx⟩ : B))`. It suffices to establish `∃ N : ℕ, IsIntegral B (z * u ^ N) by`. Take `⟨N, hN⟩` from `this`. Use `⟨N, fun M hM => ?_⟩` and prove the remaining obligations. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hM`.

Rewrite using `[pow_add, ← mul_assoc]`. Conclude with `hN.mul (hB _ (pow_mem hu _))`. Take `⟨p, hp, hz⟩` from `hz`. Use `choose n hn using fun r : A => hr r r.2`. Set `N` to `p.support.sup fun i => n (p.coeff i)`.

Establish `hN : ∀ i k, k ≠ 0 → IsIntegral B (algebraMap A Ω (p.coeff i) * (u ^ N) ^ k)`. Introduce `i k hk`. Distinguish the cases in `hi : i ∈ p.support`. Establish `h1 : n (p.coeff i) ≤ N * k` using `(Finset.le_sup (f := fun i => n (p.coeff i)) hi).trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk))`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le h1`.

Rewrite using `[← pow_mul, hd, pow_add, ← mul_assoc]`. Conclude with `hB _ (mul_mem (hn _) (pow_mem hu _))`. Rewrite using `[notMem_support_iff.mp hi, map_zero, zero_mul]`. Conclude with `isIntegral_zero`. Set `q` to `p.map (algebraMap A Ω)`.

Establish `hq : q.Monic` using `hp.map _`. Establish `hqz : q.eval z = 0` using `by rw [eval_map, hz]`. Establish `hq0 : q.natDegree ≠ 0`. Introduce `h`. Rewrite `hqz` using `[hq.natDegree_eq_zero.mp h]`.

Simplify using `at hqz`. Use `⟨N, IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := q.scaleRoots (u ^ N)) ((monic_scaleRoots_iff _).mpr hq) (by rwa [natDegree_scaleRoots]) ?_ fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, scaleRoots_eval_mul, hqz, mul_zero]`. Conclude with `isIntegral_zero`. Rewrite using `[coeff_scaleRoots]`.

Break down `lt_trichotomy i q.natDegree with h | rfl | h` into its components or cases. Rewrite using `[coeff_map]`. Conclude with `hN _ _ (by omega)`. Simplify `isIntegral_one` using `[hq.coeff_natDegree]`. Simplify `isIntegral_zero` using `[coeff_eq_zero_of_natDegree_lt h]`.
-/
theorem exists_isIntegral_mul_pow_of_subalgebra (A B : Subalgebra o Ω) {u : Ω} (hu : u ∈ B)
    (hr : ∀ r ∈ A, ∃ n : ℕ, r * u ^ n ∈ B) {z : Ω} (hz : IsIntegral A z) :
    ∃ N : ℕ, ∀ M, N ≤ M → IsIntegral B (z * u ^ M) := by
  have hB : ∀ x ∈ B, IsIntegral B x := fun x hx => isIntegral_algebraMap (x := (⟨x, hx⟩ : B))
  suffices ∃ N : ℕ, IsIntegral B (z * u ^ N) by
    obtain ⟨N, hN⟩ := this
    refine ⟨N, fun M hM => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
    rw [pow_add, ← mul_assoc]
    exact hN.mul (hB _ (pow_mem hu _))
  obtain ⟨p, hp, hz⟩ := hz
  choose n hn using fun r : A => hr r r.2
  let N := p.support.sup fun i => n (p.coeff i)
  have hN : ∀ i k, k ≠ 0 → IsIntegral B (algebraMap A Ω (p.coeff i) * (u ^ N) ^ k) := by
    intro i k hk
    by_cases hi : i ∈ p.support
    · have h1 : n (p.coeff i) ≤ N * k :=
        (Finset.le_sup (f := fun i => n (p.coeff i)) hi).trans
          (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk))
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
      rw [← pow_mul, hd, pow_add, ← mul_assoc]
      exact hB _ (mul_mem (hn _) (pow_mem hu _))
    · rw [notMem_support_iff.mp hi, map_zero, zero_mul]
      exact isIntegral_zero
  let q := p.map (algebraMap A Ω)
  have hq : q.Monic := hp.map _
  have hqz : q.eval z = 0 := by rw [eval_map, hz]
  have hq0 : q.natDegree ≠ 0 := by
    intro h
    rw [hq.natDegree_eq_zero.mp h] at hqz
    simp at hqz
  refine ⟨N, IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := q.scaleRoots (u ^ N))
    ((monic_scaleRoots_iff _).mpr hq) (by rwa [natDegree_scaleRoots]) ?_ fun i => ?_⟩
  · rw [mul_comm, scaleRoots_eval_mul, hqz, mul_zero]
    exact isIntegral_zero
  · rw [coeff_scaleRoots]
    rcases lt_trichotomy i q.natDegree with h | rfl | h
    · rw [coeff_map]
      exact hN _ _ (by omega)
    · simpa [hq.coeff_natDegree] using isIntegral_one
    · simpa [coeff_eq_zero_of_natDegree_lt h] using isIntegral_zero

/- English proof (translation)
Set `y : J → C.toSubring` to `fun i => ⟨_, hC i⟩`. Distinguish the cases in `hI : Ideal.span (Set.range y) = ⊤`. Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp hI)`. Use `⟨fun i => ⟨c i, (c i).2⟩, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg C.toSubring.subtype hc`.

Rewrite `h` using `[map_sum, map_one]`. Conclude with `h`. It suffices to derive a contradiction. Take `⟨V, hV, hV'⟩` from `Ideal.image_subset_nonunits_valuationSubring _ hI`. Take `⟨i₀, hi₀⟩` from `ht`.

Take `⟨i, -, hi⟩` from `Finset.exists_max_image Finset.univ (fun j => V.valuation (t j)) ⟨i₀, Finset.mem_univ _⟩`. Establish `hv : 0 < V.valuation (t i)` using `((V.valuation.pos_iff).mpr hi₀).trans_le (hi _ (Finset.mem_univ _))`. Establish `hti : t i ≠ 0` using `(V.valuation.pos_iff).mp hv`. Establish `hle : ∀ x ∈ Algebra.adjoin o (Set.range fun j => t j / t i), x ∈ V`. Introduce `x hx`.

Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Rewrite using `[← V.valuation_le_one_iff, map_div₀, div_le_one₀ hv]`. Conclude with `hi _ (Finset.mem_univ _)`.

Consider the case `algebraMap a => exact hV (C.algebraMap_mem a)`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `mul x y _ _ hx hy => exact mul_mem hx hy`. Establish `h1 : IsIntegral V (w / t i ^ e)` using `(hw i hti).map_of_comp_eq (T := V) ((Algebra.adjoin o (Set.range fun j => t j / t i)).val.toRingHom.codRestrict V fun x => hle x x.2) (RingHom.id Ω) rfl`. Take `⟨v, hv1⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h1`.

Establish `h2 : V.valuation (w / t i ^ e) ≤ 1`. Rewrite using `[V.valuation_le_one_iff, ← hv1]`. Conclude with `v.2`. Establish `h3 : V.valuation (t i ^ e / w) < 1` using `V.mem_nonunits_iff.mp (hV' ⟨y i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩)`. Establish `h4 : V.valuation (t i ^ e / w) * V.valuation (w / t i ^ e) = 1`.

Rewrite using `[← map_mul, div_mul_div_cancel₀ hw0, div_self (pow_ne_zero _ hti), map_one]`. Conclude with `(mul_lt_one_of_lt_of_le h3 h2).ne h4`.
-/
theorem exists_sum_mul_pow_div_eq_one [Fintype J] (t : J → Ω) (ht : ∃ i, t i ≠ 0) (e : ℕ) {w : Ω}
    (hw0 : w ≠ 0) (hw : ∀ i, t i ≠ 0 →
      IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) (w / t i ^ e))
    (C : Subalgebra o Ω) (hC : ∀ i, t i ^ e / w ∈ C) :
    ∃ c : J → C, ∑ i, (c i : Ω) * (t i ^ e / w) = 1 := by
  let y : J → C.toSubring := fun i => ⟨_, hC i⟩
  by_cases hI : Ideal.span (Set.range y) = ⊤
  · obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp hI)
    refine ⟨fun i => ⟨c i, (c i).2⟩, ?_⟩
    have h := congrArg C.toSubring.subtype hc
    rw [map_sum, map_one] at h
    exact h
  exfalso
  obtain ⟨V, hV, hV'⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  obtain ⟨i₀, hi₀⟩ := ht
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => V.valuation (t j))
    ⟨i₀, Finset.mem_univ _⟩
  have hv : 0 < V.valuation (t i) :=
    ((V.valuation.pos_iff).mpr hi₀).trans_le (hi _ (Finset.mem_univ _))
  have hti : t i ≠ 0 := (V.valuation.pos_iff).mp hv
  have hle : ∀ x ∈ Algebra.adjoin o (Set.range fun j => t j / t i), x ∈ V := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ hv]
      exact hi _ (Finset.mem_univ _)
    | algebraMap a => exact hV (C.algebraMap_mem a)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have h1 : IsIntegral V (w / t i ^ e) :=
    (hw i hti).map_of_comp_eq (T := V)
      ((Algebra.adjoin o (Set.range fun j => t j / t i)).val.toRingHom.codRestrict V
        fun x => hle x x.2) (RingHom.id Ω) rfl
  obtain ⟨v, hv1⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  have h2 : V.valuation (w / t i ^ e) ≤ 1 := by
    rw [V.valuation_le_one_iff, ← hv1]
    exact v.2
  have h3 : V.valuation (t i ^ e / w) < 1 :=
    V.mem_nonunits_iff.mp (hV' ⟨y i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩)
  have h4 : V.valuation (t i ^ e / w) * V.valuation (w / t i ^ e) = 1 := by
    rw [← map_mul, div_mul_div_cancel₀ hw0, div_self (pow_ne_zero _ hti), map_one]
  exact (mul_lt_one_of_lt_of_le h3 h2).ne h4

end

/- English proof (translation)
Set `A : J → Subalgebra o Ω` to `fun i => Algebra.adjoin o (Set.range fun j => t j / t i)`. Establish `hA : ∀ i, ∀ x ∈ A i, IsIntegral (A i) x` using `fun i x hx => isIntegral_algebraMap (x := (⟨x, hx⟩ : A i))`. Establish `hmem : ∀ i j, t j / t i ∈ A i` using `fun i j => Algebra.subset_adjoin ⟨j, rfl⟩`. Use `choose G hG hGi hGs using fun i : {i // t i ≠ 0} => exists_finite_span_isIntegral_chart (o := o) t i.2 hfin`. Use `haveI : ∀ i, Finite (G i) := fun i => (hG i).to_subtype`.

Use `choose N hN using fun a : (Σ i, G i) × J => exists_isIntegral_mul_pow_of_subalgebra (A a.1.1) (A a.2) (hmem a.2 a.1.1) (fun r hr => exists_mul_pow_mem_chart t a.2 a.1.1.2 hr) (hGi _ _ a.1.2.2)`. Take `⟨d, hd⟩` from `(Set.finite_range N).bddAbove`. Set `Z : Set Ω` to `Set.range (fun a : J × J => t a.1 ^ d * t a.2) ∪ Set.range (fun a : (Σ i, G i) => (a.2 : Ω) * t a.1 ^ (d + 1))`. Establish `hZ : Z.Finite` using `(Set.finite_range _).union (Set.finite_range _)`. Take `⟨n, z, -, hz⟩` from `hZ.fin_param`.

Establish `hzt : ∀ i j, ∃ k, z k = t i ^ d * t j` using `fun i j => (hz.ge (Or.inl ⟨(i, j), rfl⟩) :)`. Take `_ | n` from `n`. Take `⟨i, -⟩` from `ht`. Take `⟨k, -⟩` from `hzt i i`. Conclude with `k.elim0`.

Establish `hzi : ∀ k i, t i ≠ 0 → IsIntegral (A i) (z k / t i ^ (d + 1))`. Introduce `k i hi`. Take `⟨a, ha⟩ | ⟨a, ha⟩ : z k ∈ Z` from `hz.le ⟨k, rfl⟩`. Establish `: z k / t i ^ (d + 1) = (t a.1 / t i) ^ d * (t a.2 / t i)`. Rewrite using `[← ha, div_pow, div_mul_div_comm, pow_succ]`.

Rewrite using `[this]`. Conclude with `hA _ _ (mul_mem (pow_mem (hmem _ _) _) (hmem _ _))`. Establish `: z k / t i ^ (d + 1) = a.2 * (t a.1 / t i) ^ (d + 1)`. Rewrite using `[← ha, div_pow, mul_div_assoc]`. Rewrite using `[this]`.

Conclude with `hN (a, i) _ ((hd ⟨_, rfl⟩).trans (Nat.le_succ d))`. Establish `hzp : ∀ i, ∃ k, z k = t i ^ (d + 1)` using `fun i => by simpa [pow_succ] using hzt i i`. Use `⟨d + 1, n, z, Nat.le_add_left _ _, hzp, fun i hi x => ⟨fun hx => ?_, fun hx => ?_⟩, fun k hk => exists_sum_mul_pow_div_eq_one t ht _ hk (hzi k) _ fun i => ?_⟩` and prove the remaining obligations. Establish `: Algebra.adjoin o (Set.range fun k => z k / t i ^ (d + 1)) ≤ (integralClosure (A i) Ω).restrictScalars o`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hzi k i hi`. Conclude with `this hx`. Establish `h1 : A i ≤ Algebra.adjoin o (Set.range fun k => z k / t i ^ (d + 1))`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, rfl⟩`. Take `⟨k, hk⟩` from `hzt i j`. Use `Algebra.subset_adjoin ⟨k, ?_⟩` and prove the remaining obligations. Simplify using `only [hk]`. Rewrite using `[pow_succ, mul_div_mul_left _ _ (pow_ne_zero _ hi)]`.

Establish `h2` using `hGs ⟨i, hi⟩ x hx`. Use `clear hx`. Proceed by induction on `h2 using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨k, hk⟩ : y * t i ^ (d + 1) ∈ Set.range z` from `hz.ge (Or.inr ⟨⟨⟨i, hi⟩, y, hy⟩, rfl⟩)`.

Use `Algebra.subset_adjoin ⟨k, ?_⟩` and prove the remaining obligations. Simplify using `only [hk]`. Clear the denominators using the available nonvanishing facts. Consider the case `zero => exact zero_mem _`. Consider the case `add y w _ _ hy hw => exact add_mem hy hw`.

Consider the case `smul c y _ hy => exact mul_mem (h1 c.2) hy`. Take `⟨l, hl⟩` from `hzp i`. Conclude with `Algebra.subset_adjoin ⟨l, by simp only [hl]⟩`.
-/
theorem exists_tuple_normalisation_charts (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    [IsDedekindDomain o] [CharZero Ω] (_hinj : Function.Injective (algebraMap o Ω)) (J : Type)
    [Fintype J] (t : J → Ω) (ht : ∃ i, t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω) :
    ∃ (e n : ℕ) (z : Fin (n + 1) → Ω), 1 ≤ e ∧ (∀ i, ∃ k, z k = t i ^ e) ∧
      (∀ i, t i ≠ 0 → ∀ x, x ∈ Algebra.adjoin o (Set.range fun k => z k / t i ^ e) ↔
        IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) ∧
      ∀ k, z k ≠ 0 → ∃ c : J → Algebra.adjoin o (Set.range fun l => z l / z k),
        ∑ i, (c i : Ω) * (t i ^ e / z k) = 1 := by
  let A : J → Subalgebra o Ω := fun i => Algebra.adjoin o (Set.range fun j => t j / t i)
  have hA : ∀ i, ∀ x ∈ A i, IsIntegral (A i) x := fun i x hx =>
    isIntegral_algebraMap (x := (⟨x, hx⟩ : A i))
  have hmem : ∀ i j, t j / t i ∈ A i := fun i j => Algebra.subset_adjoin ⟨j, rfl⟩
  choose G hG hGi hGs using fun i : {i // t i ≠ 0} =>
    exists_finite_span_isIntegral_chart (o := o) t i.2 hfin
  haveI : ∀ i, Finite (G i) := fun i => (hG i).to_subtype
  choose N hN using fun a : (Σ i, G i) × J =>
    exists_isIntegral_mul_pow_of_subalgebra (A a.1.1) (A a.2) (hmem a.2 a.1.1)
      (fun r hr => exists_mul_pow_mem_chart t a.2 a.1.1.2 hr) (hGi _ _ a.1.2.2)
  obtain ⟨d, hd⟩ := (Set.finite_range N).bddAbove
  let Z : Set Ω := Set.range (fun a : J × J => t a.1 ^ d * t a.2) ∪
    Set.range (fun a : (Σ i, G i) => (a.2 : Ω) * t a.1 ^ (d + 1))
  have hZ : Z.Finite := (Set.finite_range _).union (Set.finite_range _)
  obtain ⟨n, z, -, hz⟩ := hZ.fin_param
  have hzt : ∀ i j, ∃ k, z k = t i ^ d * t j := fun i j =>
    (hz.ge (Or.inl ⟨(i, j), rfl⟩) :)
  obtain _ | n := n
  · obtain ⟨i, -⟩ := ht
    obtain ⟨k, -⟩ := hzt i i
    exact k.elim0
  have hzi : ∀ k i, t i ≠ 0 → IsIntegral (A i) (z k / t i ^ (d + 1)) := by
    intro k i hi
    obtain ⟨a, ha⟩ | ⟨a, ha⟩ : z k ∈ Z := hz.le ⟨k, rfl⟩
    · have : z k / t i ^ (d + 1) = (t a.1 / t i) ^ d * (t a.2 / t i) := by
        rw [← ha, div_pow, div_mul_div_comm, pow_succ]
      rw [this]
      exact hA _ _ (mul_mem (pow_mem (hmem _ _) _) (hmem _ _))
    · have : z k / t i ^ (d + 1) = a.2 * (t a.1 / t i) ^ (d + 1) := by
        rw [← ha, div_pow, mul_div_assoc]
      rw [this]
      exact hN (a, i) _ ((hd ⟨_, rfl⟩).trans (Nat.le_succ d))
  have hzp : ∀ i, ∃ k, z k = t i ^ (d + 1) := fun i => by simpa [pow_succ] using hzt i i
  refine ⟨d + 1, n, z, Nat.le_add_left _ _, hzp, fun i hi x => ⟨fun hx => ?_, fun hx => ?_⟩,
    fun k hk => exists_sum_mul_pow_div_eq_one t ht _ hk (hzi k) _ fun i => ?_⟩
  · have : Algebra.adjoin o (Set.range fun k => z k / t i ^ (d + 1)) ≤
        (integralClosure (A i) Ω).restrictScalars o := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨k, rfl⟩
      exact hzi k i hi
    exact this hx
  · have h1 : A i ≤ Algebra.adjoin o (Set.range fun k => z k / t i ^ (d + 1)) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := hzt i j
      refine Algebra.subset_adjoin ⟨k, ?_⟩
      simp only [hk]
      rw [pow_succ, mul_div_mul_left _ _ (pow_ne_zero _ hi)]
    have h2 := hGs ⟨i, hi⟩ x hx
    clear hx
    induction h2 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk⟩ : y * t i ^ (d + 1) ∈ Set.range z := hz.ge (Or.inr ⟨⟨⟨i, hi⟩, y, hy⟩, rfl⟩)
      refine Algebra.subset_adjoin ⟨k, ?_⟩
      simp only [hk]
      field_simp
    | zero => exact zero_mem _
    | add y w _ _ hy hw => exact add_mem hy hw
    | smul c y _ hy => exact mul_mem (h1 c.2) hy
  · obtain ⟨l, hl⟩ := hzp i
    exact Algebra.subset_adjoin ⟨l, by simp only [hl]⟩

end GlobalTheory

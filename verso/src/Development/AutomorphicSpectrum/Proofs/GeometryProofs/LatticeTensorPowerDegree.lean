import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TensDeg

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => simpa using pow_mem h n`. Consider the case `negSucc n`. Rewrite using `[zpow_negSucc, ← inv_pow]`. Conclude with `pow_mem h' _`.
-/
lemma zpow_mem_of_unit {Ω : Type} [Field Ω] (R : Subring Ω) {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (n : ℤ) :
    u ^ n ∈ R := by
  cases n with
  | ofNat n => simpa using pow_mem h n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h' _

/- English proof (translation)
Establish `h1 : s ∈ Submodule.span R {t}` using `h ▸ Submodule.mem_span_singleton_self s`. Establish `h2 : t ∈ Submodule.span R {s}` using `h ▸ Submodule.mem_span_singleton_self t`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 h1`. Take `⟨b, hb⟩` from `Submodule.mem_span_singleton.1 h2`. Establish `ha' : (a : Ω) * t = s` using `ha`.

Establish `hb' : (b : Ω) * s = t` using `hb`. Establish `hba : (b : Ω) * a = 1`. Apply `mul_right_cancel₀ ht` to reduce the goal to its premises. Rewrite using `[_root_.mul_assoc, ha', hb', _root_.one_mul]`. Use `⟨a, a.2, ?_, ha'.symm⟩` and prove the remaining obligations.

Rewrite using `[inv_eq_of_mul_eq_one_left hba]`. Conclude with `b.2`.
-/
lemma exists_unit_of_span_eq {Ω : Type} [Field Ω] (R : Subring Ω) {s t : Ω} (ht : t ≠ 0)
    (h : Submodule.span R {s} = Submodule.span R {t}) : ∃ u, u ∈ R ∧ u⁻¹ ∈ R ∧ s = u * t := by
  have h1 : s ∈ Submodule.span R {t} := h ▸ Submodule.mem_span_singleton_self s
  have h2 : t ∈ Submodule.span R {s} := h ▸ Submodule.mem_span_singleton_self t
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h2
  have ha' : (a : Ω) * t = s := ha
  have hb' : (b : Ω) * s = t := hb
  have hba : (b : Ω) * a = 1 := by
    apply mul_right_cancel₀ ht
    rw [_root_.mul_assoc, ha', hb', _root_.one_mul]
  refine ⟨a, a.2, ?_, ha'.symm⟩
  rw [inv_eq_of_mul_eq_one_left hba]
  exact b.2

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hx, ih]`.
-/
lemma zpow_finset_sum {Ω I : Type} [Field Ω] {x : Ω} (hx : x ≠ 0) (s : Finset I) (f : I → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hx, ih]

end GlobalTheory.CompanionTheory.Ar.TensDeg

open GlobalTheory.CompanionTheory.Ar.TensDeg in

/- English proof (translation)
Introduce `X Ω _ ξ K _ J y I _ Λ T d e h a`. Establish `he : ∀ i, e i ≠ 0` using `fun i => (h i).1`. Use `⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (he i), ?_⟩` and prove the remaining obligations. Introduce `p hp c hc`. Establish `hc0 : ∏ k, y ⟨k, c k⟩ ≠ 0` using `hc.1`.

Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.1 hc0 k (Finset.mem_univ k)`. Set `g : I → Ω` to `fun i => (∏ k, y ⟨k, c k⟩ ^ d i k) • e i`. Establish `hg0 : ∀ i, g i ≠ 0` using `fun i => mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (he i)`. Establish `hgen : ∀ i, (Λ i).IsGenAt p (g i)` using `fun i => ⟨hg0 i, (h i).2 p hp c hc⟩`. Establish `hG : (∏ k, y ⟨k, c k⟩ ^ (∑ i, a i • d i) k) • (∏ i, e i ^ a i) = ∏ i, g i ^ a i`.

Simplify using `only [g, smul_eq_mul, mul_zpow, Finset.prod_mul_distrib]`. Use `congr 1`. Repeatedly rewrite using `[← Finset.prod_zpow]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_apply, zpow_finset_sum (hy k)]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]`. Rewrite using `[hG]`. Apply `le_antisymm` to reduce the goal to its premises.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `t ⟨s, hs, rfl⟩`. Use `choose u hu hu' hsu using fun i => exists_unit_of_span_eq (regAt ξ p) (hg0 i) ((hs i).2.symm.trans (hgen i).2)`. Establish `hm : ∏ i, u i ^ a i ∈ regAt ξ p` using `prod_mem fun i _ => zpow_mem_of_unit _ (hu i) (hu' i) _`. Use `Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩` and prove the remaining obligations.

Use `show (∏ i, u i ^ a i) * ∏ i, g i ^ a i = ∏ i, s i ^ a i`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hsu i, mul_zpow]`. Conclude with `Submodule.span_le.2 (Set.singleton_subset_iff.2 (Submodule.subset_span ⟨g, hgen, rfl⟩))`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (d : I → K → ℤ) (e : I → Ω), (∀ i, (Λ i).IsDegOn T y (d i) (e i)) → ∀ a : I → ℤ, (Lat.tens Λ a).IsDegOn T y (∑ i, a i • d i) (∏ i, e i ^ a i) := by
  intro X Ω _ ξ K _ J y I _ Λ T d e h a
  have he : ∀ i, e i ≠ 0 := fun i => (h i).1
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (he i), ?_⟩
  intro p hp c hc
  have hc0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := hc.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc0 k (Finset.mem_univ k)
  let g : I → Ω := fun i => (∏ k, y ⟨k, c k⟩ ^ d i k) • e i
  have hg0 : ∀ i, g i ≠ 0 := fun i =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (he i)
  have hgen : ∀ i, (Λ i).IsGenAt p (g i) := fun i => ⟨hg0 i, (h i).2 p hp c hc⟩
  have hG : (∏ k, y ⟨k, c k⟩ ^ (∑ i, a i • d i) k) • (∏ i, e i ^ a i) = ∏ i, g i ^ a i := by
    simp only [g, smul_eq_mul, mul_zpow, Finset.prod_mul_distrib]
    congr 1
    simp_rw [← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.sum_apply, zpow_finset_sum (hy k)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]
  rw [hG]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨s, hs, rfl⟩
    choose u hu hu' hsu using fun i =>
      exists_unit_of_span_eq (regAt ξ p) (hg0 i) ((hs i).2.symm.trans (hgen i).2)
    have hm : ∏ i, u i ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_mem_of_unit _ (hu i) (hu' i) _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
    show (∏ i, u i ^ a i) * ∏ i, g i ^ a i = ∏ i, s i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hsu i, mul_zpow]
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (Submodule.subset_span ⟨g, hgen, rfl⟩))

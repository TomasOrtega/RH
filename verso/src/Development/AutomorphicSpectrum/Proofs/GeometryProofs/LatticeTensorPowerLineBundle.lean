import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace LatTens

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Take `⟨_, hsΛ⟩` from `hs`. Take `⟨ht0, htΛ⟩` from `ht`. Establish `hmem : s ∈ Submodule.span (regAt ξ p) ({t} : Set Ω)`. Rewrite using `[← htΛ, hsΛ]`. Conclude with `Submodule.mem_span_singleton_self s`.

Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.mp hmem`. Establish `hr' : (r : Ω) * t = s` using `by first`. Consider the case `exact hr`. Consider the case `simpa [Subring.smul_def] using hr`. Rewrite using `[← hr', mul_div_assoc, div_self ht0, _root_.mul_one]`.

Conclude with `r.2`.
-/
theorem div_mem_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s)
    (ht : Λ.IsGenAt p t) : s / t ∈ regAt ξ p := by
  obtain ⟨_, hsΛ⟩ := hs
  obtain ⟨ht0, htΛ⟩ := ht
  have hmem : s ∈ Submodule.span (regAt ξ p) ({t} : Set Ω) := by
    rw [← htΛ, hsΛ]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have hr' : (r : Ω) * t = s := by
    first
    | exact hr
    | simpa [Subring.smul_def] using hr
  rw [← hr', mul_div_assoc, div_self ht0, _root_.mul_one]
  exact r.2

/- English proof (translation)
Consider the cases of `a with`. Consider the case `ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using pow_mem h n`. Consider the case `negSucc n => simpa only [zpow_negSucc, inv_pow] using pow_mem h' (n + 1)`.
-/
theorem zpow_mem_of_inv_mem {R : Subring Ω} {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (a : ℤ) : u ^ a ∈ R := by
  cases a with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using pow_mem h n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using pow_mem h' (n + 1)

/- English proof (translation)
Rewrite using `[show Lat.tens Λ a p = Submodule.span (regAt ξ p) {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i} from rfl]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `t ⟨s', hs', rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_singleton]`.

Use `⟨⟨∏ i, (s' i / s i) ^ a i, ?_⟩, ?_⟩` and prove the remaining obligations. Use `prod_mem fun i _ => zpow_mem_of_inv_mem (div_mem_of_isGenAt (hs' i) (hs i)) ?_ (a i)` and prove the remaining obligations. Rewrite using `[inv_div]`. Conclude with `div_mem_of_isGenAt (hs i) (hs' i)`. Use `show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_zpow, div_mul_cancel₀ _ (hs i).1]`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `Submodule.subset_span ⟨s, hs, rfl⟩`.
-/
theorem tens_eq_span {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) :
    Lat.tens Λ a p = Submodule.span (regAt ξ p) {∏ i, s i ^ a i} := by
  rw [show Lat.tens Λ a p = Submodule.span (regAt ξ p)
      {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i} from rfl]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨s', hs', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨∏ i, (s' i / s i) ^ a i, ?_⟩, ?_⟩
    · refine prod_mem fun i _ => zpow_mem_of_inv_mem (div_mem_of_isGenAt (hs' i) (hs i)) ?_ (a i)
      rw [inv_div]
      exact div_mem_of_isGenAt (hs i) (hs' i)
    · show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨s, hs, rfl⟩

/- English proof (translation)
Use `⟨?_, tens_eq_span Λ a p s hs⟩` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1`.
-/
theorem isGenAt_tens {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨?_, tens_eq_span Λ a p s hs⟩
  exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1

/- English proof (translation)
Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.inf_empty]`. Conclude with `⟨fun _ i hi => by simp at hi, fun _ => TopologicalSpace.Opens.mem_top x⟩`. Introduce `j S' _ ih`. Rewrite using `[Finset.inf_insert, TopologicalSpace.Opens.mem_inf, ih]`.

Rewrite using `[Finset.forall_mem_insert]`.
-/
theorem mem_finset_inf {I : Type} (S : Finset I) (U : I → X.Opens) (x : X) :
    x ∈ S.inf U ↔ ∀ i ∈ S, x ∈ U i := by
  classical
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.inf_empty]
    exact ⟨fun _ i hi => by simp at hi, fun _ => TopologicalSpace.Opens.mem_top x⟩
  · intro j S' _ ih
    rw [Finset.inf_insert, TopologicalSpace.Opens.mem_inf, ih]
    rw [Finset.forall_mem_insert]

/- English proof (translation)
Use `⟨LinearIndependent.ne_zero 0 h.1, ?_⟩` and prove the remaining obligations. Rewrite using `[h.2, Set.range_unique, Subsingleton.elim (default : Fin 1) 0]`.
-/
theorem isGenAt_of_isFrameAt {Λ : Lat ξ Ω} {b : Fin 1 → Ω} {p : Cpt ξ} (h : Λ.IsFrameAt b p) :
    Λ.IsGenAt p (b 0) := by
  refine ⟨LinearIndependent.ne_zero 0 h.1, ?_⟩
  rw [h.2, Set.range_unique, Subsingleton.elim (default : Fin 1) 0]

/- English proof (translation)
Use `⟨linearIndependent_unique_iff.mpr h.1, ?_⟩` and prove the remaining obligations. Rewrite using `[h.2, Set.range_const]`.
-/
theorem isFrameAt_of_isGenAt {Λ : Lat ξ Ω} {c : Ω} {p : Cpt ξ} (h : Λ.IsGenAt p c) :
    Λ.IsFrameAt (fun _ : Fin 1 => c) p := by
  refine ⟨linearIndependent_unique_iff.mpr h.1, ?_⟩
  rw [h.2, Set.range_const]

/- English proof (translation)
Use `⟨?_, fun p _ s hs => isGenAt_tens Λ a p s hs⟩` and prove the remaining obligations. Introduce `p hp`. Use `choose U hpU b _ hfr using fun i => h i p hp`. Use `⟨Finset.univ.inf U, (mem_finset_inf _ _ _).mpr fun i _ => hpU i, fun _ => ∏ i, b i 0 ^ a i, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : (∏ i, b i 0 ^ a i) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (LinearIndependent.ne_zero 0 (hfr i p hp (hpU i)).1)`.

Rewrite using `[Set.range_const, eq_top_iff]`. Introduce `y _`. Rewrite using `[Submodule.mem_span_singleton]`. Conclude with `⟨y / ∏ i, b i 0 ^ a i, by rw [smul_eq_mul, div_mul_cancel₀ _ hc]⟩`. Introduce `q hq hqU`.

Rewrite `hqU` using `[mem_finset_inf]`. Conclude with `isFrameAt_of_isGenAt (isGenAt_tens Λ a q (fun i => b i 0) fun i => isGenAt_of_isFrameAt (hfr i q hq (hqU i (Finset.mem_univ i))))`.
-/
theorem tens_isVBOn (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (I : Type)
    [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (h : ∀ i, (Λ i).IsVBOn T 1 ⊤) (a : I → ℤ) :
    (Lat.tens Λ a).IsVBOn T 1 ⊤ ∧ ∀ p ∈ T, ∀ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) →
      (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨?_, fun p _ s hs => isGenAt_tens Λ a p s hs⟩
  intro p hp
  choose U hpU b _ hfr using fun i => h i p hp
  refine ⟨Finset.univ.inf U, (mem_finset_inf _ _ _).mpr fun i _ => hpU i,
    fun _ => ∏ i, b i 0 ^ a i, ?_, ?_⟩
  · have hc : (∏ i, b i 0 ^ a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
      zpow_ne_zero _ (LinearIndependent.ne_zero 0 (hfr i p hp (hpU i)).1)
    rw [Set.range_const, eq_top_iff]
    intro y _
    rw [Submodule.mem_span_singleton]
    exact ⟨y / ∏ i, b i 0 ^ a i, by rw [smul_eq_mul, div_mul_cancel₀ _ hc]⟩
  · intro q hq hqU
    rw [mem_finset_inf] at hqU
    exact isFrameAt_of_isGenAt (isGenAt_tens Λ a q (fun i => b i 0) fun i =>
      isGenAt_of_isFrameAt (hfr i q hq (hqU i (Finset.mem_univ i))))

end LatTens

end GlobalTheory.CompanionTheory.Ar

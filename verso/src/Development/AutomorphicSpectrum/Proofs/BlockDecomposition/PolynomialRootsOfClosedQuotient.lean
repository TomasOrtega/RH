import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.RootsUpToUnits

/- English proof (translation)
Establish `hu` using `(Ideal.mem_jacobson_bot.mp hJ) (-c)`. Rewrite `hu` using `[mul_neg, h, neg_add_cancel]`. Conclude with `subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)`.
-/
theorem subsingleton_of_mul_eq_one {S : Type} [CommRing S] {ϖ c : S}
    (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) (h : ϖ * c = 1) : Subsingleton S := by
  have hu := (Ideal.mem_jacobson_bot.mp hJ) (-c)
  rw [mul_neg, h, neg_add_cancel] at hu
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)

/- English proof (translation)
Proceed by induction on `M generalizing f with`. Consider the case `zero => left`. Simplify using the standard rewrite rules. Consider the case `succ M ih`. Break down `h f with ⟨g, rfl⟩ | hf` into its components or cases.

Break down `ih g with hg | ⟨j, f', rfl, hf'⟩` into its components or cases. Use `left`. Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul_left ϖ hg`. Use the proof step `right; exact ⟨j + 1, f', by ring, hf'⟩`.

Use the proof step `right; exact ⟨0, f, by simp, hf⟩`.
-/
theorem normal_form {S : Type} [CommRing S] (ϖ : S) (h : ∀ f : S, ϖ ∣ f ∨ f ∣ ϖ) (f : S) (M : ℕ) :
    ϖ ^ M ∣ f ∨ ∃ (j : ℕ) (f' : S), f = ϖ ^ j * f' ∧ f' ∣ ϖ := by
  induction M generalizing f with
  | zero => left; simp
  | succ M ih =>
    rcases h f with ⟨g, rfl⟩ | hf
    · rcases ih g with hg | ⟨j, f', rfl, hf'⟩
      · left; rw [pow_succ']; exact mul_dvd_mul_left ϖ hg
      · right; exact ⟨j + 1, f', by ring, hf'⟩
    · right; exact ⟨0, f, by simp, hf⟩

/- English proof (translation)
Take `⟨h, hh⟩` from `hg`. Distinguish the cases in `hn : Nontrivial (S ⧸ Ideal.span {ϖ ^ 2})`. Use `haveI := hn`. Take `⟨x, hx⟩` from `hA (Polynomial.X ^ i - Polynomial.C (Ideal.Quotient.mk _ g)) (Polynomial.monic_X_pow_sub_C _ hi.ne') (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hi)`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Establish `hx' : (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) r) ^ i - Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) g = 0`. Simplify using `using hx`. Establish `hmem : r ^ i - g ∈ Ideal.span {ϖ ^ 2}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]`. Conclude with `hx'`.

Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.mp hmem`. Establish `hu` using `(Ideal.mem_jacobson_bot.mp hJ) (t * h)`. Establish `key : r ^ i = g * (ϖ * (t * h) + 1)`. Establish `e1 : r ^ i = g + t * ϖ ^ 2` using `by rw [ht]; ring`. Rewrite using `[e1, hh]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨r, hu.unit⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Combine the equalities or inequalities in the displayed calculation. Establish `hs : Subsingleton (S ⧸ Ideal.span {ϖ ^ 2})` using `not_nontrivial_iff_subsingleton.mp hn`.

Establish `h1 : (1 : S) ∈ Ideal.span {ϖ ^ 2}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Subsingleton.elim _ _`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp h1`. Establish `hS : Subsingleton S` using `subsingleton_of_mul_eq_one (c := ϖ * a) hJ (by rw [← ha]; ring)`.

Conclude with `⟨1, 1, Subsingleton.elim _ _⟩`.
-/
theorem root_of_dvd {S : Type} [CommRing S] {ϖ g : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson)
    (hA : Aic (S ⧸ Ideal.span {ϖ ^ 2})) (hg : g ∣ ϖ) {i : ℕ} (hi : 0 < i) :
    ∃ (r : S) (u : Sˣ), g = u * r ^ i := by
  obtain ⟨h, hh⟩ := hg
  by_cases hn : Nontrivial (S ⧸ Ideal.span {ϖ ^ 2})
  · haveI := hn
    obtain ⟨x, hx⟩ := hA (Polynomial.X ^ i - Polynomial.C (Ideal.Quotient.mk _ g))
      (Polynomial.monic_X_pow_sub_C _ hi.ne') (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hi)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) r) ^ i - Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) g = 0 := by
      simpa using hx
    have hmem : r ^ i - g ∈ Ideal.span {ϖ ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      exact hx'
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    have hu := (Ideal.mem_jacobson_bot.mp hJ) (t * h)
    have key : r ^ i = g * (ϖ * (t * h) + 1) := by
      have e1 : r ^ i = g + t * ϖ ^ 2 := by rw [ht]; ring
      rw [e1, hh]; ring
    refine ⟨r, hu.unit⁻¹, ?_⟩
    rw [key]
    calc g = ((↑hu.unit⁻¹ : S) * (ϖ * (t * h) + 1)) * g := by rw [hu.val_inv_mul, one_mul]
      _ = (↑hu.unit⁻¹ : S) * (g * (ϖ * (t * h) + 1)) := by ring
  · have hs : Subsingleton (S ⧸ Ideal.span {ϖ ^ 2}) := not_nontrivial_iff_subsingleton.mp hn
    have h1 : (1 : S) ∈ Ideal.span {ϖ ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Subsingleton.elim _ _
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    have hS : Subsingleton S := subsingleton_of_mul_eq_one (c := ϖ * a) hJ (by rw [← ha]; ring)
    exact ⟨1, 1, Subsingleton.elim _ _⟩

/- English proof (translation)
Introduce `S _ ϖ hJ hϖ hD hA f N i hf hi`. Establish `hdich : ∀ g : S, ϖ ∣ g ∨ g ∣ ϖ` using `fun g => hD g ϖ ⟨1, by rw [pow_one]; exact Ideal.subset_span (by simp)⟩`. Break down `normal_form ϖ hdich f (N + 1) with hM | ⟨j, f', rfl, hf'⟩` into its components or cases. Take `⟨k, hk⟩` from `dvd_trans hM hf`. Establish `e0 : (1 - ϖ * k) * ϖ ^ N = 0` using `by linear_combination hk`.

Establish `e1 : 1 - ϖ * k = 0` using `(mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hϖ N)).mp e0`. Establish `hS : Subsingleton S` using `subsingleton_of_mul_eq_one (c := k) hJ (by linear_combination -e1)`. Conclude with `⟨1, 1, Subsingleton.elim _ _⟩`. Take `⟨r0, u0, h0⟩` from `root_of_dvd hJ hA (dvd_refl ϖ) hi`. Take `⟨r, u, hr⟩` from `root_of_dvd hJ hA hf' hi`.

Use `⟨r0 ^ j * r, u0 ^ j * u, ?_⟩` and prove the remaining obligations. Rewrite using `[hr, h0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem roots_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S ⧸ Ideal.span {ϖ ^ 2}) → Roots ϖ := by
  intro S _ ϖ hJ hϖ hD hA f N i hf hi
  have hdich : ∀ g : S, ϖ ∣ g ∨ g ∣ ϖ := fun g =>
    hD g ϖ ⟨1, by rw [pow_one]; exact Ideal.subset_span (by simp)⟩
  rcases normal_form ϖ hdich f (N + 1) with hM | ⟨j, f', rfl, hf'⟩
  · obtain ⟨k, hk⟩ := dvd_trans hM hf
    have e0 : (1 - ϖ * k) * ϖ ^ N = 0 := by linear_combination hk
    have e1 : 1 - ϖ * k = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hϖ N)).mp e0
    have hS : Subsingleton S := subsingleton_of_mul_eq_one (c := k) hJ (by linear_combination -e1)
    exact ⟨1, 1, Subsingleton.elim _ _⟩
  · obtain ⟨r0, u0, h0⟩ := root_of_dvd hJ hA (dvd_refl ϖ) hi
    obtain ⟨r, u, hr⟩ := root_of_dvd hJ hA hf' hi
    refine ⟨r0 ^ j * r, u0 ^ j * u, ?_⟩
    rw [hr, h0]; push_cast; ring

end GlobalTheory.CompanionTheory.RootsUpToUnits

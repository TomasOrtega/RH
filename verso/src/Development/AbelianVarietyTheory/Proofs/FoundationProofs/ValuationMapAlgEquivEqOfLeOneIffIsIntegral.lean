import Mathlib
open scoped NNReal TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `hle : ∀ a b : Ω, v (g a) ≤ v (g b) ↔ v a ≤ v b`. Introduce `a b`. Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules.

Establish `hgb : g b ≠ 0` using `by simpa using hb`. Establish `hvb : 0 < v b` using `by simpa [pos_iff_ne_zero] using hb`. Establish `hvgb : 0 < v (g b)` using `by simpa [pos_iff_ne_zero] using hgb`. Establish `h1 : v (a / b) ≤ 1 ↔ v a ≤ v b` using `by rw [map_div₀, div_le_one hvb]`. Establish `h2 : v (g (a / b)) ≤ 1 ↔ v (g a) ≤ v (g b)`.

Rewrite using `[map_div₀ g, map_div₀, div_le_one hvgb]`. Rewrite using `[← h1, ← h2, hv, hv, isIntegral_algEquiv]`. Establish `hlt : ∀ a b : Ω, v (g a) < v (g b) ↔ v a < v b`. Introduce `a b`. Rewrite using `[← not_le, ← not_le, hle]`.

Choose the witnesses or unpack the hypotheses as in `⟨k, l, hkl, heq⟩ : ∃ k l : ℕ, k < l ∧ (g ^ k) x = (g ^ l) x := by`. Take `⟨p, hp0, hpx⟩` from `Algebra.IsAlgebraic.isAlgebraic (R := R) x`. Establish `hmap : p.map (algebraMap R Ω) ≠ 0`. Rewrite using `[Ne, Polynomial.map_eq_zero_iff hinj]` and apply the resulting hypothesis. Establish `hsub : Set.range (fun k : ℕ => (g ^ k) x) ⊆ p.rootSet Ω`.

Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[Polynomial.mem_rootSet']`. Use `⟨hmap, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_algEquiv]`. Simplify using `[hpx]`.

Establish `hfin` using `(Polynomial.rootSet_finite p Ω).subset hsub`. Establish `hni : ¬ Function.Injective (fun k : ℕ => (g ^ k) x)` using `fun hi => Set.infinite_range_of_injective hi hfin`. Simplify using `only [Function.Injective, not_forall] at hni`. Take `⟨a, b, hab, hne⟩` from `hni`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases.

Conclude with `⟨a, b, h, hab⟩`. Conclude with `⟨b, a, h, hab.symm⟩`. Establish `hstep : ∀ k : ℕ, (g ^ (k + 1)) x = g ((g ^ k) x)`. Introduce `k`. Rewrite using `[pow_succ', AlgEquiv.mul_apply]`.

Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Establish `hs : ∀ n : ℕ, v ((g ^ (n + 1)) x) < v ((g ^ n) x)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Rewrite using `[hstep (n + 1), hstep n, hlt]`. Rewrite `ih` using `[hstep n]`. Simplify `ih` using `[hstep]`.

Establish `hanti : StrictAnti (fun n : ℕ => v ((g ^ n) x))` using `strictAnti_nat_of_succ_lt hs`. Use `hanti hkl` as an intermediate fact. Simplify using `only [heq] at this`. Conclude with `lt_irrefl _ this`. Establish `hs : ∀ n : ℕ, v ((g ^ n) x) < v ((g ^ (n + 1)) x)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Rewrite using `[hstep (n + 1), hstep n, hlt]`.

Rewrite `ih` using `[hstep n]`. Simplify `ih` using `[hstep]`. Establish `hmono : StrictMono (fun n : ℕ => v ((g ^ n) x))` using `strictMono_nat_of_lt_succ hs`. Use `hmono hkl` as an intermediate fact. Simplify using `only [heq] at this`.

Conclude with `lt_irrefl _ this`.
-/
theorem valuation_map_algEquiv_eq_of_le_one_iff_isIntegral (R Ω : Type) [CommRing R] [Nontrivial R]
    [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω]
    (hinj : Function.Injective (algebraMap R Ω)) (v : Valuation Ω ℝ≥0)
    (hv : ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x) (g : Ω ≃ₐ[R] Ω) (x : Ω) : v (g x) = v x := by
  have hle : ∀ a b : Ω, v (g a) ≤ v (g b) ↔ v a ≤ v b := by
    intro a b
    by_cases hb : b = 0
    · subst hb
      simp
    · have hgb : g b ≠ 0 := by simpa using hb
      have hvb : 0 < v b := by simpa [pos_iff_ne_zero] using hb
      have hvgb : 0 < v (g b) := by simpa [pos_iff_ne_zero] using hgb
      have h1 : v (a / b) ≤ 1 ↔ v a ≤ v b := by rw [map_div₀, div_le_one hvb]
      have h2 : v (g (a / b)) ≤ 1 ↔ v (g a) ≤ v (g b) := by
        rw [map_div₀ g, map_div₀, div_le_one hvgb]
      rw [← h1, ← h2, hv, hv, isIntegral_algEquiv]
  have hlt : ∀ a b : Ω, v (g a) < v (g b) ↔ v a < v b := by
    intro a b
    rw [← not_le, ← not_le, hle]
  obtain ⟨k, l, hkl, heq⟩ : ∃ k l : ℕ, k < l ∧ (g ^ k) x = (g ^ l) x := by
    obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) x
    have hmap : p.map (algebraMap R Ω) ≠ 0 := by
      rwa [Ne, Polynomial.map_eq_zero_iff hinj]
    have hsub : Set.range (fun k : ℕ => (g ^ k) x) ⊆ p.rootSet Ω := by
      rintro _ ⟨k, rfl⟩
      rw [Polynomial.mem_rootSet']
      refine ⟨hmap, ?_⟩
      rw [Polynomial.aeval_algEquiv]
      simp [hpx]
    have hfin := (Polynomial.rootSet_finite p Ω).subset hsub
    have hni : ¬ Function.Injective (fun k : ℕ => (g ^ k) x) := fun hi =>
      Set.infinite_range_of_injective hi hfin
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, h, hab⟩
    · exact ⟨b, a, h, hab.symm⟩
  have hstep : ∀ k : ℕ, (g ^ (k + 1)) x = g ((g ^ k) x) := by
    intro k
    rw [pow_succ', AlgEquiv.mul_apply]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : ∀ n : ℕ, v ((g ^ (n + 1)) x) < v ((g ^ n) x) := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n, hlt]
        rw [hstep n] at ih
        simpa [hstep] using ih
    have hanti : StrictAnti (fun n : ℕ => v ((g ^ n) x)) := strictAnti_nat_of_succ_lt hs
    have := hanti hkl
    simp only [heq] at this
    exact lt_irrefl _ this
  · have hs : ∀ n : ℕ, v ((g ^ n) x) < v ((g ^ (n + 1)) x) := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n, hlt]
        rw [hstep n] at ih
        simpa [hstep] using ih
    have hmono : StrictMono (fun n : ℕ => v ((g ^ n) x)) := strictMono_nat_of_lt_succ hs
    have := hmono hkl
    simp only [heq] at this
    exact lt_irrefl _ this

end GlobalTheory

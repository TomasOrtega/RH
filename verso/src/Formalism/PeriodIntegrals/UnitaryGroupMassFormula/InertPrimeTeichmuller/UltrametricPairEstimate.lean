import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.TeichNeZero

open NumberField Filter Topology

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

def gens (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  {x | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)}

/- English proof (translation)
Distinguish the cases in `h0 : t = 0`. Substitute `h0` using the available equality. Establish `e : ((0 : ℂ_[p]), (0 : ℂ_[p]) ^ p) = 0`. Simplify using `[zero_pow hp.out.ne_zero]`. Rewrite using `[e]`.

Conclude with `zero_mem _`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `⟨t, ?_, rfl⟩` and prove the remaining obligations. Establish `h1 : 1 ≤ p ^ 2` using `Nat.one_le_pow _ _ hp.out.pos`. Establish `e : t ^ (p ^ 2 - 1) * t = 1 * t`.

Rewrite using `[← pow_succ, Nat.sub_add_cancel h1, ht, one_mul]`. Conclude with `mul_right_cancel₀ h0 e`.
-/
theorem pair_mem_of_pow (t : ℂ_[p]) (ht : t ^ (p ^ 2) = t) :
    (t, t ^ p) ∈ Subring.closure (gens p) := by
  by_cases h0 : t = 0
  · subst h0
    have e : ((0 : ℂ_[p]), (0 : ℂ_[p]) ^ p) = 0 := by
      simp [zero_pow hp.out.ne_zero]
    rw [e]
    exact zero_mem _
  · apply Subring.subset_closure
    refine ⟨t, ?_, rfl⟩
    have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    have e : t ^ (p ^ 2 - 1) * t = 1 * t := by
      rw [← pow_succ, Nat.sub_add_cancel h1, ht, one_mul]
    exact mul_right_cancel₀ h0 e

/- English proof (translation)
Establish `e : (X - (p : ℂ_[p]) * Y) - (T - (p : ℂ_[p]) * R) = (X - T) - (p : ℂ_[p]) * (Y - R)` using `by ring`. Rewrite using `[e, ← dist_eq_norm]`. Use `(IsUltrametricDist.dist_triangle_max _ 0 _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[dist_zero_right, norm_sub_rev]`. Conclude with `h1`.

Rewrite using `[dist_zero_left, norm_mul, norm_p_cp, pow_succ']`. Conclude with `mul_le_mul_of_nonneg_left h2 (by positivity)`.
-/
theorem positionOne_invariantIntegral_exchange_step (X T Y R : ℂ_[p]) (n : ℕ) (h1 : ‖T - X‖ ≤ (p : ℝ)⁻¹ ^ (n + 1))
    (h2 : ‖Y - R‖ ≤ (p : ℝ)⁻¹ ^ n) :
    ‖(X - (p : ℂ_[p]) * Y) - (T - (p : ℂ_[p]) * R)‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) := by
  have e : (X - (p : ℂ_[p]) * Y) - (T - (p : ℂ_[p]) * R) = (X - T) - (p : ℂ_[p]) * (Y - R) := by ring
  rw [e, ← dist_eq_norm]
  refine (IsUltrametricDist.dist_triangle_max _ 0 _).trans (max_le ?_ ?_)
  · rw [dist_zero_right, norm_sub_rev]
    exact h1
  · rw [dist_zero_left, norm_mul, norm_p_cp, pow_succ']
    exact mul_le_mul_of_nonneg_left h2 (by positivity)

/- English proof (translation)
Establish `hq1 : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b` using `fun b => by simpa using hqn b 1`. Set `φ : 𝓞 K →+* ℂ_[p]` to `τ.comp (algebraMap (𝓞 K) K)`. Proceed by induction on `n generalizing a with`. Consider the case `zero`. Use `⟨0, zero_mem _, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `using norm_tau_le τ a`. Simplify using `using norm_tau_le τ (cO a)`. Consider the case `succ n ih`. Take `⟨c, hc⟩` from `hqn a n`. Take `⟨r', hr', h1, h2⟩` from `ih (-c)`.

Use `set T := teich τ a with hT`. Establish `hTc : teich τ (cO a) = T ^ p` using `teich_c τ hq1 a (cO a) (hfrob a)`. Establish `rel1 : φ (a ^ ((p ^ 2) ^ n)) - φ a = (p : ℂ_[p]) * φ c`. Establish `h` using `congrArg φ hc`. Simplify `h` using `only [map_sub, map_mul, map_natCast]`.

Establish `rel2 : φ (cO a ^ ((p ^ 2) ^ n)) - φ (cO a) = (p : ℂ_[p]) * φ (cO c)`. Establish `h` using `congrArg (φ.comp cO) hc`. Simplify `h` using `only [RingHom.comp_apply, map_sub, map_mul, map_natCast, map_pow]`. Establish `hn1 : φ (-c) = -φ c` using `map_neg φ c`. Establish `hn2 : φ (cO (-c)) = -φ (cO c)` using `by rw [map_neg, map_neg]`.

Establish `k1 : ‖T - φ (a ^ ((p ^ 2) ^ n))‖ ≤ (p : ℝ)⁻¹ ^ (n + 1)` using `(teich_spec τ hq1 a).2 n`. Establish `k2 : ‖T ^ p - φ (cO a ^ ((p ^ 2) ^ n))‖ ≤ (p : ℝ)⁻¹ ^ (n + 1)`. Rewrite using `[← hTc]`. Conclude with `(teich_spec τ hq1 (cO a)).2 n`. Establish `j1 : ‖r'.1 - φ (-c)‖ ≤ (p : ℝ)⁻¹ ^ n`.

Rewrite using `[norm_sub_rev]`. Conclude with `h1`. Establish `j2 : ‖r'.2 - φ (cO (-c))‖ ≤ (p : ℝ)⁻¹ ^ n`. Rewrite using `[norm_sub_rev]`. Conclude with `h2`.

Use `⟨(T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r', ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Subring.add_mem _ (pair_mem_of_pow T (teich_pow τ hq1 a)) (Subring.mul_mem _ (natCast_mem _ p) hr')`. Establish `s` using `positionOne_invariantIntegral_exchange_step _ _ _ _ n k1 j1`. Establish `e : τ (a : K) - ((T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r').1 = (φ (a ^ ((p ^ 2) ^ n)) - (p : ℂ_[p]) * r'.1) - (T - (p : ℂ_[p]) * φ (-c))`. Simplify using `only [Prod.fst_add, Prod.fst_mul, Prod.fst_natCast]`.

Express the relevant statement in the definitionally equal form `φ a - _ = _`. Rewrite using `[hn1]`. Take the linear combination `-rel1`. Rewrite using `[e]`. Conclude with `s`.

Establish `s` using `positionOne_invariantIntegral_exchange_step _ _ _ _ n k2 j2`. Establish `e : τ ((cO a : 𝓞 K) : K) - ((T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r').2 = (φ (cO a ^ ((p ^ 2) ^ n)) - (p : ℂ_[p]) * r'.2) - (T ^ p - (p : ℂ_[p]) * φ (cO (-c)))`. Simplify using `only [Prod.snd_add, Prod.snd_mul, Prod.snd_natCast]`. Express the relevant statement in the definitionally equal form `φ (cO a) - _ = _`. Rewrite using `[hn2]`.

Take the linear combination `-rel2`. Rewrite using `[e]`. Conclude with `s`.
-/
theorem approx (τ : K →+* ℂ_[p]) (cO : 𝓞 K →+* 𝓞 K)
    (hqn : ∀ (a : 𝓞 K) (n : ℕ), (p : 𝓞 K) ∣ a ^ ((p ^ 2) ^ n) - a)
    (hfrob : ∀ a : 𝓞 K, (p : 𝓞 K) ∣ cO a - a ^ p) (n : ℕ) (a : 𝓞 K) :
    ∃ r ∈ Subring.closure (gens p), ‖τ (a : K) - r.1‖ ≤ (p : ℝ)⁻¹ ^ n ∧
      ‖τ ((cO a : 𝓞 K) : K) - r.2‖ ≤ (p : ℝ)⁻¹ ^ n := by
  have hq1 : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b := fun b => by simpa using hqn b 1
  let φ : 𝓞 K →+* ℂ_[p] := τ.comp (algebraMap (𝓞 K) K)
  induction n generalizing a with
  | zero =>
    refine ⟨0, zero_mem _, ?_, ?_⟩
    · simpa using norm_tau_le τ a
    · simpa using norm_tau_le τ (cO a)
  | succ n ih =>
    obtain ⟨c, hc⟩ := hqn a n
    obtain ⟨r', hr', h1, h2⟩ := ih (-c)
    set T := teich τ a with hT
    have hTc : teich τ (cO a) = T ^ p := teich_c τ hq1 a (cO a) (hfrob a)

    have rel1 : φ (a ^ ((p ^ 2) ^ n)) - φ a = (p : ℂ_[p]) * φ c := by
      have h := congrArg φ hc
      simpa only [map_sub, map_mul, map_natCast] using h
    have rel2 : φ (cO a ^ ((p ^ 2) ^ n)) - φ (cO a) = (p : ℂ_[p]) * φ (cO c) := by
      have h := congrArg (φ.comp cO) hc
      simpa only [RingHom.comp_apply, map_sub, map_mul, map_natCast, map_pow] using h
    have hn1 : φ (-c) = -φ c := map_neg φ c
    have hn2 : φ (cO (-c)) = -φ (cO c) := by rw [map_neg, map_neg]
    have k1 : ‖T - φ (a ^ ((p ^ 2) ^ n))‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) := (teich_spec τ hq1 a).2 n
    have k2 : ‖T ^ p - φ (cO a ^ ((p ^ 2) ^ n))‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) := by
      rw [← hTc]
      exact (teich_spec τ hq1 (cO a)).2 n
    have j1 : ‖r'.1 - φ (-c)‖ ≤ (p : ℝ)⁻¹ ^ n := by
      rw [norm_sub_rev]
      exact h1
    have j2 : ‖r'.2 - φ (cO (-c))‖ ≤ (p : ℝ)⁻¹ ^ n := by
      rw [norm_sub_rev]
      exact h2
    refine ⟨(T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r', ?_, ?_, ?_⟩
    · exact Subring.add_mem _ (pair_mem_of_pow T (teich_pow τ hq1 a))
        (Subring.mul_mem _ (natCast_mem _ p) hr')
    · have s := positionOne_invariantIntegral_exchange_step _ _ _ _ n k1 j1
      have e : τ (a : K) - ((T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r').1 =
          (φ (a ^ ((p ^ 2) ^ n)) - (p : ℂ_[p]) * r'.1) - (T - (p : ℂ_[p]) * φ (-c)) := by
        simp only [Prod.fst_add, Prod.fst_mul, Prod.fst_natCast]
        change φ a - _ = _
        rw [hn1]
        linear_combination -rel1
      rw [e]
      exact s
    · have s := positionOne_invariantIntegral_exchange_step _ _ _ _ n k2 j2
      have e : τ ((cO a : 𝓞 K) : K) - ((T, T ^ p) + (p : ℂ_[p] × ℂ_[p]) * r').2 =
          (φ (cO a ^ ((p ^ 2) ^ n)) - (p : ℂ_[p]) * r'.2) - (T ^ p - (p : ℂ_[p]) * φ (cO (-c))) := by
        simp only [Prod.snd_add, Prod.snd_mul, Prod.snd_natCast]
        change φ (cO a) - _ = _
        rw [hn2]
        linear_combination -rel2
      rw [e]
      exact s

end PI.OkpW

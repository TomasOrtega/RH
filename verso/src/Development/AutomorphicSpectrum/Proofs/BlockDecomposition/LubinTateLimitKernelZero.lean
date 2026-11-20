import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

/- English proof (translation)
Introduce `B _ S F ϖ C _ _ ϖ' hϖ θ hker hS hlt q hq Q hQ t ht`. Establish `hy : ∀ n, θ (ltIter ϖ q n Q) = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa [ltIter] using hQ`.

Consider the case `succ n ih`. Establish `hs : ltIter ϖ q (n + 1) Q = ϖ * ltIter ϖ q n Q + (ltIter ϖ q n Q) ^ q`. Simplify using `only [ltIter, Function.iterate_succ_apply']`. Rewrite using `[hs, map_add, map_mul, map_pow, ih]`. Simplify using `[show q ≠ 0 by omega]`.

Establish `hne : θ ϖ ≠ 0`. Introduce `h0`. Establish `h1 : θ ϖ * θ ϖ' = 1` using `by rw [← map_mul, hϖ, map_one]`. Rewrite `h1` using `[h0, zero_mul]`. Conclude with `zero_ne_one h1`.

Establish `hapos : 0 < ‖θ ϖ‖` using `norm_pos_iff.mpr hne`. Take `⟨c, hc⟩` from `ht 1`. Establish `hbound : ∀ m : ℕ, ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ ‖θ ϖ‖ ^ m`. Introduce `m`. Take `⟨N, hN⟩` from `hc m`.

Take `⟨s, hsS, hs⟩` from `hN N le_rfl`. Establish `h0` using `(hker _).mpr hs`. Simplify using `only [map_sub, map_mul, map_pow, hy, mul_zero, zero_sub] at h0`. Establish `h1 : θ ϖ ^ c * θ t = -(θ ϖ ^ m * θ s)` using `by linear_combination -h0`. Establish `h2 : ‖θ ϖ‖ ^ c * ‖θ t‖ = ‖θ ϖ‖ ^ m * ‖θ s‖`.

Use `congrArg norm h1` as an intermediate fact. Simplify `this` using `[norm_mul, norm_pow, norm_neg]`. Rewrite using `[h2]`. Conclude with `mul_le_of_le_one_right (pow_nonneg hapos.le m) (hS s hsS)`. Establish `hlim : Filter.Tendsto (fun m : ℕ => ‖θ ϖ‖ ^ m) Filter.atTop (nhds 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one hapos.le hlt`.

Establish `hle : ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ 0` using `ge_of_tendsto' hlim hbound`. Establish `hz : ‖θ t‖ ≤ 0`. Assume the negation of the conclusion as `hcon`. Establish `: 0 < ‖θ ϖ‖ ^ c * ‖θ t‖` using `mul_pos (pow_pos hapos c) (not_le.mp hcon)`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `norm_le_zero_iff.mp hz`.
-/
theorem theta_period_eq_zero_of_theta_eq_zero :
    ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q, θ Q = 0 → ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → θ t = 0 := by
  intro B _ S F ϖ C _ _ ϖ' hϖ θ hker hS hlt q hq Q hQ t ht
  have hy : ∀ n, θ (ltIter ϖ q n Q) = 0 := by
    intro n
    induction n with
    | zero => simpa [ltIter] using hQ
    | succ n ih =>
      have hs : ltIter ϖ q (n + 1) Q = ϖ * ltIter ϖ q n Q + (ltIter ϖ q n Q) ^ q := by
        simp only [ltIter, Function.iterate_succ_apply']
      rw [hs, map_add, map_mul, map_pow, ih]
      simp [show q ≠ 0 by omega]
  have hne : θ ϖ ≠ 0 := by
    intro h0
    have h1 : θ ϖ * θ ϖ' = 1 := by rw [← map_mul, hϖ, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hapos : 0 < ‖θ ϖ‖ := norm_pos_iff.mpr hne
  obtain ⟨c, hc⟩ := ht 1
  have hbound : ∀ m : ℕ, ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ ‖θ ϖ‖ ^ m := by
    intro m
    obtain ⟨N, hN⟩ := hc m
    obtain ⟨s, hsS, hs⟩ := hN N le_rfl
    have h0 := (hker _).mpr hs
    simp only [map_sub, map_mul, map_pow, hy, mul_zero, zero_sub] at h0
    have h1 : θ ϖ ^ c * θ t = -(θ ϖ ^ m * θ s) := by linear_combination -h0
    have h2 : ‖θ ϖ‖ ^ c * ‖θ t‖ = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
      have := congrArg norm h1
      simpa [norm_mul, norm_pow, norm_neg] using this
    rw [h2]
    exact mul_le_of_le_one_right (pow_nonneg hapos.le m) (hS s hsS)
  have hlim : Filter.Tendsto (fun m : ℕ => ‖θ ϖ‖ ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hapos.le hlt
  have hle : ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ 0 := ge_of_tendsto' hlim hbound
  have hz : ‖θ t‖ ≤ 0 := by
    by_contra hcon
    have : 0 < ‖θ ϖ‖ ^ c * ‖θ t‖ := mul_pos (pow_pos hapos c) (not_le.mp hcon)
    linarith
  exact norm_le_zero_iff.mp hz

end GlobalTheory.CompanionTheory.LTPer

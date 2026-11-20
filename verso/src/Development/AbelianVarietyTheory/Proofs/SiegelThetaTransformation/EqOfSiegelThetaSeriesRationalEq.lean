import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffEqZeroOfHasSumMFourierOrthonormalImage
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

/- English proof (translation)
Establish `h' : ∀ p : κ × ι, ∃ n : ℤ, (n : ℚ) = (R : ℚ) * x p.1 p.2`. Introduce `p`. Use `h p.1 p.2` as an intermediate fact. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.1 this`. Conclude with `⟨n, by simpa using hn⟩`.

Use `choose n hn using h'`. Use `⟨fun p => n p * S, ?_⟩` and prove the remaining obligations. Use extensionality with `k i`. Establish `hR' : (R : ℚ) ≠ 0` using `by exact_mod_cast hR.ne'`. Establish `hS' : (S : ℚ) ≠ 0` using `by exact_mod_cast hS.ne'`.

Simplify using `only [Matrix.of_apply]`. Use `push_cast`. Rewrite using `[hn (k, i)]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_int_div_of_intM {κ ι : Type} (R S : ℕ) (hR : 0 < R) (hS : 0 < S)
    (x : Matrix κ ι ℚ) (h : IntM ((R : ℚ) • x)) :
    ∃ s : κ × ι → ℤ, (Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)) = x := by
  have h' : ∀ p : κ × ι, ∃ n : ℤ, (n : ℚ) = (R : ℚ) * x p.1 p.2 := by
    intro p
    have := h p.1 p.2
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    exact ⟨n, by simpa using hn⟩
  choose n hn using h'
  refine ⟨fun p => n p * S, ?_⟩
  ext k i
  have hR' : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hS' : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  simp only [Matrix.of_apply]
  push_cast
  rw [hn (k, i)]
  field_simp

/- English proof (translation)
Introduce `κ ι _ _ _ φ ψ hφ hψ τ hτ h`. Take `⟨R, hR, hRφ, -⟩` from `id hφ`. Take `⟨S, hS, hSψ, -⟩` from `id hψ`. Establish `hN : (((R * S : ℕ) : ℚ)) ≠ 0` using `by exact_mod_cast (Nat.mul_pos hR hS).ne'`. Establish `hNC : (((R * S : ℕ) : ℂ)) ≠ 0` using `by exact_mod_cast (Nat.mul_pos hR hS).ne'`.

Set `e : (κ × ι → ℤ) → Matrix κ ι ℚ` to `fun s => Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)`. Establish `he : Function.Injective e`. Introduce `s t hst`. Use function extensionality and compare the values at `p`. Use `congrFun (congrFun hst p.1) p.2` as an intermediate fact.

Simplify using `only [e, Matrix.of_apply] at this`. Use `(div_left_inj' hN).1 this` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hrange : ∀ x, φ x - ψ x ≠ 0 → x ∈ Set.range e`. Introduce `x hx`.

Distinguish the cases in `h1 : φ x = 0`. Establish `h2 : ψ x ≠ 0`. Introduce `h2; exact hx (by rw [h1, h2, sub_zero])`. Take `⟨s, hs⟩` from `exists_int_div_of_intM S R hS hR x (hSψ x h2)`. Conclude with `⟨s, by rw [← hs, Nat.mul_comm S R]⟩`.

Conclude with `exists_int_div_of_intM R S hR hS x (hRφ x h1)`. Set `E : (κ → ι → ℂ) → Matrix κ ι ℚ → ℂ` to `fun ζ x => cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))`. Establish `hsφ : ∀ ζ, Summable fun x => φ x * E ζ x` using `fun ζ => (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ ζ).of_norm`. Establish `hsψ : ∀ ζ, Summable fun x => ψ x * E ζ x` using `fun ζ => (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι ψ hψ τ hτ ζ).of_norm`. Establish `hs : ∀ ζ, Summable fun x => (φ x - ψ x) * E ζ x` using `fun ζ => by`.

Simplify `(hsφ ζ).sub (hsψ ζ)` using `only [sub_mul]`. Establish `hz : ∀ ζ, ∑' x, (φ x - ψ x) * E ζ x = 0` using `fun ζ => by`. Simplify using `only [sub_mul]`. Rewrite using `[(hsφ ζ).tsum_sub (hsψ ζ)]`. Conclude with `sub_eq_zero.2 (h ζ)`.

Establish `key` using `GlobalTheory.coeff_eq_zero_of_fourier_series_eq_zero (κ × ι) (fun s => (φ (e s) - ψ (e s)) * E 0 (e s)) (((hs 0).comp_injective he).norm) (by`. Introduce `y`. Establish `h0` using `hz (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ))`. Rewrite using `[← he.tsum_eq (f := fun x => (φ x - ψ x) * E (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) x) (by`. Introduce `x hx`.

Conclude with `hrange x (left_ne_zero_of_mul hx))] at h0`. Rewrite using `[← h0]`. Use `tsum_congr fun s => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `congr 1`.

Simplify using `only [E]`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Establish `: ∀ k, qv (e s k) ⬝ᵥ (fun i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) = ∑ i, (s (k, i) : ℂ) * (y (k, i) : ℂ)`. Introduce `k`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [qv, e, Matrix.of_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [this, Pi.zero_apply, dotProduct_zero, mul_zero, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_prod_type]`. Use the proof step `ring)`.

Use function extensionality and compare the values at `x`. Assume the negation of the conclusion as `hx`. Take `⟨s, rfl⟩` from `hrange x (sub_ne_zero.2 hx)`. Use `key s` as an intermediate fact. Break down `mul_eq_zero.1 this with h1 | h1` into its components or cases.

Conclude with `hx (sub_eq_zero.1 h1)`. Conclude with `Complex.exp_ne_zero _ h1`.
-/
theorem eq_of_thS_eq : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by
  intro κ ι _ _ _ φ ψ hφ hψ τ hτ h
  obtain ⟨R, hR, hRφ, -⟩ := id hφ
  obtain ⟨S, hS, hSψ, -⟩ := id hψ
  have hN : (((R * S : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hR hS).ne'
  have hNC : (((R * S : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hR hS).ne'
  let e : (κ × ι → ℤ) → Matrix κ ι ℚ := fun s =>
    Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)
  have he : Function.Injective e := by
    intro s t hst
    funext p
    have := congrFun (congrFun hst p.1) p.2
    simp only [e, Matrix.of_apply] at this
    have := (div_left_inj' hN).1 this
    exact_mod_cast this
  have hrange : ∀ x, φ x - ψ x ≠ 0 → x ∈ Set.range e := by
    intro x hx
    by_cases h1 : φ x = 0
    · have h2 : ψ x ≠ 0 := by
        intro h2; exact hx (by rw [h1, h2, sub_zero])
      obtain ⟨s, hs⟩ := exists_int_div_of_intM S R hS hR x (hSψ x h2)
      exact ⟨s, by rw [← hs, Nat.mul_comm S R]⟩
    · exact exists_int_div_of_intM R S hR hS x (hRφ x h1)
  let E : (κ → ι → ℂ) → Matrix κ ι ℚ → ℂ := fun ζ x =>
    cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))
  have hsφ : ∀ ζ, Summable fun x => φ x * E ζ x := fun ζ =>
    (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ ζ).of_norm
  have hsψ : ∀ ζ, Summable fun x => ψ x * E ζ x := fun ζ =>
    (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι ψ hψ τ hτ ζ).of_norm
  have hs : ∀ ζ, Summable fun x => (φ x - ψ x) * E ζ x := fun ζ => by
    simpa only [sub_mul] using (hsφ ζ).sub (hsψ ζ)
  have hz : ∀ ζ, ∑' x, (φ x - ψ x) * E ζ x = 0 := fun ζ => by
    simp only [sub_mul]
    rw [(hsφ ζ).tsum_sub (hsψ ζ)]
    exact sub_eq_zero.2 (h ζ)
  have key := GlobalTheory.coeff_eq_zero_of_fourier_series_eq_zero (κ × ι)
    (fun s => (φ (e s) - ψ (e s)) * E 0 (e s))
    (((hs 0).comp_injective he).norm) (by
      intro y
      have h0 := hz (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ))
      rw [← he.tsum_eq (f := fun x => (φ x - ψ x) * E (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) x)
        (by
          intro x hx
          exact hrange x (left_ne_zero_of_mul hx))] at h0
      rw [← h0]
      refine tsum_congr fun s => ?_
      rw [mul_assoc]
      congr 1
      simp only [E]
      rw [← Complex.exp_add]
      congr 1
      have : ∀ k, qv (e s k) ⬝ᵥ (fun i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) =
          ∑ i, (s (k, i) : ℂ) * (y (k, i) : ℂ) := by
        intro k
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [qv, e, Matrix.of_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
        field_simp
      simp only [this, Pi.zero_apply, dotProduct_zero, mul_zero, add_zero, Finset.sum_add_distrib,
        ← Finset.mul_sum, Fintype.sum_prod_type]
      ring)
  funext x
  by_contra hx
  obtain ⟨s, rfl⟩ := hrange x (sub_ne_zero.2 hx)
  have := key s
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hx (sub_eq_zero.1 h1)
  · exact Complex.exp_ne_zero _ h1

end GlobalTheory.SW

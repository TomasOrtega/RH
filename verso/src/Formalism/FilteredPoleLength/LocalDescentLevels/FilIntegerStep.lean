import Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient

namespace Formalism.LatticeBaseChangeAlt

/- English proof (translation)
Introduce `n x h`. Establish `h1 : x ≤ (⌈x⌉ : ℝ)` using `Int.le_ceil x`. Establish `h2 : (-(⌈x⌉ : ℝ) - 1) < (n : ℝ)` using `by linarith`. Establish `h3 : (-⌈x⌉ - 1 : ℤ) < n` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem ordCeil : OrdCeil := by
  intro n x h
  have h1 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  have h2 : (-(⌈x⌉ : ℝ) - 1) < (n : ℝ) := by linarith
  have h3 : (-⌈x⌉ - 1 : ℤ) < n := by exact_mod_cast h2
  omega

/- English proof (translation)
Introduce `ep T ν νs c' vet e hep hc hv hν ⟨n, hn⟩ he`. Establish `hepR : (1 : ℝ) ≤ ep` using `by exact_mod_cast hep`. Establish `hT0 : (0 : ℝ) ≤ T` using `by positivity`. Establish `hy : 0 ≤ (ep : ℝ) * (T * c' * vet)` using `by positivity`. Rewrite using `[div_le_iff₀ (by linarith)]`.

Establish `hint : (ep : ℝ) * ((T : ℝ) * ν - e) = (((T : ℤ) * n - ep * e : ℤ) : ℝ)` using `by push_cast; rw [← hn]; ring`. Rewrite using `[hint, Int.ceil_intCast, Int.cast_max]`. Apply `max_le` to reduce the goal to its premises. Simplify `hy` using `[mul_comm]`. Rewrite using `[← hint]`.

Establish `: (T : ℝ) * ν - e ≤ T * c' * vet` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem poleOrderGood : PoleOrderGood := by
  intro ep T ν νs c' vet e hep hc hv hν ⟨n, hn⟩ he
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hint : (ep : ℝ) * ((T : ℝ) * ν - e) = (((T : ℤ) * n - ep * e : ℤ) : ℝ) := by
    push_cast; rw [← hn]; ring
  rw [hint, Int.ceil_intCast, Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · rw [← hint]
    have : (T : ℝ) * ν - e ≤ T * c' * vet := by nlinarith
    nlinarith

/- English proof (translation)
Introduce `ep T ν νs c' vet hep hT hc hv hν e`. Establish `hepR : (1 : ℝ) ≤ ep` using `by exact_mod_cast hep`. Establish `hTR : (1 : ℝ) ≤ T` using `by exact_mod_cast hT`. Establish `he : (T : ℝ) * (νs + 1) ≤ (e : ℝ)` using `Int.le_ceil _`. Establish `hy : 0 ≤ (ep : ℝ) * (T * c' * vet)` using `by positivity`.

Rewrite using `[div_le_iff₀ (by linarith)]`. Establish `hx : (ep : ℝ) * ((T : ℝ) * ν - e) ≤ (ep : ℝ) * (T * c' * vet) - ep`. Establish `: (T : ℝ) * ν - e ≤ T * c' * vet - 1` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hc1 : ((⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) < (ep : ℝ) * ((T : ℝ) * ν - e) + 1` using `Int.ceil_lt_add_one _`.

Rewrite using `[Int.cast_max]`. Apply `max_le` to reduce the goal to its premises. Simplify `hy` using `[mul_comm]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem poleOrderBad : PoleOrderBad := by
  intro ep T ν νs c' vet hep hT hc hv hν e
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have he : (T : ℝ) * (νs + 1) ≤ (e : ℝ) := Int.le_ceil _
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hx : (ep : ℝ) * ((T : ℝ) * ν - e) ≤ (ep : ℝ) * (T * c' * vet) - ep := by
    have : (T : ℝ) * ν - e ≤ T * c' * vet - 1 := by nlinarith
    nlinarith
  have hc1 : ((⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) < (ep : ℝ) * ((T : ℝ) * ν - e) + 1 :=
    Int.ceil_lt_add_one _
  rw [Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · nlinarith

/- English proof (translation)
Introduce `D T δ xL xF hδ h1 h2`. Establish `hD : (0 : ℝ) ≤ D` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem shareExponent : ShareExponent := by
  intro D T δ xL xF hδ h1 h2
  have hD : (0 : ℝ) ≤ D := by positivity
  nlinarith

/- English proof (translation)
Introduce `HL Hde X Y a ha ha2 hY h1 h2`. Establish `hm : X ≤ max X 0` using `le_max_left _ _`. Establish `hm0 : 0 ≤ max X 0` using `le_max_right _ _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem heightAbsorb : HeightAbsorb := by
  intro HL Hde X Y a ha ha2 hY h1 h2
  have hm : X ≤ max X 0 := le_max_left _ _
  have hm0 : 0 ≤ max X 0 := le_max_right _ _
  nlinarith

/- English proof (translation)
Introduce `νF νE T c φ μ h1 h2 h3`. Establish `hT : (0 : ℝ) ≤ T` using `by positivity`. Establish `: ((T : ℤ) * νE : ℤ) < νF`. Establish `: ((T : ℝ) * νE) < νF` using `by nlinarith`. Conclude with `this` after adjusting the coercions.

Use linear arithmetic over natural numbers and integers.
-/
theorem filIntegerStep : FilIntegerStep := by
  intro νF νE T c φ μ h1 h2 h3
  have hT : (0 : ℝ) ≤ T := by positivity
  have : ((T : ℤ) * νE : ℤ) < νF := by
    have : ((T : ℝ) * νE) < νF := by nlinarith
    exact_mod_cast this
  omega

/- English proof (translation)
Introduce `ξn lam d' ρ φ t p RR T c hξ hl hd hρ hφ hφ2 ht hRR hTc hc1`. Establish `h1 : ξn ^ 2 * lam ^ 2 ≤ d' ^ 2`. Establish `: 0 ≤ ξn * lam` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hξ2 : 0 < ξn ^ 2` using `by positivity`.

Establish `h2 : 2 * (RR * (T * c)) * (d' ^ 2 * ρ) < ξn ^ 2 * p` using `by nlinarith`. Establish `h3 : T * c ≤ RR * (T * c)` using `by nlinarith`. Establish `h4 : (T * c) * (ξn ^ 2 * lam ^ 2 * ρ) ≤ (RR * (T * c)) * (d' ^ 2 * ρ)`. Apply `mul_le_mul h3 (mul_le_mul_of_nonneg_right h1 hρ) (by positivity) (by nlinarith)` to reduce the goal to its premises. Establish `h5 : (T * c) * (ξn ^ 2 * φ) ≤ (T * c) * (ξn ^ 2 * (2 * ρ * lam ^ 2))` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφ2 hξ2.le) hTc`.

Establish `h6 : ξn ^ 2 * (T * c * φ) < ξn ^ 2 * p` using `by nlinarith`. Conclude with `lt_of_mul_lt_mul_left h6 hξ2.le`.
-/
theorem sFChain : SFChain := by
  intro ξn lam d' ρ φ t p RR T c hξ hl hd hρ hφ hφ2 ht hRR hTc hc1
  have h1 : ξn ^ 2 * lam ^ 2 ≤ d' ^ 2 := by
    have : 0 ≤ ξn * lam := by positivity
    nlinarith
  have hξ2 : 0 < ξn ^ 2 := by positivity

  have h2 : 2 * (RR * (T * c)) * (d' ^ 2 * ρ) < ξn ^ 2 * p := by nlinarith
  have h3 : T * c ≤ RR * (T * c) := by nlinarith
  have h4 : (T * c) * (ξn ^ 2 * lam ^ 2 * ρ) ≤ (RR * (T * c)) * (d' ^ 2 * ρ) := by
    apply mul_le_mul h3 (mul_le_mul_of_nonneg_right h1 hρ) (by positivity) (by nlinarith)
  have h5 : (T * c) * (ξn ^ 2 * φ) ≤ (T * c) * (ξn ^ 2 * (2 * ρ * lam ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφ2 hξ2.le) hTc
  have h6 : ξn ^ 2 * (T * c * φ) < ξn ^ 2 * p := by nlinarith
  exact lt_of_mul_lt_mul_left h6 hξ2.le

end Formalism.LatticeBaseChangeAlt

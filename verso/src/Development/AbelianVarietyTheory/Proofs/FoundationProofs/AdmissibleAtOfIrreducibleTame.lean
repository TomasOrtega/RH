import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.WdCocycle

section General

variable {D : D7} {T : Tor D} {N N' : ℕ}

/- English proof (translation)
Simplify using `only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]`.
-/
theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

/- English proof (translation)
Simplify using `only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]`.
-/
theorem hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

/- English proof (translation)
Simplify using `only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]`. Use `congr 1`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem hf_conj (x z : VC D N N') : Hf D T z x = (starRingEnd ℂ) (Hf D T x z) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `h1 : Hf D T x y = ((Hf D T x y).re : ℂ) + ((Hf D T x y).im : ℂ) * Complex.I` using `(Complex.re_add_im _).symm`. Establish `h2 : Hf D T y x = ((Hf D T x y).re : ℂ) - ((Hf D T x y).im : ℂ) * Complex.I`. Rewrite using `[hf_conj x y]`. Apply the tactic sequence `apply Complex.ext <;> simp`.

Establish `h3 : (Hf D T y x).re = (Hf D T x y).re`. Rewrite using `[hf_conj x y, Complex.conj_re]`. Establish `h4 : (w0 D * Hf D T x y).im = ((Hf D T x y).im + Real.sqrt D.host.d * (Hf D T x y).re) / 2`. Establish `: w0 D = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I`. Rewrite using `[w0]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Simplify using `only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key : ee (qH D T x / 2) * ee (qH D T y / 2) * Complex.exp (-(Real.pi : ℂ) * Hf D T (z + x) y - (Real.pi : ℂ) * Hf D T y y / 2) * Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) = ee (-(w0 D * Hf D T x y).im) * ee (qH D T (x + y) / 2) * Complex.exp (-(Re …`. Simplify using `only [ee, ← Complex.exp_add, qH]`. Use `congr 1`. Rewrite using `[h4]`. Simplify using `only [hf_add_left, hf_add_right, Complex.add_re, h3]`.

Rewrite using `[h2]`. Generalize the expression as in `(Hf D T x y).re = a at h1 ⊢`. Generalize the expression as in `(Hf D T x y).im = b at h1 ⊢`. Rewrite using `[h1]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Wd, U, wdPh, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[add_assoc z x y]`. Take the linear combination `F (z + (x + y)) * key`.
-/
theorem wd_wd (x y : VC D N N') (F : VC D N N' → ℂ) :
    Wd D T x (Wd D T y F) = ee (-(w0 D * Hf D T x y).im) • Wd D T (x + y) F := by
  funext z
  have h1 : Hf D T x y = ((Hf D T x y).re : ℂ) + ((Hf D T x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : Hf D T y x = ((Hf D T x y).re : ℂ) - ((Hf D T x y).im : ℂ) * Complex.I := by
    rw [hf_conj x y]
    apply Complex.ext <;> simp
  have h3 : (Hf D T y x).re = (Hf D T x y).re := by
    rw [hf_conj x y, Complex.conj_re]
  have h4 : (w0 D * Hf D T x y).im = ((Hf D T x y).im + Real.sqrt D.host.d * (Hf D T x y).re) / 2 := by
    have : w0 D = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
      rw [w0]; push_cast; ring
    rw [this]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have key : ee (qH D T x / 2) * ee (qH D T y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T (z + x) y - (Real.pi : ℂ) * Hf D T y y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) =
      ee (-(w0 D * Hf D T x y).im) * ee (qH D T (x + y) / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z (x + y) - (Real.pi : ℂ) * Hf D T (x + y) (x + y) / 2) := by
    simp only [ee, ← Complex.exp_add, qH]
    congr 1
    rw [h4]
    simp only [hf_add_left, hf_add_right, Complex.add_re, h3]
    rw [h2]
    generalize (Hf D T x y).re = a at h1 ⊢
    generalize (Hf D T x y).im = b at h1 ⊢
    rw [h1]
    push_cast
    ring
  simp only [Wd, U, wdPh, Pi.smul_apply, smul_eq_mul]
  rw [add_assoc z x y]
  linear_combination F (z + (x + y)) * key

end General

variable {D : D7}

/- English proof (translation)
The claim follows from `D.host.conjE_apply φ x`.
-/
theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

/- English proof (translation)
Establish `h : δ * starRingEnd ℂ δ = (‖δ‖ : ℂ) ^ 2` using `Complex.mul_conj' δ`. Simplify using `only [Hf, pt, embV, tor0, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, emb_conj]`. Use `push_cast`. Rewrite using `[← h, div_mul_eq_mul_div]`. Use `congr 1`.

Simplify using `only [Finset.mul_sum]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem hf_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y) =
      ((‖δ‖ ^ 2 / area (lamOf D cc δ) : ℝ) : ℂ) * ∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (y i j)) := by
  have h : δ * starRingEnd ℂ δ = (‖δ‖ : ℂ) ^ 2 := Complex.mul_conj' δ
  simp only [Hf, pt, embV, tor0, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, emb_conj]
  push_cast
  rw [← h, div_mul_eq_mul_div]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `only [pt, embV, tor0, Pi.smul_apply, Pi.add_apply, Matrix.add_apply, smul_eq_mul, map_add, mul_add]`.
-/
theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Pi.add_apply, Matrix.add_apply, smul_eq_mul, map_add, mul_add]

/- English proof (translation)
Introduce `D hg cc δ _`. Take `⟨a, ha⟩` from `exists_integer_map_eq_w0 D`. Set `w : 𝓞 D.host.E` to `algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a`. Establish `hw : (w : D.host.E) = ((a : D.host.K) : D.host.E)` using `rfl`. Establish `hτ : ∀ τ, embT D τ (w : D.host.E) = w0 D` using `fun τ => by`.

Rewrite using `[hw, ← ha]`. Conclude with `hg.1 τ _`. Use `⟨w, ?_, fun N N' z y => ⟨?_, pt_add cc δ z y, fun F => ?_⟩⟩` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Apply `D.host.φ₀.injective` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `D.host.φ₀ ((w : D.host.E) + D.host.conj (w : D.host.E)) = D.host.φ₀ 1`. Rewrite using `[map_add, emb_conj, hw, ha, map_one, w0]`. Simplify using `only [map_div₀, map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hf_pt, psi0, Complex.im_ofReal_mul]`.

Rewrite using `[wd_wd, pt_add, hf_pt, psi0]`. Use `congr 3`. Rewrite using `[mul_left_comm, Complex.im_ofReal_mul, Finset.mul_sum]`. Use `congr 2`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[← hτ τ, ← map_mul]`. Simplify using `only [Finset.mul_sum, mul_assoc]`.
-/
theorem wd_cocycle : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ (N N' : ℕ) (z y : Matrix (Fin N') (Fin N) D.host.E), ee (-(Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) ∧ pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y ∧ ∀ F, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ y) F) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * z i j * D.host.conj (y i j)) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z + y)) F := by
  intro D hg cc δ _
  obtain ⟨a, ha⟩ := exists_integer_map_eq_w0 D
  let w : 𝓞 D.host.E := algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a
  have hw : (w : D.host.E) = ((a : D.host.K) : D.host.E) := rfl
  have hτ : ∀ τ, embT D τ (w : D.host.E) = w0 D := fun τ => by
    rw [hw, ← ha]
    exact hg.1 τ _
  refine ⟨w, ?_, fun N N' z y => ⟨?_, pt_add cc δ z y, fun F => ?_⟩⟩
  · apply RingOfIntegers.ext
    apply D.host.φ₀.injective
    change D.host.φ₀ ((w : D.host.E) + D.host.conj (w : D.host.E)) = D.host.φ₀ 1
    rw [map_add, emb_conj, hw, ha, map_one, w0]
    simp only [map_div₀, map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  · rw [hf_pt, psi0, Complex.im_ofReal_mul]
  · rw [wd_wd, pt_add, hf_pt, psi0]
    congr 3
    rw [mul_left_comm, Complex.im_ofReal_mul, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← hτ τ, ← map_mul]
    simp only [Finset.mul_sum, mul_assoc]

end GlobalTheory.FinWeil.WdCocycle

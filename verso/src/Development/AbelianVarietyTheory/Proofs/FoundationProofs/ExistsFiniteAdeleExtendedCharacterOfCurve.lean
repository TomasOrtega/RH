import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.AdelicChar

/- English proof (translation)
Rewrite using `[ee, ee, ee, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[ee, mul_comm]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I k` after adjusting the coercions.
-/
theorem ee_int (k : ℤ) : ee k = 1 := by
  rw [ee, mul_comm]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I k

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

/- English proof (translation)
Rewrite using `[psi0, psi0, psi0, ← ee_add]`. Use `congr 1`. Simplify using `only [map_add, Finset.sum_add_distrib, Complex.add_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmTraceAdditiveCharacter_add (a b : D.host.E) : psi0 D cc δ (a + b) = psi0 D cc δ a * psi0 D cc δ b := by
  rw [psi0, psi0, psi0, ← ee_add]
  congr 1
  simp only [map_add, Finset.sum_add_distrib, Complex.add_im]
  ring

/- English proof (translation)
Simplify using `[psi0, ee]`.
-/
theorem cmTraceAdditiveCharacter_zero : psi0 D cc δ 0 = 1 := by simp [psi0, ee]

/- English proof (translation)
Use `haveI : IsCMField D.host.E := D.host.isCMField_hostE`. Establish `h : D.host.conj a = IsCMField.complexConj D.host.E a`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj]`. Conclude with `D.host.toHostAx.conjE_apply _ a`.

Rewrite using `[h, IsCMField.complexEmbedding_complexConj]`.
-/
theorem embT_conj (τ : D.what₂.Tau) (a : D.host.E) :
    embT D τ (D.host.conj a) = (starRingEnd ℂ) (embT D τ a) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have h : D.host.conj a = IsCMField.complexConj D.host.E a := by
    apply D.host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj]
    exact D.host.toHostAx.conjE_apply _ a
  rw [h, IsCMField.complexEmbedding_complexConj]

/- English proof (translation)
Establish `: (∑ τ, embT D τ (a + D.host.conj a)).im = 0`. Simplify using `[Complex.im_sum, embT_conj]`. Rewrite using `[psi0, this]`. Simplify using `[ee]`.
-/
theorem cmTraceAdditiveCharacter_add_conj (a : D.host.E) : psi0 D cc δ (a + D.host.conj a) = 1 := by
  have : (∑ τ, embT D τ (a + D.host.conj a)).im = 0 := by
    simp [Complex.im_sum, embT_conj]
  rw [psi0, this]
  simp [ee]

/- English proof (translation)
Take `⟨a, τ, ha, -, h⟩` from `GlobalTheory.CurveLattice.exists_tau D cc hcc`. Establish `hda : δ * a ≠ 0` using `mul_ne_zero hδ ha`. Rewrite using `[GlobalTheory.CurveLattice.area_of_tau hda (h δ)]`. Take `⟨m, n, rfl⟩` from `(h δ x).1 hx`. Take `⟨m', n', rfl⟩` from `(h δ y).1 hy`.

Use `⟨m * n' - n * m', ?_⟩` and prove the remaining obligations. Establish `hp : 0 < ‖δ * a‖ ^ 2 * τ.im`. Use `norm_pos_iff.2 hda` as an intermediate fact. Use `τ.im_pos` as an intermediate fact. Check the signs of the components of the expression.

Rewrite using `[div_eq_iff hp.ne']`. Generalize the expression as in `δ * a = b`. Simplify using `[Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem im_div_area (hcc : cc ≠ ⊥) (hδ : δ ≠ 0) {x y : ℂ} (hx : x ∈ lamOf D cc δ) (hy : y ∈ lamOf D cc δ) :
    ∃ k : ℤ, (x * (starRingEnd ℂ) y).im / area (lamOf D cc δ) = k := by
  obtain ⟨a, τ, ha, -, h⟩ := GlobalTheory.CurveLattice.exists_tau D cc hcc
  have hda : δ * a ≠ 0 := mul_ne_zero hδ ha
  rw [GlobalTheory.CurveLattice.area_of_tau hda (h δ)]
  obtain ⟨m, n, rfl⟩ := (h δ x).1 hx
  obtain ⟨m', n', rfl⟩ := (h δ y).1 hy
  refine ⟨m * n' - n * m', ?_⟩
  have hp : 0 < ‖δ * a‖ ^ 2 * τ.im := by
    have := norm_pos_iff.2 hda
    have := τ.im_pos
    positivity
  rw [div_eq_iff hp.ne']
  generalize δ * a = b
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

/- English proof (translation)
Establish `hδ : δ ≠ 0` using `(GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc).2.1`. Establish `hcc` using `hc.1.1`. Use `set n := Ideal.absNorm cc with hn`. Establish `hn0 : n ≠ 0` using `by simpa [hn, Ideal.absNorm_eq_zero_iff] using hcc`. Use `⟨n * n, by positivity, fun r hr => ?_⟩` and prove the remaining obligations.

Set `t : 𝓞 D.host.K` to `⟨Algebra.trace D.host.K D.host.E r, Algebra.isIntegral_trace hr⟩`. Establish `hnc : (n : 𝓞 D.host.K) ∈ cc` using `Ideal.absNorm_mem cc`. Take `⟨k, hk⟩` from `im_div_area D cc δ hcc hδ ((GlobalTheory.CurveLattice.mem_lamOf D cc δ _).2 ⟨_, cc.mul_mem_right t hnc, rfl⟩) ((GlobalTheory.CurveLattice.mem_lamOf D cc δ _).2 ⟨_, hnc, rfl⟩)`. Rewrite using `[psi0, ← ee_int (-k)]`. Use `congr 1`.

Establish `h1 : ∑ τ, embT D τ (((n * n : ℕ) : D.host.E) * r) = (n : ℂ) * n * D.host.φ₀ ((t : D.host.K) : D.host.E)`. Use `hg.2 r` as an intermediate fact. Simplify using `only [map_mul, map_natCast, ← Finset.mul_sum, this, Nat.cast_mul]`. Both sides reduce to the same expression. Establish `h2 : D.host.φ₀ (((n * t : 𝓞 D.host.K) : D.host.K) : D.host.E) = (n : ℂ) * D.host.φ₀ ((t : D.host.K) : D.host.E)` using `by simp`.

Establish `h3 : D.host.φ₀ ((((n : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E) = (n : ℂ)` using `by simp`. Rewrite `hk` using `[h2, h3]`. Rewrite using `[h1, Int.cast_neg, ← hk]`. Generalize the expression as in `D.host.φ₀ ((t : D.host.K) : D.host.E) = z`. Simplify using `[Complex.sq_norm, Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmTraceAdditiveCharacter_trivial_multiple_integers (hg : admG1 D) (hc : Crv D cc δ) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : D.host.E, IsIntegral ℤ r → psi0 D cc δ ((m : D.host.E) * r) = 1 := by
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc).2.1
  have hcc := hc.1.1
  set n := Ideal.absNorm cc with hn
  have hn0 : n ≠ 0 := by simpa [hn, Ideal.absNorm_eq_zero_iff] using hcc
  refine ⟨n * n, by positivity, fun r hr => ?_⟩
  let t : 𝓞 D.host.K := ⟨Algebra.trace D.host.K D.host.E r, Algebra.isIntegral_trace hr⟩
  have hnc : (n : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  obtain ⟨k, hk⟩ := im_div_area D cc δ hcc hδ
    ((GlobalTheory.CurveLattice.mem_lamOf D cc δ _).2 ⟨_, cc.mul_mem_right t hnc, rfl⟩)
    ((GlobalTheory.CurveLattice.mem_lamOf D cc δ _).2 ⟨_, hnc, rfl⟩)
  rw [psi0, ← ee_int (-k)]
  congr 1
  have h1 : ∑ τ, embT D τ (((n * n : ℕ) : D.host.E) * r) =
      (n : ℂ) * n * D.host.φ₀ ((t : D.host.K) : D.host.E) := by
    have := hg.2 r
    simp only [map_mul, map_natCast, ← Finset.mul_sum, this, Nat.cast_mul]
    rfl
  have h2 : D.host.φ₀ (((n * t : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      (n : ℂ) * D.host.φ₀ ((t : D.host.K) : D.host.E) := by simp
  have h3 : D.host.φ₀ ((((n : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E) = (n : ℂ) := by simp
  rw [h2, h3] at hk
  rw [h1, Int.cast_neg, ← hk]
  generalize D.host.φ₀ ((t : D.host.K) : D.host.E) = z
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

/- English proof (translation)
Take `⟨n, hn, hy⟩` from `GlobalTheory.HeckeVal.exists_denom D y`. Take `⟨r, -, w, hw, e⟩` from `GlobalTheory.HeckeVal.exists_approx D (n * m) (Nat.mul_pos hn hm) _ hy`. Establish `h1 : inc D ((n : D.host.E)⁻¹) * (n : AE D) = 1`. Rewrite using `[← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one]`. Use `⟨(n : D.host.E)⁻¹ * r, w, hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Move the coercions through the operations in `at e`. Take the linear combination `inc D ((n : D.host.E)⁻¹) * e + ((m : AE D) * w - y) * h1`.
-/
theorem exists_rat (m : ℕ) (hm : 0 < m) (y : AE D) :
    ∃ e : D.host.E, ∃ s ∈ OhE D, y = inc D e + (m : AE D) * s := by
  obtain ⟨n, hn, hy⟩ := GlobalTheory.HeckeVal.exists_denom D y
  obtain ⟨r, -, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D (n * m) (Nat.mul_pos hn hm) _ hy
  have h1 : inc D ((n : D.host.E)⁻¹) * (n : AE D) = 1 := by
    rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one]
  refine ⟨(n : D.host.E)⁻¹ * r, w, hw, ?_⟩
  rw [map_mul]
  push_cast at e
  linear_combination inc D ((n : D.host.E)⁻¹) * e + ((m : AE D) * w - y) * h1

/- English proof (translation)
Introduce `D hg cc δ hc`. Take `⟨m, hm, hint⟩` from `cmTraceAdditiveCharacter_trivial_multiple_integers D cc δ hg hc`. Use `choose e s hs he using exists_rat D m hm`. Establish `key : ∀ (y : AE D) (a : D.host.E) (w : AE D), w ∈ OhE D → y = inc D a + (m : AE D) * w → psi0 D cc δ (e y) = psi0 D cc δ a`. Introduce `y a w hw h`.

Establish `hm' : (m : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `h1 : inc D ((m : D.host.E)⁻¹) * (m : AE D) = 1`. Rewrite using `[← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ hm', map_one]`. Establish `h2 : inc D ((m : D.host.E)⁻¹ * (e y - a)) = w - s y`. Rewrite using `[map_mul, map_sub]`.

Take the linear combination `inc D ((m : D.host.E)⁻¹) * (h - he y) + (w - s y) * h1`. Establish `h3` using `hint _ ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 (h2 ▸ sub_mem hw (hs y)))`. Rewrite `h3` using `[mul_inv_cancel_left₀ hm']`. Rewrite using `[show e y = a + (e y - a) by ring, cmTraceAdditiveCharacter_add, h3, mul_one]`. Use `⟨fun y => psi0 D cc δ (e y), fun x y => ?_, ?_, fun a => ?_, fun y => ?_, m, hm, fun w hw => ?_⟩` and prove the remaining obligations.

Rewrite using `[← cmTraceAdditiveCharacter_add]`. Use `key _ _ _ (add_mem (hs x) (hs y)) ?_` and prove the remaining obligations. Rewrite using `[map_add]`. Take the linear combination `he x + he y`. Conclude with `(key 0 0 0 (zero_mem _) (by simp)).trans (cmTraceAdditiveCharacter_zero D cc δ)`.

Conclude with `key _ a 0 (zero_mem _) (by simp)`. Establish `hw : sgA D (s y) ∈ OhE D` using `Formalism.UG.P.csDual_sig_mem _ (hs y)`. Use `(key _ (e y + D.host.conj (e y)) _ (add_mem (hs y) hw) ?_).trans (cmTraceAdditiveCharacter_add_conj D cc δ _)` and prove the remaining obligations. Establish `h` using `congrArg (sgA D) (he y)`. Rewrite `h` using `[map_add, map_mul, map_natCast, GlobalTheory.NormSum.PtsMem.sgA_inc]`.

Rewrite using `[map_add]`. Take the linear combination `he y + h`. Conclude with `(key _ 0 w hw (by simp)).trans (cmTraceAdditiveCharacter_zero D cc δ)`.
-/
theorem exists_psi : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ ψ : AE D → ℂ, IsPsi D cc δ ψ := by
  intro D hg cc δ hc
  obtain ⟨m, hm, hint⟩ := cmTraceAdditiveCharacter_trivial_multiple_integers D cc δ hg hc
  choose e s hs he using exists_rat D m hm
  have key : ∀ (y : AE D) (a : D.host.E) (w : AE D), w ∈ OhE D → y = inc D a + (m : AE D) * w →
      psi0 D cc δ (e y) = psi0 D cc δ a := by
    intro y a w hw h
    have hm' : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h1 : inc D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
      rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ hm', map_one]
    have h2 : inc D ((m : D.host.E)⁻¹ * (e y - a)) = w - s y := by
      rw [map_mul, map_sub]
      linear_combination inc D ((m : D.host.E)⁻¹) * (h - he y) + (w - s y) * h1
    have h3 := hint _ ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 (h2 ▸ sub_mem hw (hs y)))
    rw [mul_inv_cancel_left₀ hm'] at h3
    rw [show e y = a + (e y - a) by ring, cmTraceAdditiveCharacter_add, h3, mul_one]
  refine ⟨fun y => psi0 D cc δ (e y), fun x y => ?_, ?_, fun a => ?_, fun y => ?_, m, hm, fun w hw => ?_⟩
  · rw [← cmTraceAdditiveCharacter_add]
    refine key _ _ _ (add_mem (hs x) (hs y)) ?_
    rw [map_add]
    linear_combination he x + he y
  · exact (key 0 0 0 (zero_mem _) (by simp)).trans (cmTraceAdditiveCharacter_zero D cc δ)
  · exact key _ a 0 (zero_mem _) (by simp)
  · have hw : sgA D (s y) ∈ OhE D := Formalism.UG.P.csDual_sig_mem _ (hs y)
    refine (key _ (e y + D.host.conj (e y)) _ (add_mem (hs y) hw) ?_).trans (cmTraceAdditiveCharacter_add_conj D cc δ _)
    have h := congrArg (sgA D) (he y)
    rw [map_add, map_mul, map_natCast, GlobalTheory.NormSum.PtsMem.sgA_inc] at h
    rw [map_add]
    linear_combination he y + h
  · exact (key _ 0 w hw (by simp)).trans (cmTraceAdditiveCharacter_zero D cc δ)

end GlobalTheory.FinWeil.AdelicChar

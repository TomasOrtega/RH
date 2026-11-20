import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjRiemannPos

/- English proof (translation)
Use `set N : ℕ := Ideal.absNorm c with hNdef`. Establish `hN : N ≠ 0` using `by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]`. Establish `hNc : (N : OF E) ∈ c` using `Ideal.absNorm_mem c`. Take `⟨m, hm, hym⟩` from `PI.AdCpctDenWork.exists_nat_adele (F := E) ((y⁻¹ : (Af E)ˣ) : Af E)`. Establish `key` using `GlobalTheory.CMVal.PicFin.mul_mem_hatO hNc (y := (m : Af E) * ((y⁻¹ : (Af E)ˣ) : Af E)) (fun v => hym v)`.

Use `⟨(N : E) * m, ?_, ?_⟩` and prove the remaining obligations. Use `show algebraMap E (Af E) ((N : E) * m) * _ ∈ hatO c`. Rewrite `key` using `[map_natCast, map_natCast]`. Rewrite using `[map_mul, map_natCast, map_natCast, _root_.mul_assoc]`. Conclude with `key`.

Conclude with `mul_ne_zero (Nat.cast_ne_zero.mpr hN) (Nat.cast_ne_zero.mpr hm.ne')`.
-/
theorem exists_ne_zero_mem_lattice {E : Type} [Field E] [NumberField E] (c : Ideal (OF E)) (y : (Af E)ˣ)
    (hc : c ≠ ⊥) : ∃ u ∈ lattice c y, u ≠ 0 := by
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : N ≠ 0 := by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]
  have hNc : (N : OF E) ∈ c := Ideal.absNorm_mem c
  obtain ⟨m, hm, hym⟩ := PI.AdCpctDenWork.exists_nat_adele (F := E) ((y⁻¹ : (Af E)ˣ) : Af E)
  have key := GlobalTheory.CMVal.PicFin.mul_mem_hatO hNc (y := (m : Af E) * ((y⁻¹ : (Af E)ˣ) : Af E)) (fun v => hym v)
  refine ⟨(N : E) * m, ?_, ?_⟩
  · show algebraMap E (Af E) ((N : E) * m) * _ ∈ hatO c
    rw [map_natCast, map_natCast] at key
    rw [map_mul, map_natCast, map_natCast, _root_.mul_assoc]
    exact key
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr hN) (Nat.cast_ne_zero.mpr hm.ne')

/- English proof (translation)
Introduce `K _ _ d δ io _ hd hδ g hg E _ _ _ _ I _ φ hφ c y hc n e h Hm hn hdiag _ hH`. Take `⟨u, hu, hu0⟩` from `exists_ne_zero_mem_lattice c y hc`. Use `set N : ℕ := Ideal.absNorm c with hNdef`. Establish `hN : N ≠ 0` using `by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]`. Establish `hNc : (N : OF E) ∈ c` using `Ideal.absNorm_mem c`.

Use `set δ' : E := algebraMap K E δ with hδ'`. Establish `hδ'2 : δ' ^ 2 = -(d : E)` using `by rw [hδ', ← map_pow, hδ]; simp`. Establish `hint : IsIntegral ℤ δ'`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Establish `e1 : algebraMap ℤ E (-(d : ℤ)) = -(d : E)` using `by simp`.

Rewrite using `[hδ'2, ← e1]`. Conclude with `isIntegral_algebraMap`. Set `b : 𝓞 E` to `⟨δ', hint⟩`. Establish `hb : algebraMap (𝓞 E) E b = δ'` using `rfl`. Establish `hmem : (N : E) * δ' ∈ orderC c` using `mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) (N : OF E) * b, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hNc), by simp [hb]⟩`.

Establish `hu' : (N : E) * δ' * u ∈ lattice c y` using `by show algebraMap E (Af E) _ * _ ∈ hatO c`. Rewrite using `[map_mul, _root_.mul_assoc]`. Conclude with `mul_mem (algebraMap_mem_hatO hmem) hu`. Use `⟨u, hu, (N : E) * δ' * u, hu', ?_⟩` and prove the remaining obligations. Use `set w : ℂ := io δ with hw`.

Establish `hφδ : ∀ i, φ i δ' = w` using `fun i => by rw [hδ', ← RingHom.comp_apply, hφ i]`. Establish `hw2 : w ^ 2 = -(d : ℂ)` using `by rw [hw, ← map_pow, hδ]; simp`. Establish `hre` using `congrArg Complex.re hw2`. Establish `him` using `congrArg Complex.im hw2`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him`.

Establish `hdR : (0 : ℝ) < d` using `by exact_mod_cast hd`. Establish `hwre : w.re = 0`. Assume the negation of the conclusion as `hne`. Establish `h0 : w.im = 0`. Establish `: 2 * w.re * w.im = 0` using `by linarith`.

Break down `mul_eq_zero.1 this with h1 | h1` into its components or cases. Conclude with `absurd (by linarith : w.re = 0) hne`. Conclude with `h1`. Rewrite `hre` using `[h0]`. Use polynomial arithmetic with `[mul_self_nonneg w.re]`.

Establish `hwim : w.im ^ 2 = d` using `by rw [hwre] at hre; nlinarith`. Establish `hφu' : ∀ i, φ i ((N : E) * δ' * u) = (N : ℂ) * w * φ i u` using `fun i => by`. Rewrite using `[map_mul, map_mul, map_natCast, hφδ]`. Use `set P : ℝ := ∑ i, h i * Complex.normSq (φ i u) with hP`. Establish `hS : (∑ i, h i * (φ i u * starRingEnd ℂ (φ i ((N : E) * δ' * u))).im) = -((N : ℝ) * w.im) * P`.

Rewrite using `[hP, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hφu']`. Simplify using `only [map_mul, Complex.conj_natCast, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.natCast_re, Complex.natCast_im, hwre, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hPpos : 0 < P`. Establish `hz : (fun j => φ (e j) u) ≠ 0`. Introduce `h0`. Use `congrFun h0 ⟨0, hn⟩` as an intermediate fact. Conclude with `(map_ne_zero (φ (e ⟨0, hn⟩))).2 hu0 this`.

Use `hdiag _ hz` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]`. Rewrite using `[hP, ← e.sum_comp]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `set W : Fin n → ℂ := fun j => g (φ (e j) u) with hWdef`. Establish `hW' : (star fun j => g (φ (e j) ((N : E) * δ' * u))) = (starRingEnd ℂ ((N : ℂ) * w)) • star W`. Use function extensionality and compare the values at `j`.

Simplify using `only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, hWdef, hφu', map_mul, map_natCast, hw, hg δ, star_mul', Complex.star_def]`. Establish `hWne : W ≠ 0`. Introduce `h0`. Use `congrFun h0 ⟨0, hn⟩` as an intermediate fact. Conclude with `(map_ne_zero g).2 ((map_ne_zero (φ (e ⟨0, hn⟩))).2 hu0) this`.

Establish `hQ` using `hH W hWne`. Use `set Q : ℂ := W ⬝ᵥ Hm.mulVec (star W) with hQdef`. Establish `hQ' : (W ⬝ᵥ Hm.mulVec (star fun j => g (φ (e j) ((N : E) * δ' * u)))).im = -((N : ℝ) * w.im) * Q.re`. Rewrite using `[hW', Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, ← hQdef]`. Simplify using `only [map_mul, Complex.conj_natCast, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.natCast_re, Complex.natCast_im, hwre]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hwim0 : w.im ≠ 0`. Introduce `h0`. Rewrite `hwim` using `[h0]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hNR : (0 : ℝ) < N` using `by exact_mod_cast Nat.pos_of_ne_zero hN`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hS]`. Conclude with `mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hNR.ne' hwim0)) hPpos.ne'`. Rewrite using `[hS, hQ']`.

Establish `hk : 0 < ((N : ℝ) * w.im) ^ 2` using `by positivity`. Establish `: -((N : ℝ) * w.im) * P * (-((N : ℝ) * w.im) * Q.re) = ((N : ℝ) * w.im) ^ 2 * (P * Q.re)` using `by ring`. Rewrite using `[this]`. Conclude with `mul_pos hk (mul_pos hPpos hQ)`.
-/
theorem exists_pos_pair : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (h : I → ℝ) (Hm : Matrix (Fin n) (Fin n) ℂ), 0 < n →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Matrix.diagonal fun j ↦ (h (e j) : ℂ)).mulVec (star z)).re) → Hm.IsHermitian →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
      ∃ u ∈ lattice c y, ∃ u' ∈ lattice c y, (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) ≠ 0 ∧
        0 < (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) * ((fun j ↦ g (φ (e j) u)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) u'))).im := by
  intro K _ _ d δ io _ hd hδ g hg E _ _ _ _ I _ φ hφ c y hc n e h Hm hn hdiag _ hH
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_lattice c y hc
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : N ≠ 0 := by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]
  have hNc : (N : OF E) ∈ c := Ideal.absNorm_mem c
  set δ' : E := algebraMap K E δ with hδ'
  have hδ'2 : δ' ^ 2 = -(d : E) := by rw [hδ', ← map_pow, hδ]; simp
  have hint : IsIntegral ℤ δ' := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have e1 : algebraMap ℤ E (-(d : ℤ)) = -(d : E) := by simp
    rw [hδ'2, ← e1]
    exact isIntegral_algebraMap
  let b : 𝓞 E := ⟨δ', hint⟩
  have hb : algebraMap (𝓞 E) E b = δ' := rfl
  have hmem : (N : E) * δ' ∈ orderC c := mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) (N : OF E) * b,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hNc), by simp [hb]⟩
  have hu' : (N : E) * δ' * u ∈ lattice c y := by
    show algebraMap E (Af E) _ * _ ∈ hatO c
    rw [map_mul, _root_.mul_assoc]
    exact mul_mem (algebraMap_mem_hatO hmem) hu
  refine ⟨u, hu, (N : E) * δ' * u, hu', ?_⟩
  set w : ℂ := io δ with hw
  have hφδ : ∀ i, φ i δ' = w := fun i => by rw [hδ', ← RingHom.comp_apply, hφ i]
  have hw2 : w ^ 2 = -(d : ℂ) := by rw [hw, ← map_pow, hδ]; simp
  have hre := congrArg Complex.re hw2
  have him := congrArg Complex.im hw2
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hwre : w.re = 0 := by
    by_contra hne
    have h0 : w.im = 0 := by
      have : 2 * w.re * w.im = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd (by linarith : w.re = 0) hne
      · exact h1
    rw [h0] at hre
    nlinarith [mul_self_nonneg w.re]
  have hwim : w.im ^ 2 = d := by rw [hwre] at hre; nlinarith
  have hφu' : ∀ i, φ i ((N : E) * δ' * u) = (N : ℂ) * w * φ i u := fun i => by
    rw [map_mul, map_mul, map_natCast, hφδ]

  set P : ℝ := ∑ i, h i * Complex.normSq (φ i u) with hP
  have hS : (∑ i, h i * (φ i u * starRingEnd ℂ (φ i ((N : E) * δ' * u))).im) = -((N : ℝ) * w.im) * P := by
    rw [hP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφu']
    simp only [map_mul, Complex.conj_natCast, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.natCast_re, Complex.natCast_im, hwre, Complex.normSq_apply]
    ring
  have hPpos : 0 < P := by
    have hz : (fun j => φ (e j) u) ≠ 0 := by
      intro h0
      have := congrFun h0 ⟨0, hn⟩
      exact (map_ne_zero (φ (e ⟨0, hn⟩))).2 hu0 this
    have := hdiag _ hz
    convert this using 1
    simp only [Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]
    rw [hP, ← e.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_im, Complex.normSq_apply]
    ring

  set W : Fin n → ℂ := fun j => g (φ (e j) u) with hWdef
  have hW' : (star fun j => g (φ (e j) ((N : E) * δ' * u))) = (starRingEnd ℂ ((N : ℂ) * w)) • star W := by
    funext j
    simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, hWdef, hφu', map_mul, map_natCast, hw, hg δ, star_mul',
      Complex.star_def]
  have hWne : W ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn⟩
    exact (map_ne_zero g).2 ((map_ne_zero (φ (e ⟨0, hn⟩))).2 hu0) this
  have hQ := hH W hWne
  set Q : ℂ := W ⬝ᵥ Hm.mulVec (star W) with hQdef
  have hQ' : (W ⬝ᵥ Hm.mulVec (star fun j => g (φ (e j) ((N : E) * δ' * u)))).im = -((N : ℝ) * w.im) * Q.re := by
    rw [hW', Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, ← hQdef]
    simp only [map_mul, Complex.conj_natCast, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.natCast_re, Complex.natCast_im, hwre]
    ring
  have hwim0 : w.im ≠ 0 := by
    intro h0; rw [h0] at hwim; nlinarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  refine ⟨?_, ?_⟩
  · rw [hS]
    exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hNR.ne' hwim0)) hPpos.ne'
  · rw [hS, hQ']
    have hk : 0 < ((N : ℝ) * w.im) ^ 2 := by positivity
    have : -((N : ℝ) * w.im) * P * (-((N : ℝ) * w.im) * Q.re) = ((N : ℝ) * w.im) ^ 2 * (P * Q.re) := by ring
    rw [this]
    exact mul_pos hk (mul_pos hPpos hQ)

end GlobalTheory.ConjRiemannPos

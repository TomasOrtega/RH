import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PullSectionIntegral

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Simplify using `only [aeval_def, eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hpow : ∏ p : Σ k, ι k, t p.1 ^ d p = ∏ k, t k ^ e k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `show ∏ i, t k ^ d ⟨k, i⟩ = t k ^ e k`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf d hd k]`. Establish `hsplit : ∏ p, (t p.1 * y p) ^ d p = (∏ p : Σ k, ι k, t p.1 ^ d p) * ∏ p, y p ^ d p`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun p _ => mul_pow _ _ _`.

Rewrite using `[hsplit, hpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_scale_of_isMultiHomog (y : (Σ k, ι k) → Ω) (t : K → Ω) {f : MRing ι} {e : K → ℕ}
    (hf : IsMultiHomog f e) :
    aeval (fun p => t p.1 * y p) f = (∏ k, t k ^ e k) * aeval y f := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hpow : ∏ p : Σ k, ι k, t p.1 ^ d p = ∏ k, t k ^ e k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ d ⟨k, i⟩ = t k ^ e k
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  have hsplit : ∏ p, (t p.1 * y p) ^ d p = (∏ p : Σ k, ι k, t p.1 ^ d p) * ∏ p, y p ^ d p := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => mul_pow _ _ _
  rw [hsplit, hpow]
  ring

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, map_mul, hp]`.

Simplify using `[mConeMap, mul_comm]`.
-/
theorem eval_mConeMap (y : (Σ k, ι k) → Ω) (t : K → Ω) (f : MRing ι) :
    eval t (mConeMap y f) = aeval (fun p => t p.1 * y p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    simp [mConeMap, mul_comm]

/- English proof (translation)
Rewrite using `[← eval_mConeMap, show mConeMap y f = 0 from hf, map_zero]`.
-/
theorem aeval_scale_eq_zero {y : (Σ k, ι k) → Ω} (t : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p => t p.1 * y p) f = 0 := by
  rw [← eval_mConeMap, show mConeMap y f = 0 from hf, map_zero]

/- English proof (translation)
Use `set φ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω := aeval y'`. Set `Lq : Fin n → MvPolynomial (Σ k, ι k) ℚ` to `fun i => map (algebraMap ℤ ℚ) (L i)`. Establish `hLq : ∀ i, φ (Lq i) = aeval y' (L i)` using `fun i => aeval_map_algebraMap ℚ y' (L i)`. Set `J : Ideal (MvPolynomial (Σ k, ι k) ℚ)` to `RingHom.ker φ ⊔ Ideal.span (Set.range Lq)`. Distinguish the cases in `hJ : J = ⊤`.

Establish `h1 : (1 : MvPolynomial (Σ k, ι k) ℚ) ∈ J` using `hJ ▸ Submodule.mem_top`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp h1`. Take `⟨β, rfl⟩` from `(Ideal.mem_span_range_iff_exists_fun).mp hb`. Use `⟨β, ?_⟩` and prove the remaining obligations. Use `congrArg φ hab` as an intermediate fact.

Rewrite `this` using `[map_add, show φ a = 0 from ha, zero_add, map_sum, map_one]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_mul, hLq]`. It suffices to derive a contradiction. Take `⟨m, hm, hJm⟩` from `Ideal.exists_le_maximal J hJ`.

Set `` to `Ideal.Quotient.field m`. Establish `: Algebra.FiniteType ℚ (MvPolynomial (Σ k, ι k) ℚ ⧸ m)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) (Ideal.Quotient.mkₐ_surjective ℚ m)`. Use `finite_of_finite_type_of_isJacobsonRing ℚ (MvPolynomial (Σ k, ι k) ℚ ⧸ m)` as an intermediate fact. Set `ψ : (MvPolynomial (Σ k, ι k) ℚ ⧸ m) →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Set `z : (Σ k, ι k) → ℂ` to `fun p => ψ (Ideal.Quotient.mk m (X p))`.

Establish `hz : ∀ g : MvPolynomial (Σ k, ι k) ℚ, ψ (Ideal.Quotient.mk m g) = aeval z g`. Introduce `g`. Establish `: (ψ.comp (Ideal.Quotient.mkₐ ℚ m)) = aeval z`. Use extensionality with `p`. Simplify using `[z]`.

Conclude with `congrArg (fun F => F g) this`. Establish `hzZ : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = ψ (Ideal.Quotient.mk m (map (algebraMap ℤ ℚ) f))`. Introduce `f`. Rewrite using `[hz, aeval_map_algebraMap, eval_map, aeval_def, algebraMap_int_eq]`. Establish `hker : ∀ g ∈ RingHom.ker φ, Ideal.Quotient.mk m g = 0` using `fun g hg => Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.mem_sup_left hg))`.

Establish `hzP : z ∈ mcPts P`. Use `⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩` and prove the remaining obligations. Establish `hX : (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℚ) ∈ RingHom.ker φ`. Simplify using `[RingHom.mem_ker, φ, hc k]`. Use `hker _ hX` as an intermediate fact.

Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Simplify using `[z, this]`. Establish `hφf : φ (map (algebraMap ℤ ℚ) f) = 0`. Rewrite using `[show φ (map (algebraMap ℤ ℚ) f) = aeval y' f from aeval_map_algebraMap ℚ y' f]`. Conclude with `hP f hf`.

Rewrite using `[hzZ, hker _ (RingHom.mem_ker.mpr hφf), map_zero]`. Take `⟨j, hj⟩` from `hL z hzP`. Apply `hj` to reduce the goal to its premises. Rewrite using `[hzZ, Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))), map_zero]`.
-/
theorem exists_sum_eq_one [CharZero Ω] (P : Ideal (MRing ι)) (y' : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y' ⟨k, c k⟩ = 1) (hP : ∀ f ∈ P, aeval y' f = 0) {n : ℕ} (L : Fin n → MRing ι)
    (hL : ∀ z ∈ mcPts P, ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ b : Fin n → MvPolynomial (Σ k, ι k) ℚ, ∑ i, aeval y' (b i) * aeval y' (L i) = 1 := by
  classical
  set φ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω := aeval y'
  let Lq : Fin n → MvPolynomial (Σ k, ι k) ℚ := fun i => map (algebraMap ℤ ℚ) (L i)
  have hLq : ∀ i, φ (Lq i) = aeval y' (L i) := fun i => aeval_map_algebraMap ℚ y' (L i)
  let J : Ideal (MvPolynomial (Σ k, ι k) ℚ) := RingHom.ker φ ⊔ Ideal.span (Set.range Lq)
  by_cases hJ : J = ⊤
  · have h1 : (1 : MvPolynomial (Σ k, ι k) ℚ) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨β, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hb
    refine ⟨β, ?_⟩
    have := congrArg φ hab
    rw [map_add, show φ a = 0 from ha, zero_add, map_sum, map_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hLq]
  · exfalso
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
    let := Ideal.Quotient.field m
    have : Algebra.FiniteType ℚ (MvPolynomial (Σ k, ι k) ℚ ⧸ m) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m)
        (Ideal.Quotient.mkₐ_surjective ℚ m)
    have := finite_of_finite_type_of_isJacobsonRing ℚ (MvPolynomial (Σ k, ι k) ℚ ⧸ m)
    let ψ : (MvPolynomial (Σ k, ι k) ℚ ⧸ m) →ₐ[ℚ] ℂ := IsAlgClosed.lift
    let z : (Σ k, ι k) → ℂ := fun p => ψ (Ideal.Quotient.mk m (X p))
    have hz : ∀ g : MvPolynomial (Σ k, ι k) ℚ, ψ (Ideal.Quotient.mk m g) = aeval z g := by
      intro g
      have : (ψ.comp (Ideal.Quotient.mkₐ ℚ m)) = aeval z := by
        ext p; simp [z]
      exact congrArg (fun F => F g) this
    have hzZ : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) =
        ψ (Ideal.Quotient.mk m (map (algebraMap ℤ ℚ) f)) := by
      intro f
      rw [hz, aeval_map_algebraMap, eval_map, aeval_def, algebraMap_int_eq]
    have hker : ∀ g ∈ RingHom.ker φ, Ideal.Quotient.mk m g = 0 := fun g hg =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.mem_sup_left hg))
    have hzP : z ∈ mcPts P := by
      refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
      · have hX : (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℚ) ∈ RingHom.ker φ := by
          simp [RingHom.mem_ker, φ, hc k]
        have := hker _ hX
        rw [map_sub, map_one, sub_eq_zero] at this
        simp [z, this]
      · have hφf : φ (map (algebraMap ℤ ℚ) f) = 0 := by
          rw [show φ (map (algebraMap ℤ ℚ) f) = aeval y' f from aeval_map_algebraMap ℚ y' f]
          exact hP f hf
        rw [hzZ, hker _ (RingHom.mem_ker.mpr hφf), map_zero]
    obtain ⟨j, hj⟩ := hL z hzP
    apply hj
    rw [hzZ, Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.mem_sup_right
      (Ideal.subset_span ⟨j, rfl⟩))), map_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `b using MvPolynomial.induction_on with`. Consider the case `C a => simpa using hQ a`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `V.add_mem hp hq`. Consider the case `mul_X p i hp => rw [map_mul, aeval_X]`.

Conclude with `V.mul_mem hp (hy i)`.
-/
theorem aeval_mem_of_forall [CharZero Ω] (V : Subring Ω) (hQ : ∀ r : ℚ, algebraMap ℚ Ω r ∈ V)
    (y' : (Σ k, ι k) → Ω) (hy : ∀ p, y' p ∈ V) (b : MvPolynomial (Σ k, ι k) ℚ) : aeval y' b ∈ V := by
  induction b using MvPolynomial.induction_on with
  | C a => simpa using hQ a
  | add p q hp hq => rw [map_add]; exact V.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact V.mul_mem hp (hy i)

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D e L q hV _ he hL hzero τ s hs j hj`. Use `set A := Algebra.adjoin ℚ (Set.range fun i => aeval y (L i) / aeval y (L j))`. Use `set R := (integralClosure A Ω).toSubring`. Establish `: IsIntegrallyClosedIn R Ω` using `inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)`. Use `show s / aeval y (L j) ^ (q * τ) ∈ R`.

Assume the negation of the conclusion as `hnot`. Take `⟨V, hRV, htV⟩` from `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hnot`. Establish `hAV : ∀ x ∈ A, x ∈ V` using `fun x hx => hRV (isIntegral_algebraMap (R := A) (A := Ω) (x := ⟨x, hx⟩))`. Establish `hQ : ∀ r : ℚ, algebraMap ℚ Ω r ∈ V.toSubring` using `fun r => hAV _ (A.algebraMap_mem r)`. Establish `hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`.

Introduce `k`. Take `⟨i, hi⟩` from `hV.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Use `show mConeMap y (X ⟨k, i⟩) = 0`. Simplify using `[mConeMap, h0]`.

Establish `hmax : ∀ k, ∃ c : ι k, ∀ i, V.valuation (y ⟨k, i⟩) ≤ V.valuation (y ⟨k, c⟩)`. Introduce `k`. Take `⟨i0, -⟩` from `hrel k`. Take `⟨c, -, hc⟩` from `Finset.exists_max_image Finset.univ (fun i => V.valuation (y ⟨k, i⟩)) ⟨i0, Finset.mem_univ _⟩`. Conclude with `⟨c, fun i => hc i (Finset.mem_univ _)⟩`.

Use `choose c hc using hmax`. Establish `hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0`. Introduce `k h0`. Take `⟨i0, hi0⟩` from `hrel k`. Use `hc k i0` as an intermediate fact.

Rewrite `this` using `[h0, map_zero, le_zero_iff, map_eq_zero]`. Conclude with `hi0 this`. Establish `hratio : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ V`. Introduce `p`. Rewrite using `[← V.valuation_le_one_iff, map_div₀]`.

Conclude with `div_le_one_of_le₀ (hc p.1 p.2) zero_le`. Use `set M : Ω := ∏ k, y ⟨k, c k⟩ ^ e k`. Establish `hM0 : M ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)`. Establish `hchart : (chartRingZ y c : Set Ω) ⊆ V`. Introduce `x hx`.

Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx => obtain ⟨p, rfl⟩ := hx`. Conclude with `hratio p`. Consider the case `algebraMap r => simp`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`.

Consider the case `mul a b _ _ ha hb => exact mul_mem ha hb`. Establish `: IsIntegrallyClosedIn V.toSubring Ω` using `inferInstanceAs (IsIntegrallyClosedIn V Ω)`. Establish `hxV : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) ∈ V.toSubring` using `(Subring.integralClosure_le_iff (R := chartRingZ y c) (T := V.toSubring)).mpr (fun r => hchart r.2) (hs c hc0)`. Establish `hprod : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) = (M ^ (q * τ))⁻¹`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_inv_distrib]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[show -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) = -((e k * (q * τ) : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, pow_mul]`. Rewrite `hxV` using `[hprod]`. Use `set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹`. Establish `hP' : ∀ f ∈ mCoordIdeal y, aeval (fun p => t p.1 * y p) f = 0` using `fun f hf => aeval_scale_eq_zero t hf`.

Take `⟨b, hb⟩` from `exists_sum_eq_one (mCoordIdeal y) (fun p => t p.1 * y p) c (fun k => inv_mul_cancel₀ (hc0 k)) hP' L hzero`. Establish `hLt : ∀ i, aeval (fun p => t p.1 * y p) (L i) = M⁻¹ * aeval y (L i)`. Introduce `i`. Rewrite using `[aeval_scale_of_isMultiHomog y t (hL i)]`. Simplify using `[t, M, Finset.prod_inv_distrib, inv_pow]`.

Establish `hratio' : ∀ p : Σ k, ι k, t p.1 * y p ∈ V` using `fun p => by`. Simplify `hratio p` using `[t, div_eq_inv_mul]`. Establish `hMV : M / aeval y (L j) ∈ V`. Establish `hsum : M / aeval y (L j) = ∑ i, aeval (fun p => t p.1 * y p) (b i) * (aeval y (L i) / aeval y (L j))`. Use `congrArg (fun w => w * (M / aeval y (L j))) hb` as an intermediate fact.

Simplify using `only [one_mul, Finset.sum_mul, hLt] at this`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Rewrite using `[hsum]`.

Use `sum_mem fun i _ => mul_mem ?_ ?_` and prove the remaining obligations. Conclude with `aeval_mem_of_forall V.toSubring hQ _ (fun p => hratio' p) (b i)`. Conclude with `hAV _ (Algebra.subset_adjoin ⟨i, rfl⟩)`. Apply `htV` to reduce the goal to its premises. Establish `hMn : M ^ (q * τ) ≠ 0` using `pow_ne_zero _ hM0`.

Establish `: s / aeval y (L j) ^ (q * τ) = s * (M ^ (q * τ))⁻¹ * (M / aeval y (L j)) ^ (q * τ)`. Rewrite using `[div_pow, mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ hMn, mul_one_div]`. Rewrite using `[this]`. Conclude with `mul_mem hxV (pow_mem hMV _)`.
-/
theorem proof : PullSectionIntegral.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hV _ he hL hzero τ s hs j hj
  classical
  set A := Algebra.adjoin ℚ (Set.range fun i => aeval y (L i) / aeval y (L j))
  set R := (integralClosure A Ω).toSubring
  have : IsIntegrallyClosedIn R Ω := inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
  show s / aeval y (L j) ^ (q * τ) ∈ R
  by_contra hnot
  obtain ⟨V, hRV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hnot
  have hAV : ∀ x ∈ A, x ∈ V := fun x hx =>
    hRV (isIntegral_algebraMap (R := A) (A := Ω) (x := ⟨x, hx⟩))
  have hQ : ∀ r : ℚ, algebraMap ℚ Ω r ∈ V.toSubring := fun r => hAV _ (A.algebraMap_mem r)

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  have hmax : ∀ k, ∃ c : ι k, ∀ i, V.valuation (y ⟨k, i⟩) ≤ V.valuation (y ⟨k, c⟩) := by
    intro k
    obtain ⟨i0, -⟩ := hrel k
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (y ⟨k, i⟩))
      ⟨i0, Finset.mem_univ _⟩
    exact ⟨c, fun i => hc i (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    obtain ⟨i0, hi0⟩ := hrel k
    have := hc k i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  have hratio : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ V := by
    intro p
    rw [← V.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hc p.1 p.2) zero_le

  set M : Ω := ∏ k, y ⟨k, c k⟩ ^ e k
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  have hchart : (chartRingZ y c : Set Ω) ⊆ V := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hratio p
    | algebraMap r => simp
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  have : IsIntegrallyClosedIn V.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn V Ω)
  have hxV : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) ∈ V.toSubring :=
    (Subring.integralClosure_le_iff (R := chartRingZ y c) (T := V.toSubring)).mpr
      (fun r => hchart r.2) (hs c hc0)
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) = (M ^ (q * τ))⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) = -((e k * (q * τ) : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, pow_mul]
  rw [hprod] at hxV

  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have hP' : ∀ f ∈ mCoordIdeal y, aeval (fun p => t p.1 * y p) f = 0 := fun f hf =>
    aeval_scale_eq_zero t hf
  obtain ⟨b, hb⟩ := exists_sum_eq_one (mCoordIdeal y) (fun p => t p.1 * y p) c
    (fun k => inv_mul_cancel₀ (hc0 k)) hP' L hzero
  have hLt : ∀ i, aeval (fun p => t p.1 * y p) (L i) = M⁻¹ * aeval y (L i) := by
    intro i
    rw [aeval_scale_of_isMultiHomog y t (hL i)]
    simp [t, M, Finset.prod_inv_distrib, inv_pow]
  have hratio' : ∀ p : Σ k, ι k, t p.1 * y p ∈ V := fun p => by
    simpa [t, div_eq_inv_mul] using hratio p
  have hMV : M / aeval y (L j) ∈ V := by
    have hsum : M / aeval y (L j) =
        ∑ i, aeval (fun p => t p.1 * y p) (b i) * (aeval y (L i) / aeval y (L j)) := by
      have := congrArg (fun w => w * (M / aeval y (L j))) hb
      simp only [one_mul, Finset.sum_mul, hLt] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [hsum]
    refine sum_mem fun i _ => mul_mem ?_ ?_
    · exact aeval_mem_of_forall V.toSubring hQ _ (fun p => hratio' p) (b i)
    · exact hAV _ (Algebra.subset_adjoin ⟨i, rfl⟩)
  apply htV
  have hMn : M ^ (q * τ) ≠ 0 := pow_ne_zero _ hM0
  have : s / aeval y (L j) ^ (q * τ) = s * (M ^ (q * τ))⁻¹ * (M / aeval y (L j)) ^ (q * τ) := by
    rw [div_pow, mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ hMn, mul_one_div]
  rw [this]
  exact mul_mem hxV (pow_mem hMV _)

end PullSectionIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1

section Rel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Set `φ : MvPolynomial K Ω →ₐ[ℤ] Ω` to `(aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ`. Establish `e : φ.comp (mConeMap y) = aeval y`. Use `MvPolynomial.algHom_ext fun p => ?_` and prove the remaining obligations. Simplify using `[φ, mConeMap]`. Establish `h0 : mConeMap y h = 0` using `hh`.

Rewrite using `[← e, AlgHom.comp_apply, h0, map_zero]`.
-/
theorem aeval_eq_zero_of_mem_mCoordIdeal (y : (Σ k, ι k) → Ω) {h : MRing ι}
    (hh : h ∈ mCoordIdeal y) : aeval y h = 0 := by
  let φ : MvPolynomial K Ω →ₐ[ℤ] Ω :=
    (aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ
  have e : φ.comp (mConeMap y) = aeval y := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp [φ, mConeMap]
  have h0 : mConeMap y h = 0 := hh
  rw [← e, AlgHom.comp_apply, h0, map_zero]

/- English proof (translation)
Take `⟨p, hpm, hp⟩` from `hθ`. Use `set n := p.natDegree`. Rewrite `hp` using `[hpm.as_sum]`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp`. Use `⟨n, fun j => C (p.coeff j), ?_⟩` and prove the remaining obligations.

Rewrite using `[one_mul]`. Use `LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (d := n • d) ?_ ?_` and prove the remaining obligations. Use `LocalRep.isMultiHomog_add (SectionOrderAtPoint.isMultiHomog_pow' hf n) (SectionOrderAtPoint.isMultiHomog_sum' _ _ fun j hj => ?_)` and prove the remaining obligations. Establish `h1` using `LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_C (ι := ι) (p.coeff j)) (SectionOrderAtPoint.isMultiHomog_pow' hf j)) (SectionOrderAtPoint.isMultiHomog_pow' hg (n - j))`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Establish `hj' : j ≤ n` using `(Finset.mem_range.mp hj).le`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_add]`. Rewrite using `[← add_mul, Nat.add_sub_cancel' hj']`. Establish `hsum : ∀ j ∈ Finset.range n, aeval y (C (p.coeff j) * f ^ j * g ^ (n - j)) = aeval y g ^ n * (algebraMap ℤ Ω (p.coeff j) * θ ^ j)`.

Introduce `j hj`. Establish `hj' : j ≤ n` using `(Finset.mem_range.mp hj).le`. Establish `e3 : aeval y g ^ n = aeval y g ^ j * aeval y g ^ (n - j)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hj']`. Simplify using `only [map_mul, map_pow, aeval_C, he]`.

Rewrite using `[e3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, map_sum, Finset.sum_congr rfl hsum, ← Finset.mul_sum, map_pow, he, mul_pow]`. Take the linear combination `(aeval y g ^ n) * hp`.
-/
theorem exists_monic_rel (y : (Σ k, ι k) → Ω) {f g : MRing ι} {d : K → ℕ} {θ : Ω}
    (hf : IsMultiHomog f d) (hg : IsMultiHomog g d) (hθ : IsIntegral ℤ θ)
    (he : aeval y f = θ * aeval y g) :
    ∃ (n : ℕ) (c : ℕ → MRing ι),
      1 * f ^ n + ∑ j ∈ Finset.range n, c j * f ^ j * g ^ (n - j) ∈ mCoordIdeal y := by
  classical
  obtain ⟨p, hpm, hp⟩ := hθ
  set n := p.natDegree
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp
  refine ⟨n, fun j => C (p.coeff j), ?_⟩
  rw [one_mul]
  refine LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (d := n • d) ?_ ?_
  · refine LocalRep.isMultiHomog_add (SectionOrderAtPoint.isMultiHomog_pow' hf n)
      (SectionOrderAtPoint.isMultiHomog_sum' _ _ fun j hj => ?_)
    have h1 := LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_mul
      (LocalRep.isMultiHomog_C (ι := ι) (p.coeff j)) (SectionOrderAtPoint.isMultiHomog_pow' hf j))
      (SectionOrderAtPoint.isMultiHomog_pow' hg (n - j))
    convert h1 using 1
    have hj' : j ≤ n := (Finset.mem_range.mp hj).le
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_add]
    rw [← add_mul, Nat.add_sub_cancel' hj']
  · have hsum : ∀ j ∈ Finset.range n,
        aeval y (C (p.coeff j) * f ^ j * g ^ (n - j)) =
          aeval y g ^ n * (algebraMap ℤ Ω (p.coeff j) * θ ^ j) := by
      intro j hj
      have hj' : j ≤ n := (Finset.mem_range.mp hj).le
      have e3 : aeval y g ^ n = aeval y g ^ j * aeval y g ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hj']
      simp only [map_mul, map_pow, aeval_C, he]
      rw [e3]
      ring
    rw [map_add, map_sum, Finset.sum_congr rfl hsum, ← Finset.mul_sum, map_pow, he, mul_pow]
    linear_combination (aeval y g ^ n) * hp

end Rel

/- English proof (translation)
Establish `hWp : W.IsPrime` using `hW.1.1`. Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.2`. Establish `hbW : b ∈ W` using `hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))`. Establish `h1 : (1 : R) ∉ W` using `(Ideal.ne_top_iff_one W).mp hWp.ne_top`. Establish `haW : a ∈ W` using `SectionOrderAtPoint.mem_of_rel hWp hbW h1 c (hPW hrel)`.

Use `⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr haW)⟩, fun Q hQ hQW => ?_⟩` and prove the remaining obligations. Conclude with `(eq_of_le_of_mem_minimalPrimes hP hW hQ.1 (le_sup_left.trans hQ.2) (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))) ha hQW).ge`.
-/
theorem mem_minimalPrimes_of_rel {R : Type*} [CommRing R] [IsNoetherianRing R] {P W : Ideal R}
    (hP : P.IsPrime) {a b : R} (ha : a ∉ P) {n : ℕ} (c : ℕ → R)
    (hrel : 1 * a ^ n + ∑ j ∈ Finset.range n, c j * a ^ j * b ^ (n - j) ∈ P)
    (hW : W ∈ (P ⊔ Ideal.span {b}).minimalPrimes) : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hbW : b ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
  have h1 : (1 : R) ∉ W := (Ideal.ne_top_iff_one W).mp hWp.ne_top
  have haW : a ∈ W := SectionOrderAtPoint.mem_of_rel hWp hbW h1 c (hPW hrel)
  refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr haW)⟩, fun Q hQ hQW => ?_⟩
  exact (eq_of_le_of_mem_minimalPrimes hP hW hQ.1 (le_sup_left.trans hQ.2)
    (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))) ha hQW).ge

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D d f g θ hV hf hg hgy hθ0 hθ hθi he`. Establish `hP : (mCoordIdeal y).IsPrime` using `hV.2.1.1`. Establish `hfy : aeval y f ≠ 0`. Rewrite using `[he]`. Conclude with `mul_ne_zero hθ0 hgy`.

Establish `hfP : f ∉ mCoordIdeal y` using `fun h => hfy (aeval_eq_zero_of_mem_mCoordIdeal y h)`. Establish `hgP : g ∉ mCoordIdeal y` using `fun h => hgy (aeval_eq_zero_of_mem_mCoordIdeal y h)`. Take `⟨n, c, hrel⟩` from `exists_monic_rel y hf hg hθ he`. Take `⟨m, c', hrel'⟩` from `exists_monic_rel y hg hf hθi (by rw [he, ← mul_assoc, inv_mul_cancel₀ hθ0, one_mul])`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `W`. Conclude with `⟨fun h => ⟨mem_minimalPrimes_of_rel hP hgP c' hrel' h.1, h.2⟩, fun h => ⟨mem_minimalPrimes_of_rel hP hfP c hrel h.1, h.2⟩⟩`. Introduce `W hW`. Establish `hWg` using `hW.1`. Establish `hWf` using `mem_minimalPrimes_of_rel hP hfP c hrel hWg`.

Establish `hWp : W.IsPrime` using `hWg.1.1`. Establish `hPW : mCoordIdeal y ≤ W` using `le_sup_left.trans hWg.1.2`. Establish `h1 : (1 : MRing ι) ∉ W` using `(Ideal.ne_top_iff_one W).mp hWp.ne_top`. Set `pW : PrimeSpectrum (MRing ι)` to `⟨W, hWp⟩`. Establish `hle1` using `SectionOrderAtPoint.locLen_le_of_rel hP hfP hgP pW hPW h1 c hrel (locLen_ne_top hWg)`.

Establish `hle2` using `SectionOrderAtPoint.locLen_le_of_rel hP hgP hfP pW hPW h1 c' hrel' (locLen_ne_top hWf)`. Use `congrArg ENat.toNat (le_antisymm hle2 hle1)` as an intermediate fact. Simplify `this` using `[multAt, hWp, locLen]`.
-/
theorem divCycle_eq_of_unit_ratio : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (d : K → ℕ) (f g : MRing ι) (θ : Ω), IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog f d → IsMultiHomog g d → aeval y g ≠ 0 → θ ≠ 0 → IsIntegral ℤ θ → IsIntegral ℤ θ⁻¹ → aeval y f = θ * aeval y g → divSupp (mCoordIdeal y) f = divSupp (mCoordIdeal y) g ∧ ∀ W ∈ divSupp (mCoordIdeal y) g, multAt ((mCoordIdeal y) ⊔ Ideal.span {f}) W = multAt ((mCoordIdeal y) ⊔ Ideal.span {g}) W := by
  intro K _ ι _ Ω _ y D d f g θ hV hf hg hgy hθ0 hθ hθi he
  have hP : (mCoordIdeal y).IsPrime := hV.2.1.1
  have hfy : aeval y f ≠ 0 := by
    rw [he]
    exact mul_ne_zero hθ0 hgy
  have hfP : f ∉ mCoordIdeal y := fun h => hfy (aeval_eq_zero_of_mem_mCoordIdeal y h)
  have hgP : g ∉ mCoordIdeal y := fun h => hgy (aeval_eq_zero_of_mem_mCoordIdeal y h)
  obtain ⟨n, c, hrel⟩ := exists_monic_rel y hf hg hθ he
  obtain ⟨m, c', hrel'⟩ := exists_monic_rel y hg hf hθi
    (by rw [he, ← mul_assoc, inv_mul_cancel₀ hθ0, one_mul])
  refine ⟨?_, ?_⟩
  · ext W
    exact ⟨fun h => ⟨mem_minimalPrimes_of_rel hP hgP c' hrel' h.1, h.2⟩,
      fun h => ⟨mem_minimalPrimes_of_rel hP hfP c hrel h.1, h.2⟩⟩
  · intro W hW
    have hWg := hW.1
    have hWf := mem_minimalPrimes_of_rel hP hfP c hrel hWg
    have hWp : W.IsPrime := hWg.1.1
    have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hWg.1.2
    have h1 : (1 : MRing ι) ∉ W := (Ideal.ne_top_iff_one W).mp hWp.ne_top
    let pW : PrimeSpectrum (MRing ι) := ⟨W, hWp⟩
    have hle1 := SectionOrderAtPoint.locLen_le_of_rel hP hfP hgP pW hPW h1 c hrel (locLen_ne_top hWg)
    have hle2 := SectionOrderAtPoint.locLen_le_of_rel hP hgP hfP pW hPW h1 c' hrel' (locLen_ne_top hWf)
    have := congrArg ENat.toNat (le_antisymm hle2 hle1)
    simpa [multAt, hWp, locLen] using this

end GlobalTheory.CompanionTheory.Ar.Giv

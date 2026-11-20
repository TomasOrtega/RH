import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpolyBaseChangeIntegrallyClosedStatement
open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

/- English proof (translation)
Use `letI := φ.toAlgebra`. Use `haveI : Module.Finite A B := hφ`. Use `set K := FractionRing A`. Take `⟨P, hP⟩` from `GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed (K := K) φ hφ b`. Establish `hinj : Function.Injective (algebraMap A K)` using `IsFractionRing.injective A K`.

Establish `hdeg : (charK φ hφ K b).natDegree = P.natDegree`. Rewrite using `[← hP]`. Conclude with `natDegree_map_eq_of_injective hinj P`. Establish `hmon : P.Monic`. Establish `h1` using `charK_monic φ hφ K b`.

Rewrite `h1` using `[← hP]`. Apply `hinj` to reduce the goal to its premises. Rewrite `h1` using `[Monic, leadingCoeff_map_of_injective hinj]`. Simplify using `using h1`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hcoeff : ∀ j < P.natDegree, P.coeff j ∈ p`. Introduce `j hj`. Establish `hk : 1 ≤ P.natDegree - j` using `by omega`. Establish `hrev : (charK φ hφ K b).reverse.coeff (P.natDegree - j) = algebraMap A K (P.coeff j)`.

Rewrite using `[coeff_reverse, hdeg, revAt_le (by omega), show P.natDegree - (P.natDegree - j) = j by omega, ← hP, coeff_map]`. Establish `hex : ∃ a : A, algebraMap A K a = (charK φ hφ K b).reverse.coeff (P.natDegree - j)` using `⟨P.coeff j, hrev.symm⟩`. Use `algebraMap_normCoeff φ hφ b _ hex` as an intermediate fact. Rewrite `this` using `[hrev]`. Use `hinj this` as an intermediate fact.

Rewrite using `[← this]`. Conclude with `hcon _ hk`. Use `set M := TensorProduct A K B`. Establish `hCH : Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b) = 0`. Establish `h` using `LinearMap.aeval_self_charpoly (Algebra.lmul K M ((1 : K) ⊗ₜ[A] b))`.

Establish `h2 : Algebra.lmul K M (Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b)) = 0`. Rewrite using `[← Polynomial.aeval_algHom_apply]`. Conclude with `h`. Establish `h3` using `LinearMap.congr_fun h2 1`. Simplify using `using h3`.

Establish `hker : Algebra.TensorProduct.includeRight (R` using `A) (A := K) (B := B) (Polynomial.aeval b P) = 0 := by`. Rewrite using `[← Polynomial.aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply, ← Polynomial.aeval_map_algebraMap K, hP]`. Conclude with `hCH`. Set `I : Ideal B` to `RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B))`. Establish `hI : I.comap (algebraMap A B) ≤ p`.

Introduce `a ha`. Take `⟨Q₀, hQ₀p, hQ₀c⟩` from `hQ₀`. Establish `ha' : (1 : K) ⊗ₜ[A] (algebraMap A B a) = 0` using `ha`. Use `(IsLocalizedModule.eq_zero_iff (nonZeroDivisors A) (TensorProduct.mk A K B 1)).1 ha'` as an intermediate fact. Take `⟨⟨s, hs⟩, hs0⟩` from `this`.

Establish `hs0' : φ (s * a) = 0`. Rewrite using `[map_mul]`. Simplify `hs0` using `[Algebra.smul_def, RingHom.algebraMap_toAlgebra]`. Establish `hmem : s * a ∈ Q₀.comap φ` using `by simp [Ideal.mem_comap, hs0']`. Rewrite `hmem` using `[hQ₀c, Ideal.mem_bot]`.

Establish `hs' : s ≠ 0` using `nonZeroDivisors.ne_zero hs`. Establish `: a = 0`. Break down `mul_eq_zero.1 hmem with h | h` into its components or cases. Conclude with `absurd h hs'`. Conclude with `h`.

Rewrite using `[this]`. Conclude with `p.zero_mem`. Use `haveI : Algebra.IsIntegral A B := inferInstance`. Take `⟨Q, hQI, hQp, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := B) p I hI`. Establish `hPQ : Polynomial.aeval b P ∈ Q` using `hQI (by simpa [I, RingHom.mem_ker] using hker)`.

Establish `hbd : b ^ P.natDegree ∈ Q`. Establish `hsum` using `hmon.as_sum`. Rewrite `hPQ` using `[hsum, map_add, map_pow, aeval_X, map_sum]`. Use `(Q.add_mem_iff_left ?_).1 hPQ` and prove the remaining obligations. Use `Q.sum_mem fun j hj => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, aeval_C, aeval_X_pow]`. Use `Q.mul_mem_right _ ?_` and prove the remaining obligations. Establish `: P.coeff j ∈ Q.comap (algebraMap A B)`. Rewrite using `[hQc]`. Conclude with `hcoeff j (Finset.mem_range.1 hj)`.

Conclude with `this`. Conclude with `hb Q hQp hQc (hQp.mem_of_pow_mem _ hbd)`.
-/
theorem exists_normCoeff_not_mem {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (hQ₀ : ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥)
    (p : Ideal A) (hp : p.IsPrime) (hb : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) :
    ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  set K := FractionRing A
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed (K := K) φ hφ b
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hdeg : (charK φ hφ K b).natDegree = P.natDegree := by
    rw [← hP]; exact natDegree_map_eq_of_injective hinj P
  have hmon : P.Monic := by
    have h1 := charK_monic φ hφ K b
    rw [← hP] at h1
    apply hinj
    rw [Monic, leadingCoeff_map_of_injective hinj] at h1
    simpa using h1
  by_contra hcon
  push_neg at hcon

  have hcoeff : ∀ j < P.natDegree, P.coeff j ∈ p := by
    intro j hj
    have hk : 1 ≤ P.natDegree - j := by omega
    have hrev : (charK φ hφ K b).reverse.coeff (P.natDegree - j) = algebraMap A K (P.coeff j) := by
      rw [coeff_reverse, hdeg, revAt_le (by omega), show P.natDegree - (P.natDegree - j) = j by omega,
        ← hP, coeff_map]
    have hex : ∃ a : A, algebraMap A K a = (charK φ hφ K b).reverse.coeff (P.natDegree - j) :=
      ⟨P.coeff j, hrev.symm⟩
    have := algebraMap_normCoeff φ hφ b _ hex
    rw [hrev] at this
    have := hinj this
    rw [← this]
    exact hcon _ hk

  set M := TensorProduct A K B
  have hCH : Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b) = 0 := by
    have h := LinearMap.aeval_self_charpoly (Algebra.lmul K M ((1 : K) ⊗ₜ[A] b))
    have h2 : Algebra.lmul K M (Polynomial.aeval ((1 : K) ⊗ₜ[A] b : M) (charK φ hφ K b)) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]; exact h
    have h3 := LinearMap.congr_fun h2 1
    simpa using h3
  have hker : Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B) (Polynomial.aeval b P) = 0 := by
    rw [← Polynomial.aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply,
      ← Polynomial.aeval_map_algebraMap K, hP]
    exact hCH

  let I : Ideal B := RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B))
  have hI : I.comap (algebraMap A B) ≤ p := by
    intro a ha
    obtain ⟨Q₀, hQ₀p, hQ₀c⟩ := hQ₀
    have ha' : (1 : K) ⊗ₜ[A] (algebraMap A B a) = 0 := ha
    have := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)
      (TensorProduct.mk A K B 1)).1 ha'
    obtain ⟨⟨s, hs⟩, hs0⟩ := this
    have hs0' : φ (s * a) = 0 := by
      rw [map_mul]; simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hs0
    have hmem : s * a ∈ Q₀.comap φ := by simp [Ideal.mem_comap, hs0']
    rw [hQ₀c, Ideal.mem_bot] at hmem
    have hs' : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have : a = 0 := by
      rcases mul_eq_zero.1 hmem with h | h
      · exact absurd h hs'
      · exact h
    rw [this]; exact p.zero_mem
  haveI : Algebra.IsIntegral A B := inferInstance
  obtain ⟨Q, hQI, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) p I hI
  have hPQ : Polynomial.aeval b P ∈ Q := hQI (by simpa [I, RingHom.mem_ker] using hker)
  have hbd : b ^ P.natDegree ∈ Q := by
    have hsum := hmon.as_sum
    rw [hsum, map_add, map_pow, aeval_X, map_sum] at hPQ
    refine (Q.add_mem_iff_left ?_).1 hPQ
    refine Q.sum_mem fun j hj => ?_
    rw [map_mul, aeval_C, aeval_X_pow]
    refine Q.mul_mem_right _ ?_
    have : P.coeff j ∈ Q.comap (algebraMap A B) := by
      rw [hQc]; exact hcoeff j (Finset.mem_range.1 hj)
    exact this
  exact hb Q hQp hQc (hQp.mem_of_pow_mem _ hbd)

end GlobalTheory.NormalDescent

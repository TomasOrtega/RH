import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
open GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra k K := φ.toAlgebra`. Use `haveI : FaithfulSMul k K := (faithfulSMul_iff_algebraMap_injective k K).2 φ.injective`. Take `⟨s, hs⟩` from `exists_isTranscendenceBasis k K`. Use `set A : Subalgebra k K := Algebra.adjoin k (Set.range ((↑) : s → K)) with hA`. Set `ε : A →ₐ[k] k` to `(MvPolynomial.aeval (fun _ : s => (0 : k))).comp hs.1.aevalEquiv.symm.toAlgHom`.

Establish `hε : ∀ c : k, ε (algebraMap k A c) = c` using `fun c => ε.commutes c`. Set `D : Subring K` to `A.toSubring`. Set `εD : D →+* k` to `(ε : A →+* k)`. Establish `hεs : Function.Surjective εD` using `fun c => ⟨algebraMap k A c, hε c⟩`. Use `⟨D, RingHom.ker εD, ?_, RingHom.ker_isMaximal_of_surjective εD hεs, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `A.algebraMap_mem c`. Introduce `r`. Use `⟨εD r, A.algebraMap_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, map_sub]`.

Establish `: εD ⟨φ (εD r), A.algebraMap_mem _⟩ = εD r` using `hε (εD r)`. Rewrite using `[this, sub_self]`. Introduce `x haveI : Algebra.IsAlgebraic A K := hs.isAlgebraic haveI : Algebra.IsAlgebraic D K := ‹Algebra.IsAlgebraic A K›`. Take `⟨y, hy, hint⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := D) x).exists_integral_multiple`. Conclude with `⟨y, hy, by rwa [Algebra.smul_def] at hint⟩`.
-/
theorem exists_polySubring_maximal_integral (k K : Type) [Field k] [Field K] (φ : k →+* K) :
    ∃ (D : Subring K) (m₀ : Ideal D), φ.range ≤ D ∧ m₀.IsMaximal ∧
    (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) ∧
      ∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x) := by
  letI : Algebra k K := φ.toAlgebra
  haveI : FaithfulSMul k K := (faithfulSMul_iff_algebraMap_injective k K).2 φ.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  set A : Subalgebra k K := Algebra.adjoin k (Set.range ((↑) : s → K)) with hA
  let ε : A →ₐ[k] k := (MvPolynomial.aeval (fun _ : s => (0 : k))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hε : ∀ c : k, ε (algebraMap k A c) = c := fun c => ε.commutes c
  let D : Subring K := A.toSubring
  let εD : D →+* k := (ε : A →+* k)
  have hεs : Function.Surjective εD := fun c => ⟨algebraMap k A c, hε c⟩
  refine ⟨D, RingHom.ker εD, ?_, RingHom.ker_isMaximal_of_surjective εD hεs, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact A.algebraMap_mem c
  · intro r
    refine ⟨εD r, A.algebraMap_mem _, ?_⟩
    rw [RingHom.mem_ker, map_sub]
    have : εD ⟨φ (εD r), A.algebraMap_mem _⟩ = εD r := hε (εD r)
    rw [this, sub_self]
  · intro x
    haveI : Algebra.IsAlgebraic A K := hs.isAlgebraic
    haveI : Algebra.IsAlgebraic D K := ‹Algebra.IsAlgebraic A K›
    obtain ⟨y, hy, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := D) x).exists_integral_multiple
    exact ⟨y, hy, by rwa [Algebra.smul_def] at hint⟩

end GlobalTheory

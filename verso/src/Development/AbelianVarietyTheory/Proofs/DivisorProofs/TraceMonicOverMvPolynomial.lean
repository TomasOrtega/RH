import Mathlib
open MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Use `set φ : MvPolynomial ι ℤ →+* K := (aeval z).toRingHom with hφdef`. Use `set S : Subring K := Subring.closure (Set.range z) with hSdef`. Establish `hφF : ∀ p, φ p ∈ F`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`.

Consider the case `C a => simpa [hφdef] using F.intCast_mem a`. Consider the case `add p q hp hq => simpa [map_add] using F.add_mem hp hq`. Consider the case `mul_X p i hp => simpa [map_mul, hφdef] using F.mul_mem hp (hz i)`. Establish `hφS : ∀ p, φ p ∈ S`. Introduce `p`.

Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simpa [hφdef] using S.intCast_mem a`. Consider the case `add p q hp hq => simpa [map_add] using S.add_mem hp hq`. Consider the case `mul_X p i hp`. Simplify `S.mul_mem hp (Subring.subset_closure ⟨i, rfl⟩)` using `[map_mul, hφdef]`.

Set `ψ : MvPolynomial ι ℤ →+* F` to `φ.codRestrict F hφF`. Set `θ : MvPolynomial ι ℤ →+* S` to `φ.codRestrict S hφS`. Use `letI : Algebra (MvPolynomial ι ℤ) K := φ.toAlgebra`. Use `letI : Algebra (MvPolynomial ι ℤ) F := ψ.toAlgebra`. Use `letI : Algebra (MvPolynomial ι ℤ) S := θ.toAlgebra`.

Use `haveI : IsScalarTower (MvPolynomial ι ℤ) F K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : IsScalarTower (MvPolynomial ι ℤ) S K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hθsurj : Function.Surjective θ`. Introduce and unpack `⟨s, hs⟩`. Establish `hle : S ≤ φ.range`.

Rewrite using `[hSdef, Subring.closure_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨X i, by simp [hφdef]⟩`. Take `⟨p, hp⟩` from `hle hs`. Conclude with `⟨p, Subtype.ext hp⟩`.

Use `haveI : Algebra.IsIntegral (MvPolynomial ι ℤ) S := Algebra.IsIntegral.of_surjective (Algebra.ofId _ _) hθsurj`. Establish `hvP : IsIntegral (MvPolynomial ι ℤ) v` using `isIntegral_trans v hv`. Establish `hT : IsIntegral (MvPolynomial ι ℤ) (Algebra.trace F K v)` using `Algebra.isIntegral_trace hvP`. Take `⟨f, hfm, hf⟩` from `hT`. Use `⟨f, hfm, ?_⟩` and prove the remaining obligations.

Establish `h` using `congrArg F.subtype hf`. Rewrite `h` using `[Polynomial.hom_eval₂, map_zero]`. Conclude with `h`.
-/
theorem trace_monic_over_mvPolynomial {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K]
    {ι : Type} (z : ι → K) (hz : ∀ i, z i ∈ F) (v : K)
    (hv : IsIntegral (Subring.closure (Set.range z)) v) :
    ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧
      f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by
  set φ : MvPolynomial ι ℤ →+* K := (aeval z).toRingHom with hφdef
  set S : Subring K := Subring.closure (Set.range z) with hSdef
  have hφF : ∀ p, φ p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa [hφdef] using F.intCast_mem a
    | add p q hp hq => simpa [map_add] using F.add_mem hp hq
    | mul_X p i hp => simpa [map_mul, hφdef] using F.mul_mem hp (hz i)
  have hφS : ∀ p, φ p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa [hφdef] using S.intCast_mem a
    | add p q hp hq => simpa [map_add] using S.add_mem hp hq
    | mul_X p i hp =>
        simpa [map_mul, hφdef] using S.mul_mem hp (Subring.subset_closure ⟨i, rfl⟩)
  let ψ : MvPolynomial ι ℤ →+* F := φ.codRestrict F hφF
  let θ : MvPolynomial ι ℤ →+* S := φ.codRestrict S hφS
  letI : Algebra (MvPolynomial ι ℤ) K := φ.toAlgebra
  letI : Algebra (MvPolynomial ι ℤ) F := ψ.toAlgebra
  letI : Algebra (MvPolynomial ι ℤ) S := θ.toAlgebra
  haveI : IsScalarTower (MvPolynomial ι ℤ) F K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (MvPolynomial ι ℤ) S K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hθsurj : Function.Surjective θ := by
    rintro ⟨s, hs⟩
    have hle : S ≤ φ.range := by
      rw [hSdef, Subring.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨X i, by simp [hφdef]⟩
    obtain ⟨p, hp⟩ := hle hs
    exact ⟨p, Subtype.ext hp⟩
  haveI : Algebra.IsIntegral (MvPolynomial ι ℤ) S :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId _ _) hθsurj
  have hvP : IsIntegral (MvPolynomial ι ℤ) v := isIntegral_trans v hv
  have hT : IsIntegral (MvPolynomial ι ℤ) (Algebra.trace F K v) := Algebra.isIntegral_trace hvP
  obtain ⟨f, hfm, hf⟩ := hT
  refine ⟨f, hfm, ?_⟩
  have h := congrArg F.subtype hf
  rw [Polynomial.hom_eval₂, map_zero] at h
  exact h

end GlobalTheory

import Mathlib

open Polynomial

namespace GlobalTheory.IsIntegralDetLattice

/- English proof (translation)
Take `⟨p, hp, hpA⟩` from `hA`. Establish `hmem : x ∈ spectrum K A` using `Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hx`. Establish `h2` using `spectrum.subset_polynomial_aeval A (p.map (algebraMap R K)) ⟨x, hmem, rfl⟩`. Rewrite `h2` using `[aeval_map_algebraMap, aeval_def, hpA, spectrum.mem_iff, sub_zero]`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations.

Rewrite using `[eval₂_eq_eval_map]`. Assume the negation of the conclusion as `hne`. Conclude with `h2 ((Ne.isUnit hne).map (algebraMap K (Matrix (Fin N) (Fin N) K)))`.
-/
theorem isIntegral_of_isRoot_charpoly {R K : Type} [CommRing R] [Field K] [Algebra R K] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) (hA : IsIntegral R A) (x : K) (hx : A.charpoly.IsRoot x) :
    IsIntegral R x := by
  obtain ⟨p, hp, hpA⟩ := hA

  have hmem : x ∈ spectrum K A := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hx
  have h2 := spectrum.subset_polynomial_aeval A (p.map (algebraMap R K)) ⟨x, hmem, rfl⟩
  rw [aeval_map_algebraMap, aeval_def, hpA, spectrum.mem_iff, sub_zero] at h2
  refine ⟨p, hp, ?_⟩
  rw [eval₂_eq_eval_map]
  by_contra hne
  exact h2 ((Ne.isUnit hne).map (algebraMap K (Matrix (Fin N) (Fin N) K)))

/- English proof (translation)
Set `φ : E →ₐ[R] AlgebraicClosure E` to `IsScalarTower.toAlgHom R E (AlgebraicClosure E)`. Establish `hA' : IsIntegral R (A.map (algebraMap E (AlgebraicClosure E)))`. Conclude with `hA.map (φ.mapMatrix (m := Fin N))`. Establish `hdet : (A.map (algebraMap E (AlgebraicClosure E))).det = algebraMap E (AlgebraicClosure E) A.det`. Rewrite using `[RingHom.map_det]`.

Both sides reduce to the same expression. Rewrite using `[← isIntegral_algHom_iff φ (algebraMap E (AlgebraicClosure E)).injective]`. Use `show IsIntegral R (algebraMap E (AlgebraicClosure E) A.det)`. Rewrite using `[← hdet, Matrix.det_eq_prod_roots_charpoly]`. Conclude with `multiset_prod_mem (S := integralClosure R (AlgebraicClosure E)) _ fun r hr => isIntegral_of_isRoot_charpoly _ hA' r (Polynomial.isRoot_of_mem_roots hr)`.
-/
theorem isIntegral_det {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) E) (hA : IsIntegral R A) : IsIntegral R A.det := by

  let φ : E →ₐ[R] AlgebraicClosure E := IsScalarTower.toAlgHom R E (AlgebraicClosure E)
  have hA' : IsIntegral R (A.map (algebraMap E (AlgebraicClosure E))) := by
    exact hA.map (φ.mapMatrix (m := Fin N))
  have hdet : (A.map (algebraMap E (AlgebraicClosure E))).det = algebraMap E (AlgebraicClosure E) A.det := by
    rw [RingHom.map_det]; rfl
  rw [← isIntegral_algHom_iff φ (algebraMap E (AlgebraicClosure E)).injective]
  show IsIntegral R (algebraMap E (AlgebraicClosure E) A.det)
  rw [← hdet, Matrix.det_eq_prod_roots_charpoly]
  exact multiset_prod_mem (S := integralClosure R (AlgebraicClosure E)) _
    fun r hr => isIntegral_of_isRoot_charpoly _ hA' r (Polynomial.isRoot_of_mem_roots hr)

/- English proof (translation)
Establish `: Module.Finite R L` using `Module.Finite.iff_fg.mpr hL`. Set `f : Module.End R L` to `((Matrix.mulVecLin γ).restrictScalars R).restrict hγ`. Take `⟨p, hp, hpf⟩` from `LinearMap.exists_monic_and_aeval_eq_zero R f`. Establish `hpow : ∀ (n : ℕ) (v : Fin N → E) (hv : v ∈ L), (γ ^ n).mulVec v = ((f ^ n) ⟨v, hv⟩ : Fin N → E)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro v hv`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `v hv`.

Rewrite using `[pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih v hv, Module.End.mul_apply]`. Both sides reduce to the same expression. Establish `key : ∀ (q : R[X]) (v : Fin N → E) (hv : v ∈ L), (aeval γ q).mulVec v = ((aeval f q) ⟨v, hv⟩ : Fin N → E)`. Introduce `q`. Proceed by induction on `q using Polynomial.induction_on' with`.

Consider the case `add p q hp hq => intro v hv`. Simplify using `[Matrix.add_mulVec, hp v hv, hq v hv]`. Consider the case `monomial n a`. Introduce `v hv`. Simplify using `[aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, hpow n v hv]`.

Establish `hz : Matrix.toLin' (aeval γ p) = 0`. Use `LinearMap.ext_on hs fun v hv => ?_` and prove the remaining obligations. Simplify using `[Matrix.toLin'_apply, key p v hv, hpf]`. Conclude with `⟨p, hp, by rw [← aeval_def]; exact Matrix.toLin'.map_eq_zero_iff.mp hz⟩`.
-/
theorem isIntegral_of_preserves {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (L : Submodule R (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral R γ := by
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hL

  let f : Module.End R L := ((Matrix.mulVecLin γ).restrictScalars R).restrict hγ
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  have hpow : ∀ (n : ℕ) (v : Fin N → E) (hv : v ∈ L),
      (γ ^ n).mulVec v = ((f ^ n) ⟨v, hv⟩ : Fin N → E) := by
    intro n
    induction n with
    | zero => intro v hv; simp
    | succ n ih =>
      intro v hv
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih v hv, Module.End.mul_apply]
      rfl
  have key : ∀ (q : R[X]) (v : Fin N → E) (hv : v ∈ L),
      (aeval γ q).mulVec v = ((aeval f q) ⟨v, hv⟩ : Fin N → E) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v hv; simp [Matrix.add_mulVec, hp v hv, hq v hv]
    | monomial n a =>
      intro v hv
      simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, hpow n v hv]
  have hz : Matrix.toLin' (aeval γ p) = 0 := by
    refine LinearMap.ext_on hs fun v hv => ?_
    simp [Matrix.toLin'_apply, key p v hv, hpf]
  exact ⟨p, hp, by rw [← aeval_def]; exact Matrix.toLin'.map_eq_zero_iff.mp hz⟩

/- English proof (translation)
Conclude with `isIntegral_trans _ (isIntegral_det γ (isIntegral_of_preserves L hL hs γ hγ))`.
-/
theorem isIntegral_det_of_preserves_lattice {E : Type} [Field E] [NumberField E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det := by
  exact isIntegral_trans _ (isIntegral_det γ (isIntegral_of_preserves L hL hs γ hγ))

end GlobalTheory.IsIntegralDetLattice

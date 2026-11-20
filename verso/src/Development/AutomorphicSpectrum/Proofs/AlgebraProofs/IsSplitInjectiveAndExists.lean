import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample

open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Crv

/- English proof (translation)
Unfold `IsSplit at h`. Use `set F := Algebra.TensorProduct.lift (Algebra.ofId k (S → k)) (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom) (fun _ _ => Commute.all _ _) with hF`. Establish `hv : ∀ (a : k) (x : O) (s : S), F (a ⊗ₜ[ℤ] x) s = a * χ s x`. Introduce `a x s`. Simplify using `[hF, Algebra.ofId_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce `s t hst`. Assume the negation of the conclusion as `hne`. Take `⟨y, hy⟩` from `h.2 (Pi.single s 1)`. Establish `key : ∀ y : TensorProduct ℤ k O, F y s = F y t`.

Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rw [hv, hv, hst]`. Consider the case `add u v hu hv' => simp [map_add, hu, hv']`.

Establish `h1` using `key y`. Rewrite `h1` using `[hy]`. Simplify using `[Pi.single_apply, Ne.symm hne] at h1`. Introduce `ψ`. Set `Ψ : TensorProduct ℤ k O →ₐ[k] k` to `Algebra.TensorProduct.lift (AlgHom.id k k) ψ.toIntAlgHom (fun _ _ => Commute.all _ _)`.

Use `choose y hy using fun s => h.2 (Pi.single s (1 : k))`. Establish `hsum : ∑ s, y s = 1`. Apply `h.1` to reduce the goal to its premises. Rewrite using `[map_sum, map_one]`. Simplify using `only [hy]`.

Use extensionality with `t`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hne : ∑ s, Ψ (y s) ≠ 0`. Rewrite using `[← map_sum, hsum, map_one]`. Conclude with `one_ne_zero`.

Take `⟨s, -, hs⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `hmul : ∀ z, z * y s = (F z s) • y s`. Introduce `z`. Apply `h.1` to reduce the goal to its premises.

Rewrite using `[map_mul, map_smul, hy]`. Use extensionality with `t`. Distinguish the cases in `hts : t = s`. Substitute `hts` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, hts]`. Use extensionality with `o`. Establish `h1` using `congrArg Ψ (hmul ((1 : k) ⊗ₜ[ℤ] o))`. Establish `h2 : Ψ ((1 : k) ⊗ₜ[ℤ] o) = ψ o`. Simplify using `[Ψ]`.

Rewrite `h1` using `[map_mul, map_smul, hv, h2, smul_eq_mul, one_mul]`. Conclude with `(mul_right_cancel₀ hs h1).symm`.
-/
theorem isSplit_injective_and_exists (O k S : Type) [CommRing O] [Field k] [Fintype S]
    (χ : S → (O →+* k)) (h : IsSplit χ) :
    Function.Injective χ ∧ ∀ ψ : O →+* k, ∃ s, χ s = ψ := by
  classical
  unfold IsSplit at h
  set F := Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom)
    (fun _ _ => Commute.all _ _) with hF
  have hv : ∀ (a : k) (x : O) (s : S), F (a ⊗ₜ[ℤ] x) s = a * χ s x := by
    intro a x s
    simp [hF, Algebra.ofId_apply]
  constructor
  · intro s t hst
    by_contra hne
    obtain ⟨y, hy⟩ := h.2 (Pi.single s 1)
    have key : ∀ y : TensorProduct ℤ k O, F y s = F y t := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rw [hv, hv, hst]
      | add u v hu hv' => simp [map_add, hu, hv']
    have h1 := key y
    rw [hy] at h1
    simp [Pi.single_apply, Ne.symm hne] at h1
  · intro ψ
    let Ψ : TensorProduct ℤ k O →ₐ[k] k :=
      Algebra.TensorProduct.lift (AlgHom.id k k) ψ.toIntAlgHom (fun _ _ => Commute.all _ _)
    choose y hy using fun s => h.2 (Pi.single s (1 : k))
    have hsum : ∑ s, y s = 1 := by
      apply h.1
      rw [map_sum, map_one]
      simp only [hy]
      ext t
      simp [Finset.sum_apply, Pi.single_apply]
    have hne : ∑ s, Ψ (y s) ≠ 0 := by
      rw [← map_sum, hsum, map_one]
      exact one_ne_zero
    obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine ⟨s, ?_⟩
    have hmul : ∀ z, z * y s = (F z s) • y s := by
      intro z
      apply h.1
      rw [map_mul, map_smul, hy]
      ext t
      by_cases hts : t = s
      · subst hts
        simp
      · simp [Pi.single_apply, hts]
    ext o
    have h1 := congrArg Ψ (hmul ((1 : k) ⊗ₜ[ℤ] o))
    have h2 : Ψ ((1 : k) ⊗ₜ[ℤ] o) = ψ o := by
      simp [Ψ]
    rw [map_mul, map_smul, hv, h2, smul_eq_mul, one_mul] at h1
    exact (mul_right_cancel₀ hs h1).symm

end GlobalTheory.CompanionTheory.Ar.Crv
